use std::fmt;
use std::str::FromStr;

use gentoo_interner::{DefaultInterner, Interned};
use winnow::combinator::{alt, cut_err, opt, preceded};
use winnow::error::StrContext;
use winnow::prelude::*;

use crate::cpn::{Cpn, parse_cpn};
use crate::cpv::{Cpv, parse_cpv};
use crate::error::{Error, Result};
use crate::parsers::has_version_suffix;
use crate::slot::{SlotDep, parse_slot_dep};
use crate::use_dep::{UseDep, parse_use_deps};
use crate::version::Version;

/// Package dependency blocker type
///
/// Blockers prevent conflicting packages from being installed simultaneously.
/// See [PMS 8.3.2](https://projects.gentoo.org/pms/9/pms.html#block-operator).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Blocker {
    /// `!` — weak blocker: the blocked package may be temporarily installed
    /// during a transition, but must be uninstalled before the operation completes.
    Weak,
    /// `!!` — strong blocker: the blocked package must never be installed
    /// at the same time as this package.
    Strong,
}

impl fmt::Display for Blocker {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Blocker::Weak => write!(f, "!"),
            Blocker::Strong => write!(f, "!!"),
        }
    }
}

/// Full dependency atom
///
/// Represents a complete dependency atom as it appears in ebuild `*DEPEND`
/// variables, e.g. `>=dev-lang/rust-1.75.0:0[ssl]::gentoo`.
///
/// The general form is `[!|!!][op]category/package[-ver][:slot][use][::repo]`.
///
/// See [PMS 8.3](https://projects.gentoo.org/pms/9/pms.html#package-dependency-specifications)
/// for the full specification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "builder", derive(bon::Builder))]
pub struct Dep {
    /// The unversioned category/package name (e.g. `dev-lang/rust`).
    ///
    /// See [`Cpn`] and [PMS 3.1].
    ///
    /// [PMS 3.1]: https://projects.gentoo.org/pms/9/pms.html#restrictions-upon-names
    #[cfg_attr(feature = "builder", builder(start_fn))]
    pub cpn: Cpn,
    /// Optional blocker prefix.
    ///
    /// `!` is a weak blocker; `!!` is a strong blocker.
    /// See [PMS 8.3.2].
    ///
    /// [PMS 8.3.2]: https://projects.gentoo.org/pms/9/pms.html#block-operator
    pub blocker: Option<Blocker>,
    /// Optional version constraint with its comparison operator.
    ///
    /// The [`Version::op`] field holds the operator (`>=`, `=`, `~`, etc.).
    /// See [PMS 8.3.1].
    ///
    /// [PMS 8.3.1]: https://projects.gentoo.org/pms/9/pms.html#operators
    pub version: Option<Version>,
    /// Optional slot dependency (the portion after `:`).
    ///
    /// See [PMS 8.3.3].
    ///
    /// [PMS 8.3.3]: https://projects.gentoo.org/pms/9/pms.html#slot-dependencies
    pub slot_dep: Option<SlotDep>,
    /// Optional USE flag constraints (the bracketed portion).
    ///
    /// See [PMS 8.3.4].
    ///
    /// [PMS 8.3.4]: https://projects.gentoo.org/pms/9/pms.html#style-and-style-use-dependencies
    pub use_deps: Option<Vec<UseDep>>,
    /// Optional repository name (after `::`, e.g. `gentoo`).
    ///
    /// See [PMS 8.3.5].
    ///
    /// [PMS 8.3.5]: https://projects.gentoo.org/pms/9/pms.html#repository-dependencies
    #[cfg_attr(feature = "builder", builder(into))]
    pub repo: Option<Interned<DefaultInterner>>,
}

impl Dep {
    /// Create a minimal dependency from a [`Cpn`].
    ///
    /// All optional fields default to `None`.
    pub fn new(cpn: Cpn) -> Self {
        Dep {
            cpn,
            blocker: None,
            version: None,
            slot_dep: None,
            use_deps: None,
            repo: None,
        }
    }

    /// Parse a full dependency atom string.
    ///
    /// Returns an error if the string does not conform to the PMS format.
    pub fn parse(input: &str) -> Result<Self> {
        parse_dep
            .parse(input)
            .map_err(|e| Error::InvalidDep(format!("{}: {}", input, e)))
    }

    /// Try to create from a string.
    ///
    /// Alias for [`Dep::parse`].
    pub fn try_new(s: &str) -> Result<Self> {
        Self::parse(s)
    }

    /// The category portion of the atom (e.g. `dev-lang`).
    pub fn category(&self) -> &str {
        &self.cpn.category
    }

    /// The package name portion of the atom (e.g. `rust`).
    pub fn package(&self) -> &str {
        &self.cpn.package
    }

    /// Build a [`Cpv`] from this dependency, if it carries a version.
    pub fn cpv(&self) -> Option<Cpv> {
        self.version.as_ref().map(|v| Cpv::new(self.cpn, v.clone()))
    }
}

impl fmt::Display for Dep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(blocker) = &self.blocker {
            write!(f, "{}", blocker)?;
        }

        if let Some(version) = &self.version {
            if let Some(op) = version.op {
                write!(f, "{}", op)?;
            }
        }

        write!(f, "{}", self.cpn)?;

        if let Some(version) = &self.version {
            write!(f, "-")?;
            for (i, num) in version.numbers.iter().enumerate() {
                if i > 0 {
                    write!(f, ".")?;
                }
                write!(f, "{num}")?;
            }
            if let Some(letter) = version.letter {
                write!(f, "{letter}")?;
            }
            for suffix in &version.suffixes {
                write!(f, "{suffix}")?;
            }
            write!(f, "{}", version.revision)?;
            if version.glob {
                write!(f, "*")?;
            }
        }

        if let Some(slot) = &self.slot_dep {
            write!(f, ":{}", slot)?;
        }

        if let Some(use_deps) = &self.use_deps {
            if !use_deps.is_empty() {
                write!(f, "[")?;
                for (i, dep) in use_deps.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{}", dep)?;
                }
                write!(f, "]")?;
            }
        }

        if let Some(repo) = &self.repo {
            write!(f, "::{}", repo)?;
        }

        Ok(())
    }
}

impl FromStr for Dep {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

// Winnow parsers

fn parse_cpn_or_cpv(input: &mut &str) -> ModalResult<(Cpn, Option<crate::version::Version>)> {
    if has_version_suffix(input) {
        match parse_cpv.parse_next(input) {
            Ok(cpv) => return Ok((cpv.cpn, Some(cpv.version))),
            Err(winnow::error::ErrMode::Backtrack(_)) => {}
            Err(e) => return Err(e),
        }
    }
    parse_cpn.parse_next(input).map(|cpn| (cpn, None))
}

/// Parse blocker prefix
fn parse_blocker(input: &mut &str) -> ModalResult<Blocker> {
    alt(("!!".value(Blocker::Strong), "!".value(Blocker::Weak))).parse_next(input)
}

/// Parse repository name (alphanumeric, _, -, +)
fn parse_repo(input: &mut &str) -> ModalResult<Interned<DefaultInterner>> {
    use crate::parsers::parse_ident_base;

    parse_ident_base
        .map(|s: &str| Interned::intern(s))
        .parse_next(input)
}

/// Parse full dependency atom
/// Handles: [!|!!][op]cat/pkg[-ver][:slot][use][::repo]
pub(crate) fn parse_dep(input: &mut &str) -> ModalResult<Dep> {
    use crate::version::parse_operator;
    use winnow::combinator::fail;

    // Parse optional blocker
    let blocker = opt(parse_blocker).parse_next(input)?;

    // Parse optional operator (just the operator, not the version)
    let operator = opt(parse_operator).parse_next(input)?;

    // Try to parse as CPV first (contains version), fall back to CPN
    let (cpn, mut version) = if operator.is_some() {
        let cpv = cut_err(parse_cpv)
            .context(StrContext::Label("versioned atom"))
            .parse_next(input)?;
        (cpv.cpn, Some(cpv.version))
    } else {
        parse_cpn_or_cpv.parse_next(input)?
    };

    // Apply operator if we have one
    if let Some(op) = operator {
        match &mut version {
            Some(v) => v.op = Some(op),
            None => return fail.parse_next(input), // Operator requires version
        }
    }

    // Parse optional slot dependency
    let slot_dep = opt(preceded(':', parse_slot_dep)).parse_next(input)?;

    // Parse optional USE dependencies
    let use_deps = opt(parse_use_deps).parse_next(input)?;

    // Parse optional repository
    let repo = opt(preceded("::", parse_repo)).parse_next(input)?;

    Ok(Dep {
        cpn,
        blocker,
        version,
        slot_dep,
        use_deps,
        repo,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slot::SlotOperator;
    use crate::version::{Operator, SuffixKind};

    #[test]
    fn test_dep_simple() {
        let dep = Dep::parse("dev-lang/rust").unwrap();
        assert_eq!(dep.category(), "dev-lang");
        assert_eq!(dep.package(), "rust");
        assert!(dep.version.is_none());
        assert!(dep.blocker.is_none());
        assert_eq!(dep.to_string(), "dev-lang/rust");
    }

    #[test]
    fn test_dep_versioned() {
        let dep = Dep::parse(">=dev-lang/rust-1.75.0").unwrap();
        assert!(dep.version.is_some());
        let version = dep.version.as_ref().unwrap();
        assert_eq!(version.numbers[0], 1);
        assert_eq!(version.numbers[1], 75);
        assert_eq!(dep.to_string(), ">=dev-lang/rust-1.75.0");
    }

    #[test]
    fn test_dep_with_slot() {
        let dep = Dep::parse("dev-lang/rust:0").unwrap();
        assert!(dep.slot_dep.is_some());
        assert_eq!(dep.to_string(), "dev-lang/rust:0");
    }

    #[test]
    fn test_dep_with_use_deps() {
        let dep = Dep::parse("dev-lang/rust[llvm_targets_AMDGPU]").unwrap();
        assert!(dep.use_deps.is_some());
        let use_deps = dep.use_deps.as_ref().unwrap();
        assert_eq!(use_deps.len(), 1);
        assert_eq!(dep.to_string(), "dev-lang/rust[llvm_targets_AMDGPU]");
    }

    #[test]
    fn test_dep_with_blocker() {
        let dep = Dep::parse("!dev-lang/rust").unwrap();
        assert_eq!(dep.blocker, Some(Blocker::Weak));
        assert_eq!(dep.to_string(), "!dev-lang/rust");

        let dep = Dep::parse("!!dev-lang/rust").unwrap();
        assert_eq!(dep.blocker, Some(Blocker::Strong));
        assert_eq!(dep.to_string(), "!!dev-lang/rust");
    }

    #[test]
    fn test_dep_with_repo() {
        let dep = Dep::parse("dev-lang/rust::gentoo").unwrap();
        assert_eq!(dep.repo, Some(Interned::intern("gentoo")));
        assert_eq!(dep.to_string(), "dev-lang/rust::gentoo");
    }

    #[test]
    fn test_dep_complex() {
        let dep = Dep::parse(">=dev-lang/rust-1.75.0:0/1.75[llvm_targets_AMDGPU,-debug]::gentoo")
            .unwrap();
        assert!(dep.version.is_some());
        assert!(dep.slot_dep.is_some());
        assert!(dep.use_deps.is_some());
        assert_eq!(dep.repo, Some(Interned::intern("gentoo")));
    }

    #[test]
    fn test_dep_with_all_features() {
        // Test a complex dependency using all PMS features
        let dep_str = "!!>=dev-lang/rust-1.75.0_rc1:0/1.75=[ssl(-),-debug,python?]::gentoo";
        let dep = Dep::parse(dep_str).unwrap();

        assert_eq!(dep.blocker, Some(Blocker::Strong));
        assert!(dep.version.is_some());
        let version = dep.version.as_ref().unwrap();
        assert_eq!(version.op, Some(Operator::GreaterOrEqual));
        assert_eq!(version.numbers[0], 1);
        assert_eq!(version.suffixes[0].kind, SuffixKind::Rc);

        assert!(dep.slot_dep.is_some());
        let slot_dep = dep.slot_dep.as_ref().unwrap();
        match slot_dep {
            SlotDep::Slot {
                slot: Some(s),
                op: Some(o),
            } => {
                assert_eq!(s.slot, "0");
                assert_eq!(s.subslot, Some(Interned::intern("1.75")));
                assert_eq!(*o, SlotOperator::Equal);
            }
            _ => panic!("Unexpected slot dep format"),
        }

        assert!(dep.use_deps.is_some());
        let use_deps = dep.use_deps.as_ref().unwrap();
        assert_eq!(use_deps.len(), 3);

        assert_eq!(dep.repo, Some(Interned::intern("gentoo")));
    }

    #[test]
    #[cfg(feature = "builder")]
    fn test_dep_builder_simple() {
        let cpn = Cpn::new("dev-lang", "rust");
        let dep = Dep::builder(cpn).build();
        assert_eq!(dep.category(), "dev-lang");
        assert_eq!(dep.package(), "rust");
        assert!(dep.version.is_none());
        assert!(dep.blocker.is_none());
        assert_eq!(dep.to_string(), "dev-lang/rust");
    }

    #[test]
    #[cfg(feature = "builder")]
    fn test_dep_builder_versioned() {
        let cpn = Cpn::new("dev-lang", "rust");
        let mut version = Version::new(&[1, 75, 0]);
        version.op = Some(Operator::GreaterOrEqual);
        let dep = Dep::builder(cpn).version(version).build();
        assert!(dep.version.is_some());
        assert_eq!(dep.to_string(), ">=dev-lang/rust-1.75.0");
    }

    #[test]
    #[cfg(feature = "builder")]
    fn test_dep_builder_with_blocker_and_repo() {
        let cpn = Cpn::new("dev-libs", "old");
        let dep = Dep::builder(cpn)
            .blocker(Blocker::Strong)
            .repo("gentoo")
            .build();
        assert_eq!(dep.blocker, Some(Blocker::Strong));
        assert_eq!(dep.repo, Some(Interned::intern("gentoo")));
        assert_eq!(dep.to_string(), "!!dev-libs/old::gentoo");
    }

    #[test]
    #[cfg(feature = "builder")]
    fn test_dep_builder_roundtrip() {
        let original = Dep::parse(">=dev-lang/rust-1.75.0:0[ssl,-debug]::gentoo").unwrap();

        let mut version = original.version.clone().unwrap();
        version.op = Some(Operator::GreaterOrEqual);
        let built = Dep::builder(original.cpn)
            .version(version)
            .slot_dep(original.slot_dep.clone().unwrap())
            .use_deps(original.use_deps.clone().unwrap())
            .repo("gentoo")
            .build();

        assert_eq!(original.to_string(), built.to_string());
    }

    // --- PMS 8.3.1 operator tests ---

    #[test]
    fn test_all_operators() {
        let cases = [
            ("<dev-libs/a-1.0", Operator::Less),
            ("<=dev-libs/a-1.0", Operator::LessOrEqual),
            ("=dev-libs/a-1.0", Operator::Equal),
            ("~dev-libs/a-1.0", Operator::Approximate),
            (">=dev-libs/a-1.0", Operator::GreaterOrEqual),
            (">dev-libs/a-1.0", Operator::Greater),
        ];
        for (input, expected_op) in cases {
            let dep = Dep::parse(input).unwrap();
            let v = dep.version.as_ref().unwrap();
            assert_eq!(v.op, Some(expected_op), "operator mismatch for: {input}");
            assert_eq!(dep.to_string(), input, "round-trip failed for: {input}");
        }
    }

    #[test]
    fn test_approximate_operator() {
        // PMS 8.3.1: ~ ignores revision
        let dep = Dep::parse("~dev-lang/rust-1.75.0").unwrap();
        let v = dep.version.as_ref().unwrap();
        assert_eq!(v.op, Some(Operator::Approximate));
        assert_eq!(v.numbers, vec![1, 75, 0]);
    }

    #[test]
    fn test_glob_with_equal() {
        // PMS 8.3.1: glob (*) only valid with = operator
        assert!(Dep::parse("=dev-libs/a-1*").is_ok());
        // TODO: PMS says "An asterisk used with any other operator is illegal"
        // but we currently don't validate this at parse time.
    }

    #[test]
    fn test_dep_display_round_trip() {
        let inputs = [
            "dev-lang/rust",
            "!dev-libs/old",
            "!!dev-libs/old",
            ">=dev-lang/rust-1.75.0",
            "=dev-libs/a-11*",
            "dev-lang/rust:0",
            "dev-lang/rust:0/1.75",
            "dev-lang/rust[ssl]",
            "dev-lang/rust::gentoo",
            ">=dev-lang/rust-1.75.0:0[ssl]::gentoo",
        ];
        for input in inputs {
            let dep = Dep::parse(input).unwrap();
            assert_eq!(dep.to_string(), input, "round-trip failed for: {input}");
        }
    }
}
