use std::fmt;
use std::str::FromStr;

use winnow::combinator::{alt, cut_err, opt, preceded};
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::take_while;

use crate::cpn::{parse_cpn, Cpn};
use crate::cpv::{parse_cpv, Cpv};
use crate::error::{Error, Result};
use crate::slot::{parse_slot_dep, SlotDep};
use crate::use_dep::{parse_use_deps, UseDep};
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
/// Represents full dependency atoms like `>=dev-lang/rust-1.75.0:0[ssl]::gentoo`.
///
/// See [PMS 8.3](https://projects.gentoo.org/pms/9/pms.html#package-dependency-specifications)
/// for the dependency specification syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dep {
    /// Unversioned category/package name (e.g. `dev-lang/rust`).
    pub cpn: Cpn,
    /// Optional blocker prefix (`!` or `!!`).
    pub blocker: Option<Blocker>,
    /// Optional version constraint with operator (e.g. `>=1.75.0-r1`).
    pub version: Option<Version>,
    /// Optional slot dependency (e.g. `:0/1.2=`).
    pub slot_dep: Option<SlotDep>,
    /// Optional USE flag constraints (e.g. `[ssl,-debug]`).
    pub use_deps: Option<Vec<UseDep>>,
    /// Optional repository name (e.g. `gentoo` from `::gentoo`).
    pub repo: Option<String>,
}

impl Dep {
    /// Create new dependency from cpn
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

    /// Parse from string
    pub fn parse(input: &str) -> Result<Self> {
        parse_dep()
            .parse(input)
            .map_err(|e| Error::InvalidDep(format!("{}: {}", input, e)))
    }

    /// Try to create from string (alias for parse)
    pub fn try_new(s: &str) -> Result<Self> {
        Self::parse(s)
    }

    /// Get the category
    pub fn category(&self) -> &str {
        &self.cpn.category
    }

    /// Get the package name
    pub fn package(&self) -> &str {
        &self.cpn.package
    }

    /// Convert to Cpv if versioned
    pub fn cpv(&self) -> Option<Cpv> {
        self.version
            .as_ref()
            .map(|v| Cpv::new(self.cpn.clone(), v.clone()))
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
            // Display version without operator (operator already shown above)
            write!(f, "-")?;
            for (i, num) in version.numbers.iter().enumerate() {
                if i > 0 {
                    write!(f, ".")?;
                }
                write!(f, "{}", num)?;
            }
            if let Some(letter) = version.letter {
                write!(f, "{}", letter)?;
            }
            for suffix in &version.suffixes {
                write!(f, "{}", suffix)?;
            }
            write!(f, "{}", version.revision)?;
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

/// Parse blocker prefix
fn parse_blocker<'s>() -> impl Parser<&'s str, Blocker, ErrMode<ContextError>> {
    alt(("!!".value(Blocker::Strong), "!".value(Blocker::Weak)))
}

/// Parse repository name (alphanumeric, _, -, +)
fn parse_repo<'s>() -> impl Parser<&'s str, String, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+'
    })
    .map(|s: &str| s.to_string())
}

/// Parse full dependency atom
/// Handles: [!|!!][op]cat/pkg[-ver][:slot][use][::repo]
pub(crate) fn parse_dep<'s>() -> impl Parser<&'s str, Dep, ErrMode<ContextError>> {
    move |input: &mut &'s str| {
        use crate::version::parse_operator;
        use winnow::combinator::fail;

        // Parse optional blocker
        let blocker = opt(parse_blocker()).parse_next(input)?;

        // Parse optional operator (just the operator, not the version)
        let operator = opt(parse_operator()).parse_next(input)?;

        // Try to parse as CPV first (contains version), fall back to CPN
        let (cpn, mut version) = if operator.is_some() {
            // Operator requires version — commit to parsing a CPV
            let cpv = cut_err(parse_cpv())
                .context(StrContext::Label("versioned atom"))
                .parse_next(input)?;
            (cpv.cpn, Some(cpv.version))
        } else {
            alt((
                parse_cpv().map(|cpv| (cpv.cpn, Some(cpv.version))),
                parse_cpn().map(|cpn| (cpn, None)),
            ))
            .parse_next(input)?
        };

        // Apply operator if we have one
        if let Some(op) = operator {
            match &mut version {
                Some(v) => v.op = Some(op),
                None => return fail.parse_next(input), // Operator requires version
            }
        }

        // Parse optional slot dependency
        let slot_dep = opt(preceded(':', parse_slot_dep())).parse_next(input)?;

        // Parse optional USE dependencies
        let use_deps = opt(parse_use_deps()).parse_next(input)?;

        // Parse optional repository
        let repo = opt(preceded("::", parse_repo())).parse_next(input)?;

        Ok(Dep {
            cpn,
            blocker,
            version,
            slot_dep,
            use_deps,
            repo,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(dep.repo, Some("gentoo".to_string()));
        assert_eq!(dep.to_string(), "dev-lang/rust::gentoo");
    }

    #[test]
    fn test_dep_complex() {
        let dep = Dep::parse(">=dev-lang/rust-1.75.0:0/1.75[llvm_targets_AMDGPU,-debug]::gentoo")
            .unwrap();
        assert!(dep.version.is_some());
        assert!(dep.slot_dep.is_some());
        assert!(dep.use_deps.is_some());
        assert_eq!(dep.repo, Some("gentoo".to_string()));
    }
}
