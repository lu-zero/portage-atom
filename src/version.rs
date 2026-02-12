use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

use winnow::ascii::digit1;
use winnow::combinator::{alt, cut_err, opt, preceded, repeat, separated};
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::one_of;

use crate::error::{Error, Result};

/// Package revision (`-r1`, `-r2`, etc.)
///
/// Tracks packaging changes independently of the upstream version.
/// A revision of `0` is the implicit default and is omitted from display.
///
/// See [PMS 3.2](https://projects.gentoo.org/pms/9/pms.html#version-specifications).
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Revision(pub u64);

impl fmt::Display for Revision {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == 0 {
            Ok(())
        } else {
            write!(f, "-r{}", self.0)
        }
    }
}

impl PartialOrd for Revision {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Revision {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

/// Version suffix kind
///
/// PMS defines five ordered suffix types that modify version comparison.
/// `Alpha`, `Beta`, `Pre`, and `Rc` sort *below* the unsuffixed version,
/// while `P` (patchlevel) sorts *above* it.
///
/// See [PMS 3.2](https://projects.gentoo.org/pms/9/pms.html#version-specifications)
/// and [Algorithm 3.1](https://projects.gentoo.org/pms/9/pms.html#version-comparison).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SuffixKind {
    /// `_alpha` — earliest pre-release stage.
    Alpha,
    /// `_beta` — feature-complete but not yet stable.
    Beta,
    /// `_pre` — pre-release snapshot.
    Pre,
    /// `_rc` — release candidate.
    Rc,
    /// `_p` — post-release patchlevel (sorts *above* the base version).
    P,
}

impl SuffixKind {
    /// Ordering value for PMS version comparison
    fn order(&self) -> i32 {
        match self {
            SuffixKind::Alpha => -4,
            SuffixKind::Beta => -3,
            SuffixKind::Pre => -2,
            SuffixKind::Rc => -1,
            SuffixKind::P => 1,
        }
    }
}

impl fmt::Display for SuffixKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SuffixKind::Alpha => write!(f, "_alpha"),
            SuffixKind::Beta => write!(f, "_beta"),
            SuffixKind::Pre => write!(f, "_pre"),
            SuffixKind::Rc => write!(f, "_rc"),
            SuffixKind::P => write!(f, "_p"),
        }
    }
}

impl FromStr for SuffixKind {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "alpha" => Ok(SuffixKind::Alpha),
            "beta" => Ok(SuffixKind::Beta),
            "pre" => Ok(SuffixKind::Pre),
            "rc" => Ok(SuffixKind::Rc),
            "p" => Ok(SuffixKind::P),
            _ => Err(Error::InvalidVersion(format!("invalid suffix kind: {}", s))),
        }
    }
}

/// A version suffix with optional numeric qualifier
///
/// Represents one `_alpha`, `_beta`, `_pre`, `_rc`, or `_p` segment,
/// optionally followed by a number (e.g. `_rc2`, `_p1`).
///
/// See [PMS 3.2](https://projects.gentoo.org/pms/9/pms.html#version-specifications).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Suffix {
    /// The suffix type (`_alpha`, `_beta`, `_pre`, `_rc`, or `_p`).
    pub kind: SuffixKind,
    /// Optional numeric qualifier (e.g. `2` in `_rc2`).
    pub version: Option<u64>,
}

impl fmt::Display for Suffix {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)?;
        if let Some(v) = self.version {
            write!(f, "{}", v)?;
        }
        Ok(())
    }
}

impl PartialOrd for Suffix {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Suffix {
    fn cmp(&self, other: &Self) -> Ordering {
        // PMS: Compare suffix kind first
        match self.kind.order().cmp(&other.kind.order()) {
            Ordering::Equal => {
                // Same kind: compare version numbers
                match (&self.version, &other.version) {
                    (Some(a), Some(b)) => a.cmp(b),
                    (Some(_), None) => Ordering::Greater,
                    (None, Some(_)) => Ordering::Less,
                    (None, None) => Ordering::Equal,
                }
            }
            other => other,
        }
    }
}

/// Version comparison operator for dependency atoms
///
/// Used as a prefix on versioned dependencies to constrain which versions
/// satisfy the dependency.
///
/// See [PMS 8.3.1](https://projects.gentoo.org/pms/9/pms.html#operators).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    /// `<` — strictly less than the specified version.
    Less,
    /// `<=` — less than or equal to the specified version.
    LessOrEqual,
    /// `=` — exactly the specified version (including revision).
    /// When used with a version ending in `*`, performs prefix matching
    /// per PMS 8.3.1 (e.g., `=pkg-1.2*` matches `1.2.3`, `1.2.4`, etc.).
    Equal,
    /// `~` — matches the same base version, ignoring the revision
    /// (e.g. `~dev-lang/rust-1.75.0` matches `-r0`, `-r1`, etc.).
    Approximate,
    /// `>=` — greater than or equal to the specified version.
    GreaterOrEqual,
    /// `>` — strictly greater than the specified version.
    Greater,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operator::Less => write!(f, "<"),
            Operator::LessOrEqual => write!(f, "<="),
            Operator::Equal => write!(f, "="),
            Operator::Approximate => write!(f, "~"),
            Operator::GreaterOrEqual => write!(f, ">="),
            Operator::Greater => write!(f, ">"),
        }
    }
}

/// Package version according to PMS
///
/// Represents a version string such as `1.2.3a_alpha4_beta5_pre6_rc7_p8-r9`.
///
/// Ordering implements
/// [Algorithm 3.1](https://projects.gentoo.org/pms/9/pms.html#version-comparison):
/// numeric components are compared left-to-right, then the optional letter,
/// then suffixes (where `_p` sorts above the base while `_alpha`/`_beta`/`_pre`/`_rc`
/// sort below), and finally the revision.
///
/// See [PMS 3.2](https://projects.gentoo.org/pms/9/pms.html#version-specifications)
/// for the full version syntax.
///
/// # Differences from semver
///
/// - **Variable component count** — `1`, `1.2`, `1.2.3.4` are all valid
///   (semver requires exactly `major.minor.patch`).
/// - **Letter suffix** — a single lowercase letter after the numbers (e.g.
///   `1.2.3a`); no semver equivalent.
/// - **Typed suffixes** — `_alpha`, `_beta`, `_pre`, `_rc`, `_p` with
///   defined ordering; semver uses free-form pre-release identifiers.
/// - **Revision** — a dedicated `-rN` component for distribution-level changes.
/// - **Ordering** — `_p` sorts *above* the base version; semver pre-releases
///   always sort below.
/// - **Glob suffix** — PMS allows `*` as wildcard for version components
///   (e.g., `1.2*` matches `1.2.3`, `1.2.4`, etc.) when used with `=` operator.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Version {
    /// Version operator (set only inside a [`Dep`](crate::Dep)).
    pub op: Option<Operator>,
    /// Dot-separated numeric components (e.g. `[1, 2, 3]` for `1.2.3`).
    pub numbers: Vec<u64>,
    /// Optional single lowercase letter after the numeric components.
    pub letter: Option<char>,
    /// Zero or more version suffixes (`_alpha`, `_beta`, `_pre`, `_rc`, `_p`).
    pub suffixes: Vec<Suffix>,
    /// Package revision; defaults to `0` (omitted from display).
    pub revision: Revision,
    /// PMS glob suffix (`*`) for wildcard matching when used with `=` operator.
    /// When present, only the specified number of version components are used for comparison.
    pub glob: bool,
}

impl Version {
    /// Parse version from string without operator
    pub fn parse(input: &str) -> Result<Self> {
        parse_version()
            .parse(input)
            .map_err(|e| Error::InvalidVersion(format!("{}: {}", input, e)))
    }

    /// Base version without revision for ~ operator comparison
    pub fn base(&self) -> Self {
        Version {
            op: None,
            numbers: self.numbers.clone(),
            letter: self.letter,
            suffixes: self.suffixes.clone(),
            revision: Revision::default(),
            glob: false,
        }
    }

    /// Check if version has no suffixes (for * glob matching)
    pub fn without_suffix(&self) -> Self {
        Version {
            op: None,
            numbers: self.numbers.clone(),
            letter: self.letter,
            suffixes: Vec::new(),
            revision: Revision::default(),
            glob: false,
        }
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(op) = &self.op {
            write!(f, "{}", op)?;
        }

        for (i, num) in self.numbers.iter().enumerate() {
            if i > 0 {
                write!(f, ".")?;
            }
            write!(f, "{}", num)?;
        }

        if let Some(letter) = self.letter {
            write!(f, "{}", letter)?;
        }

        for suffix in &self.suffixes {
            write!(f, "{}", suffix)?;
        }

        write!(f, "{}", self.revision)?;

        if self.glob {
            write!(f, "*")?;
        }

        Ok(())
    }
}

/// PMS version comparison (Algorithm 3.1)
impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> Ordering {
        // PMS 8.3.1: glob matching — only compare the specified components
        if self.glob {
            return self.glob_cmp(other);
        }
        if other.glob {
            return other.glob_cmp(self).reverse();
        }

        // Compare numeric components
        let max_len = self.numbers.len().max(other.numbers.len());
        for i in 0..max_len {
            let a = self.numbers.get(i).copied().unwrap_or(0);
            let b = other.numbers.get(i).copied().unwrap_or(0);
            match a.cmp(&b) {
                Ordering::Equal => continue,
                other => return other,
            }
        }

        // Compare letter suffixes
        let a_letter = self.letter.unwrap_or('\0');
        let b_letter = other.letter.unwrap_or('\0');
        match a_letter.cmp(&b_letter) {
            Ordering::Equal => {}
            other => return other,
        }

        // Compare version suffixes
        let max_suffixes = self.suffixes.len().max(other.suffixes.len());
        for i in 0..max_suffixes {
            match (self.suffixes.get(i), other.suffixes.get(i)) {
                (Some(a), Some(b)) => match a.cmp(b) {
                    Ordering::Equal => continue,
                    other => return other,
                },
                (Some(s), None) => {
                    return if s.kind == SuffixKind::P {
                        Ordering::Greater
                    } else {
                        Ordering::Less
                    };
                }
                (None, Some(s)) => {
                    return if s.kind == SuffixKind::P {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    };
                }
                (None, None) => break,
            }
        }

        // Compare revisions
        self.revision.cmp(&other.revision)
    }
}

impl Version {
    /// PMS glob comparison for versions ending with `*`
    /// Per PMS 8.3.1: "if the version specified has an asterisk immediately following it,
    /// then only the given number of version components is used for comparison"
    fn glob_cmp(&self, other: &Version) -> Ordering {
        // Compare only the number of components specified in self (before *)
        let self_components = self.numbers.len();

        // Compare numeric components up to self's component count
        for i in 0..self_components {
            let a = self.numbers.get(i).copied().unwrap_or(0);
            let b = other.numbers.get(i).copied().unwrap_or(0);
            match a.cmp(&b) {
                Ordering::Equal => continue,
                other => return other,
            }
        }

        // If self has a letter, other must match it exactly
        if let Some(self_letter) = self.letter {
            let other_letter = other.letter.unwrap_or('\0');
            if self_letter != other_letter {
                return self_letter.cmp(&other_letter);
            }
        } else if other.letter.is_some() {
            // Self has no letter but other does - self is less specific
            return Ordering::Less;
        }

        // PMS: glob matching succeeds if prefix matches
        // Only fail if other has fewer components than self
        if other.numbers.len() < self_components {
            Ordering::Greater // other is "less than" the glob pattern
        } else {
            Ordering::Equal // prefix matches, glob succeeds
        }
    }
}

// Winnow parsers

fn parse_number<'s>() -> impl Parser<&'s str, u64, ErrMode<ContextError>> {
    digit1.try_map(|s: &str| s.parse::<u64>())
}

fn parse_letter<'s>() -> impl Parser<&'s str, char, ErrMode<ContextError>> {
    one_of('a'..='z')
}

fn parse_suffix_kind<'s>() -> impl Parser<&'s str, SuffixKind, ErrMode<ContextError>> {
    alt((
        "alpha".value(SuffixKind::Alpha),
        "beta".value(SuffixKind::Beta),
        "pre".value(SuffixKind::Pre),
        "rc".value(SuffixKind::Rc),
        "p".value(SuffixKind::P),
    ))
}

fn parse_suffix<'s>() -> impl Parser<&'s str, Suffix, ErrMode<ContextError>> {
    preceded('_', cut_err((parse_suffix_kind(), opt(parse_number()))))
        .map(|(kind, version)| Suffix { kind, version })
}

fn parse_revision<'s>() -> impl Parser<&'s str, Revision, ErrMode<ContextError>> {
    preceded("-r", cut_err(parse_number())).map(Revision)
}

pub(crate) fn parse_version<'s>() -> impl Parser<&'s str, Version, ErrMode<ContextError>> {
    (
        separated(1.., parse_number(), '.'),
        opt(parse_letter()),
        repeat(0.., parse_suffix()),
        opt(parse_revision()),
        opt('*'), // Handle PMS glob suffix for version wildcard matching
    )
        .map(|(numbers, letter, suffixes, revision, has_glob)| Version {
            op: None,
            numbers,
            letter,
            suffixes,
            revision: revision.unwrap_or_default(),
            glob: has_glob.is_some(),
        })
        .context(StrContext::Label("version"))
}

pub(crate) fn parse_operator<'s>() -> impl Parser<&'s str, Operator, ErrMode<ContextError>> {
    alt((
        "<=".value(Operator::LessOrEqual),
        "<".value(Operator::Less),
        ">=".value(Operator::GreaterOrEqual),
        ">".value(Operator::Greater),
        "~".value(Operator::Approximate),
        "=".value(Operator::Equal),
    ))
    .context(StrContext::Label("operator"))
}

impl FromStr for Version {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_parsing() {
        let v = Version::parse("1.2.3").unwrap();
        assert_eq!(v.numbers.len(), 3);
        assert_eq!(v.numbers[0], 1);
        assert_eq!(v.numbers[1], 2);
        assert_eq!(v.numbers[2], 3);
        assert_eq!(v.letter, None);
        assert!(v.suffixes.is_empty());
        assert_eq!(v.revision.0, 0);
    }

    #[test]
    fn test_version_with_letter() {
        let v = Version::parse("1.2.3a").unwrap();
        assert_eq!(v.letter, Some('a'));
    }

    #[test]
    fn test_version_with_suffixes() {
        let v = Version::parse("1.2.3_alpha4_beta5").unwrap();
        assert_eq!(v.suffixes.len(), 2);
        assert_eq!(v.suffixes[0].kind, SuffixKind::Alpha);
        assert_eq!(v.suffixes[0].version.unwrap(), 4);
        assert_eq!(v.suffixes[1].kind, SuffixKind::Beta);
        assert_eq!(v.suffixes[1].version.unwrap(), 5);
    }

    #[test]
    fn test_version_with_revision() {
        let v = Version::parse("1.2.3-r1").unwrap();
        assert_eq!(v.revision.0, 1);
    }

    #[test]
    fn test_version_comparison() {
        let v1 = Version::parse("1.2.3").unwrap();
        let v2 = Version::parse("1.2.4").unwrap();
        assert!(v1 < v2);

        let v3 = Version::parse("1.2.3-r1").unwrap();
        assert!(v1 < v3);

        let v4 = Version::parse("1.2.3_rc1").unwrap();
        assert!(v4 < v1);
    }

    // Issue 3: = version prefix with glob * suffix
    // Note: PMS specifies that * is part of the version, not the operator
    // So there is no separate =* operator - just = operator with * in version
    #[test]
    fn test_version_with_glob_suffix() {
        let version = Version::parse("1.2.3*").unwrap();
        assert!(version.glob);
        assert_eq!(version.numbers, vec![1, 2, 3]);
    }
}
