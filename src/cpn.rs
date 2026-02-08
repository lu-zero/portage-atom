use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use winnow::combinator::cut_err;
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::take_while;

use crate::error::{Error, Result};

/// Category/Package Name (Cpn)
///
/// Represents unversioned package atoms like `dev-lang/rust`.
///
/// See [PMS 3.1](https://projects.gentoo.org/pms/latest/pms.html#restrictions-upon-names)
/// for category and package naming rules.
#[derive(Debug, Clone)]
pub struct Cpn {
    pub category: String,
    pub package: String,
}

impl Cpn {
    /// Create a new Cpn
    pub fn new(category: impl Into<String>, package: impl Into<String>) -> Self {
        Cpn {
            category: category.into(),
            package: package.into(),
        }
    }

    /// Parse from string
    pub fn parse(input: &str) -> Result<Self> {
        parse_cpn()
            .parse(input)
            .map_err(|e| Error::InvalidCpn(format!("{}: {}", input, e)))
    }

    /// Try to create from string (alias for parse)
    pub fn try_new(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

impl fmt::Display for Cpn {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.category, self.package)
    }
}

impl PartialEq for Cpn {
    fn eq(&self, other: &Self) -> bool {
        self.category == other.category && self.package == other.package
    }
}

impl Eq for Cpn {}

impl Hash for Cpn {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.category.hash(state);
        self.package.hash(state);
    }
}

impl PartialOrd for Cpn {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cpn {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.category.cmp(&other.category) {
            std::cmp::Ordering::Equal => self.package.cmp(&other.package),
            other => other,
        }
    }
}

impl FromStr for Cpn {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

// Winnow parsers

/// Parse category name
/// PMS: category name must start with letter/digit, contain alphanumeric + _ - +
pub(crate) fn parse_category<'s>() -> impl Parser<&'s str, String, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+'
    })
    .verify(|s: &str| s.chars().next().is_some_and(|c| c.is_ascii_alphanumeric()) && s.len() <= 64)
    .map(|s: &str| s.to_string())
    .context(StrContext::Label("category"))
}

/// Parse package name
/// PMS: package name must start with letter/digit, contain alphanumeric + _ - +
/// Must not end with hyphen followed by version-like string
pub(crate) fn parse_package<'s>() -> impl Parser<&'s str, String, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+'
    })
    .verify(|s: &str| s.chars().next().is_some_and(|c| c.is_ascii_alphanumeric()) && s.len() <= 64)
    .map(|s: &str| s.to_string())
    .context(StrContext::Label("package"))
}

/// Parse full Cpn (category/package)
pub(crate) fn parse_cpn<'s>() -> impl Parser<&'s str, Cpn, ErrMode<ContextError>> {
    (parse_category(), '/', cut_err(parse_package()))
        .map(|(category, _, package)| Cpn { category, package })
        .context(StrContext::Label("cpn"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpn_parsing() {
        let cpn = Cpn::parse("dev-lang/rust").unwrap();
        assert_eq!(cpn.category, "dev-lang");
        assert_eq!(cpn.package, "rust");
        assert_eq!(cpn.to_string(), "dev-lang/rust");
    }

    #[test]
    fn test_cpn_comparison() {
        let cpn1 = Cpn::parse("app-misc/foo").unwrap();
        let cpn2 = Cpn::parse("dev-lang/rust").unwrap();
        assert!(cpn1 < cpn2);

        let cpn3 = Cpn::parse("app-misc/bar").unwrap();
        assert!(cpn3 < cpn1);
    }

    #[test]
    fn test_invalid_cpn() {
        assert!(Cpn::parse("invalid").is_err());
        assert!(Cpn::parse("/package").is_err());
        assert!(Cpn::parse("category/").is_err());
    }
}
