use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use winnow::combinator::cut_err;
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::take_while;

use crate::cpn::{parse_category, parse_package, Cpn};
use crate::error::{Error, Result};
use crate::version::{parse_version, Version};

/// Category/Package/Version (Cpv)
///
/// Represents versioned package atoms like `dev-lang/rust-1.75.0`.
/// The version is separated from the package name at the last hyphen
/// followed by a digit.
///
/// See [PMS 3.2](https://projects.gentoo.org/pms/9/pms.html#version-specifications)
/// for the version syntax and
/// [PMS 3.3](https://projects.gentoo.org/pms/9/pms.html#version-comparison)
/// for the version comparison algorithm.
#[derive(Debug, Clone)]
pub struct Cpv {
    pub cpn: Cpn,
    pub version: Version,
}

impl Cpv {
    /// Create a new Cpv
    pub fn new(cpn: Cpn, version: Version) -> Self {
        Cpv { cpn, version }
    }

    /// Parse from string
    pub fn parse(input: &str) -> Result<Self> {
        parse_cpv()
            .parse(input)
            .map_err(|e| Error::InvalidCpv(format!("{}: {}", input, e)))
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
}

impl fmt::Display for Cpv {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}-{}", self.cpn, self.version)
    }
}

impl PartialEq for Cpv {
    fn eq(&self, other: &Self) -> bool {
        self.cpn == other.cpn && self.version == other.version
    }
}

impl Eq for Cpv {}

impl Hash for Cpv {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.cpn.hash(state);
        self.version.hash(state);
    }
}

impl PartialOrd for Cpv {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cpv {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.cpn.cmp(&other.cpn) {
            std::cmp::Ordering::Equal => self.version.cmp(&other.version),
            other => other,
        }
    }
}

impl FromStr for Cpv {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

// Winnow parsers

/// Parse Cpv (category/package-version)
/// Package names can contain hyphens, so we need to find the version boundary
/// Per PMS, version always starts after the LAST hyphen followed by a digit
pub(crate) fn parse_cpv<'s>() -> impl Parser<&'s str, Cpv, ErrMode<ContextError>> {
    (
        parse_category(),
        '/',
        cut_err(take_while(1.., |c: char| {
            c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+' || c == '.' || c == '*'
        })),
    )
        .verify_map(|(category, _, pkg_ver): (String, char, &str)| {
            // Find the last -<digit> boundary to split package from version
            let bytes = pkg_ver.as_bytes();
            let mut version_start = None;

            for i in 0..bytes.len() {
                if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
                    version_start = Some(i);
                }
            }

            let version_pos = version_start?;
            let pkg_str = &pkg_ver[..version_pos];
            let ver_str = &pkg_ver[version_pos + 1..];

            // Validate package name
            let package = parse_package().parse(pkg_str).ok()?;

            // Parse version
            let version = parse_version().parse(ver_str).ok()?;

            Some(Cpv {
                cpn: Cpn { category, package },
                version,
            })
        })
        .context(StrContext::Label("cpv"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpv_parsing() {
        let cpv = Cpv::parse("dev-lang/rust-1.75.0").unwrap();
        assert_eq!(cpv.category(), "dev-lang");
        assert_eq!(cpv.package(), "rust");
        assert_eq!(cpv.version.numbers[0], 1);
        assert_eq!(cpv.version.numbers[1], 75);
        assert_eq!(cpv.version.numbers[2], 0);
        assert_eq!(cpv.to_string(), "dev-lang/rust-1.75.0");
    }

    #[test]
    fn test_cpv_with_revision() {
        let cpv = Cpv::parse("dev-lang/rust-1.75.0-r1").unwrap();
        assert_eq!(cpv.version.revision.0, 1);
        assert_eq!(cpv.to_string(), "dev-lang/rust-1.75.0-r1");
    }

    #[test]
    fn test_cpv_comparison() {
        let cpv1 = Cpv::parse("dev-lang/rust-1.75.0").unwrap();
        let cpv2 = Cpv::parse("dev-lang/rust-1.76.0").unwrap();
        assert!(cpv1 < cpv2);

        let cpv3 = Cpv::parse("dev-lang/rust-1.75.0-r1").unwrap();
        assert!(cpv1 < cpv3);
    }
}
