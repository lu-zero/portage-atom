use std::fmt;
use std::hash::Hash;
use std::str::FromStr;

use gentoo_interner::{DefaultInterner, Interned};
use winnow::combinator::cut_err;
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;

use crate::error::{Error, Result};

/// Category/Package Name (Cpn)
///
/// Represents unversioned package atoms like `dev-lang/rust`.
///
/// See [PMS 3.1](https://projects.gentoo.org/pms/9/pms.html#restrictions-upon-names)
/// for category and package naming rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Cpn {
    pub category: Interned<DefaultInterner>,
    pub package: Interned<DefaultInterner>,
}

impl Cpn {
    /// Create a new Cpn from strings
    pub fn new(category: impl AsRef<str>, package: impl AsRef<str>) -> Self {
        Cpn {
            category: Interned::intern(category.as_ref()),
            package: Interned::intern(package.as_ref()),
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
        write!(f, "{}/{}", self.category.resolve(), self.package.resolve())
    }
}

impl PartialOrd for Cpn {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cpn {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.category.resolve().cmp(other.category.resolve()) {
            std::cmp::Ordering::Equal => self.package.resolve().cmp(other.package.resolve()),
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
/// PMS 3.1.1: category name may contain [A-Za-z0-9+_.-], must not begin with hyphen or plus
pub(crate) fn parse_category<'s>()
-> impl Parser<&'s str, Interned<DefaultInterner>, ErrMode<ContextError>> {
    use crate::parsers::parse_ident_with_dot;

    parse_ident_with_dot()
        .verify(|s: &str| {
            let first_char = s.chars().next().unwrap();
            !matches!(first_char, '-' | '.' | '+')
        })
        .map(|s: &str| Interned::intern(s))
        .context(StrContext::Label("category"))
}

/// Parse package name
/// PMS: package name must start with letter/digit, contain alphanumeric + _ - +
/// Must not end with hyphen followed by version-like string
///
/// Note: In practice, Gentoo's tree contains packages whose names start with
/// an underscore (e.g. `acct-user/_cron-failure`). We accept those even though
/// PMS 3.1.2 technically requires an alphanumeric first character.
pub(crate) fn parse_package<'s>()
-> impl Parser<&'s str, Interned<DefaultInterner>, ErrMode<ContextError>> {
    use crate::parsers::parse_ident_base;

    parse_ident_base()
        .verify(|s: &str| {
            // Must start with alphanumeric or underscore.
            // PMS 3.1.2 requires alphanumeric, but real-world Gentoo packages
            // such as acct-user/_cron-failure begin with '_'.
            s.chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        })
        .map(|s: &str| Interned::intern(s))
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
    use crate::Cpv;

    #[test]
    fn test_cpn_parsing() {
        let cpn = Cpn::parse("dev-lang/rust").unwrap();
        assert_eq!(cpn.category.resolve(), "dev-lang");
        assert_eq!(cpn.package.resolve(), "rust");
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

    #[test]
    fn test_package_name_starting_with_underscore() {
        // Real-world Gentoo packages such as acct-user/_cron-failure have
        // names starting with '_'.  We accept them even though PMS 3.1.2
        // requires an alphanumeric first character.
        let cpn = Cpn::parse("acct-user/_cron-failure").unwrap();
        assert_eq!(cpn.category.resolve(), "acct-user");
        assert_eq!(cpn.package.resolve(), "_cron-failure");

        let cpn = Cpn::parse("acct-group/_cron-failure").unwrap();
        assert_eq!(cpn.category.resolve(), "acct-group");
        assert_eq!(cpn.package.resolve(), "_cron-failure");
    }

    #[test]
    fn test_package_name_cannot_end_with_hyphen_version() {
        // PMS 3.1.2: "must not end in a hyphen followed by anything matching the version syntax"
        // Note: This rule is enforced at the CPV level, not the CPN level.
        // The CPN parser allows hyphen endings, but the CPV parser ensures proper version boundary detection.

        // These are valid CPN names (the CPV parser will handle version detection)
        assert!(
            Cpn::parse("cat/pkg-").is_ok(),
            "Package name ending with hyphen is valid at CPN level"
        );
        assert!(
            Cpn::parse("cat/pkg-test").is_ok(),
            "Package name ending with hyphen+word should be valid"
        );

        // But when used in CPV context, the version boundary detection should work correctly
        let cpv1 = Cpv::parse("cat/pkg--1.2"); // pkg- is package, -1.2 is version
        assert!(
            cpv1.is_ok(),
            "CPV parser should handle hyphen in package name correctly"
        );
        let cpv1 = cpv1.unwrap();
        assert_eq!(cpv1.cpn.package.resolve(), "pkg-");
        assert_eq!(cpv1.version.numbers, vec![1, 2]);
    }

    #[test]
    fn test_package_name_no_arbitrary_length_limit() {
        // PMS doesn't specify length limits, so we shouldn't impose arbitrary ones

        // Valid: normal length
        assert!(Cpn::parse("cat/normal-package-name").is_ok());

        // Valid: very long name (PMS doesn't specify limits)
        let long_name = "a".repeat(100);
        assert!(Cpn::parse(&format!("cat/{}", long_name)).is_ok());

        // Valid: very long category (PMS doesn't specify limits)
        let long_cat = "a".repeat(100);
        assert!(Cpn::parse(&format!("{}/package", long_cat)).is_ok());
    }

    #[test]
    fn test_category_name_with_dot() {
        // PMS 3.1.1: category names may contain dots
        assert!(Cpn::parse("dev.lang/rust").is_ok());
        assert!(Cpn::parse("app-office/libreoffice").is_ok());
        assert!(Cpn::parse("media.gfx/gimp").is_ok());

        // Category names can start with underscore (allowed character)
        assert!(Cpn::parse("_special/package").is_ok());

        // But category names must not begin with hyphen, dot, or plus
        assert!(Cpn::parse("-dev-lang/rust").is_err());
        assert!(Cpn::parse(".dev-lang/rust").is_err());
        assert!(Cpn::parse("+dev-lang/rust").is_err());
    }

    #[test]
    fn test_cpn_copy() {
        let cpn = Cpn::parse("dev-lang/rust").unwrap();
        let cpn2 = cpn;
        assert_eq!(cpn, cpn2);
    }
}
