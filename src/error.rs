/// Error type for portage-atom parsing and operations
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    #[error("parse error: {0}")]
    Parse(String),

    #[error("invalid category: {0}")]
    InvalidCategory(String),

    #[error("invalid package: {0}")]
    InvalidPackage(String),

    #[error("invalid version: {0}")]
    InvalidVersion(String),

    #[error("invalid cpv: {0}")]
    InvalidCpv(String),

    #[error("invalid cpn: {0}")]
    InvalidCpn(String),

    #[error("invalid dep: {0}")]
    InvalidDep(String),

    #[error("invalid slot: {0}")]
    InvalidSlot(String),

    #[error("invalid use dep: {0}")]
    InvalidUseDep(String),

    #[error("invalid operator: {0}")]
    InvalidOperator(String),

    #[error("invalid dep string: {0}")]
    InvalidDepString(String),
}

/// Result type for portage-atom operations
pub type Result<T> = std::result::Result<T, Error>;
