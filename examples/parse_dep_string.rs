//! Example demonstrating parsing ebuild dependency strings into DepEntry trees

use portage_atom::DepEntry;

/// Pretty-print a list of DepEntry with indentation.
fn print_entries(entries: &[DepEntry], indent: usize) {
    let pad = "  ".repeat(indent);
    for entry in entries {
        match entry {
            DepEntry::Atom(dep) => println!("{pad}{dep}"),
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                let neg = if *negate { "!" } else { "" };
                println!("{pad}{neg}{flag}? (");
                print_entries(children, indent + 1);
                println!("{pad})");
            }
            DepEntry::AnyOf(children) => {
                println!("{pad}|| (");
                print_entries(children, indent + 1);
                println!("{pad})");
            }
        }
    }
}

fn main() {
    let examples = [
        // Simple atoms
        "dev-lang/rust >=dev-libs/openssl-1.1.0",
        // Any-of group
        "|| ( dev-libs/openssl dev-libs/libressl )",
        // USE conditional
        "ssl? ( dev-libs/openssl ) !ssl? ( dev-libs/libressl )",
        // Nested structures (realistic DEPEND string)
        ">=dev-lang/rust-1.75.0 || ( ssl? ( >=dev-libs/openssl-1.1.0:0= ) dev-libs/libressl:0= ) !test? ( dev-libs/bar ) dev-libs/baz:2[foo,-debug]",
    ];

    for (i, input) in examples.iter().enumerate() {
        println!("{}. Input:  {input}", i + 1);
        match DepEntry::parse(input) {
            Ok(entries) => {
                println!("   Parsed: {} top-level entries", entries.len());
                print_entries(&entries, 3);

                // Round-trip through Display
                let displayed: Vec<String> = entries.iter().map(|e| e.to_string()).collect();
                println!("   Display: {}", displayed.join(" "));
            }
            Err(e) => println!("   Error: {e}"),
        }
        println!();
    }
}
