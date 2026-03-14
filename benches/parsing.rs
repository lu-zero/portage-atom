use criterion::{Criterion, black_box, criterion_group, criterion_main};
use portage_atom::{Cpn, Cpv, Dep};

fn bench_cpn_parsing(c: &mut Criterion) {
    let inputs = [
        "dev-lang/rust",
        "app-editors/vim",
        "media-video/ffmpeg",
        "sys-kernel/gentoo-sources",
        "dev-python/numpy",
    ];

    c.bench_function("cpn_parse", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(Cpn::parse(input).unwrap());
            }
        })
    });
}

fn bench_cpv_parsing(c: &mut Criterion) {
    let inputs = [
        "dev-lang/rust-1.75.0",
        "app-editors/vim-9.0.2167",
        "media-video/ffmpeg-6.1",
        "sys-kernel/gentoo-sources-6.6.13",
        "dev-python/numpy-1.26.3",
    ];

    c.bench_function("cpv_parse", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(Cpv::parse(input).unwrap());
            }
        })
    });
}

fn bench_dep_parsing(c: &mut Criterion) {
    let inputs = [
        "dev-lang/rust",
        ">=dev-lang/rust-1.75.0",
        ">=dev-lang/rust-1.75.0:0",
        ">=dev-lang/rust-1.75.0:0[llvm_targets_AMDGPU]",
        "!!>=dev-lang/rust-1.75.0:0/1.75[llvm_targets_AMDGPU,-debug]::gentoo",
    ];

    c.bench_function("dep_parse", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(Dep::parse(input).unwrap());
            }
        })
    });
}

fn bench_cpn_comparison(c: &mut Criterion) {
    let cpns: Vec<Cpn> = (0..1000)
        .map(|i| Cpn::new("cat", format!("pkg-{i}")))
        .collect();

    c.bench_function("cpn_compare", |b| {
        b.iter(|| {
            for i in 0..cpns.len() - 1 {
                black_box(cpns[i] == cpns[i + 1]);
            }
        })
    });
}

fn bench_interning_dedup(c: &mut Criterion) {
    c.bench_function("intern_same_string_1000x", |b| {
        b.iter(|| {
            for _ in 0..1000 {
                black_box(Cpn::new("dev-lang", "rust"));
            }
        })
    });
}

criterion_group!(
    benches,
    bench_cpn_parsing,
    bench_cpv_parsing,
    bench_dep_parsing,
    bench_cpn_comparison,
    bench_interning_dedup,
);

criterion_main!(benches);
