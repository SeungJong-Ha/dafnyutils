use crate::fuzz::system_state_concretizer::symlink_target_stays_within_fixture;
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, HardlinkSpec, SymlinkSpec};
use rand::rngs::StdRng;
use rand::Rng;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

pub(super) fn basic_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"beta\n".to_vec(),
                mode: 0o600,
            },
            FileSpec {
                relative_path: PathBuf::from("target.txt"),
                bytes: b"target\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("a-link"),
            target: PathBuf::from("a.txt"),
        }],
        hardlinks: Vec::new(),
    }
}

pub(super) fn line_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"one\n\nthree\nfour\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("left.txt"),
                bytes: b"apple\nbanana\nbanana\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right.txt"),
                bytes: b"banana\ncarrot\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("dups.txt"),
                bytes: b"a\na\nb\nc\nc\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("case.txt"),
                bytes: b"A\na\nB\nb\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("empty.txt"),
                bytes: Vec::new(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("payload.bin"),
                bytes: vec![0, 1, 2, 3, b'\n'],
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("target.txt"),
                bytes: b"existing target\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("a-link"),
            target: PathBuf::from("a.txt"),
        }],
        hardlinks: Vec::new(),
    }
}

pub(super) fn generate_line_fixture_blueprint() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"one\n\nthree\nfour\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("dups.txt"),
                bytes: b"a\na\nb\nc\nc\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("case.txt"),
                bytes: b"A\na\nB\nb\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("empty.txt"),
                bytes: Vec::new(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

pub(super) fn generate_fixture_blueprint(
    rng: &mut StdRng,
    max_fs_entries: usize,
    allow_dangling_symlinks: bool,
) -> FixtureBlueprint {
    let total_entries = max_fs_entries.max(1);
    let mut directory_paths = BTreeSet::new();
    let target_dir_count = rng.random_range(1..=usize::min(4, total_entries));
    while directory_paths.len() < target_dir_count {
        directory_paths.insert(random_relative_dir(rng));
    }

    let directory_pool: Vec<PathBuf> = directory_paths.iter().cloned().collect();
    let mut files = Vec::new();
    let mut occupied_paths = directory_paths.clone();
    let remaining_after_dirs = total_entries.saturating_sub(directory_paths.len());
    let target_file_count = if remaining_after_dirs == 0 {
        0
    } else {
        rng.random_range(1..=remaining_after_dirs)
    };
    while files.len() < target_file_count {
        let mut relative_path = PathBuf::new();
        if !directory_pool.is_empty() && rng.random_bool(0.8) {
            let idx = rng.random_range(0..directory_pool.len());
            relative_path.push(&directory_pool[idx]);
        }
        relative_path.push(random_file_name(rng));
        if occupied_paths.insert(relative_path.clone()) {
            files.push(FileSpec {
                relative_path,
                bytes: random_file_contents(rng),
                mode: random_file_mode(rng),
            });
        }
    }

    let existing_targets: Vec<PathBuf> = directory_paths
        .iter()
        .cloned()
        .chain(files.iter().map(|f| f.relative_path.clone()))
        .collect();

    let remaining_after_files = total_entries.saturating_sub(directory_paths.len() + files.len());
    let symlink_budget = usize::min(2, remaining_after_files);
    let symlinks = generate_symlink_specs(
        rng,
        &directory_pool,
        &existing_targets,
        &mut occupied_paths,
        symlink_budget,
        allow_dangling_symlinks,
    );
    let mut hardlink_rng = rng.clone();
    let hardlinks = if total_entries > directory_paths.len() + files.len() + symlinks.len()
        && !files.is_empty()
        && hardlink_rng.random_bool(0.3)
    {
        let symlink_source = if !symlinks.is_empty() && hardlink_rng.random_bool(0.2) {
            Some(&symlinks[hardlink_rng.random_range(0..symlinks.len())])
        } else {
            None
        };
        let source_relative_path = symlink_source.map_or_else(
            || {
                files[hardlink_rng.random_range(0..files.len())]
                    .relative_path
                    .clone()
            },
            |source| source.relative_path.clone(),
        );
        let relative_path = loop {
            let mut path = PathBuf::new();
            if !directory_pool.is_empty() && hardlink_rng.random_bool(0.8) {
                path.push(&directory_pool[hardlink_rng.random_range(0..directory_pool.len())]);
            }
            path.push(random_file_name(&mut hardlink_rng));
            if occupied_paths.contains(&path)
                || symlink_source.is_some_and(|source| {
                    !symlink_target_stays_within_fixture(&path, &source.target)
                })
            {
                continue;
            }
            occupied_paths.insert(path.clone());
            break path;
        };
        vec![HardlinkSpec {
            relative_path,
            source_relative_path,
        }]
    } else {
        Vec::new()
    };

    let directories = directory_paths
        .into_iter()
        .map(|relative_path| DirSpec {
            relative_path,
            mode: random_directory_mode(rng),
        })
        .collect();

    FixtureBlueprint {
        directories,
        files,
        symlinks,
        hardlinks,
    }
}

impl FixtureBlueprint {
    pub(in crate::fuzz) fn existing_operands(&self) -> Vec<String> {
        let mut paths = BTreeSet::new();
        paths.insert(".".to_string());
        for dir in &self.directories {
            paths.insert(dir.relative_path.display().to_string());
        }
        for file in &self.files {
            paths.insert(file.relative_path.display().to_string());
            if let Some(parent) = file.relative_path.parent() {
                if !parent.as_os_str().is_empty() {
                    paths.insert(parent.display().to_string());
                }
            }
        }
        for symlink in &self.symlinks {
            paths.insert(symlink.relative_path.display().to_string());
            if let Some(parent) = symlink.relative_path.parent() {
                if !parent.as_os_str().is_empty() {
                    paths.insert(parent.display().to_string());
                }
            }
        }
        for hardlink in &self.hardlinks {
            paths.insert(hardlink.relative_path.display().to_string());
            if let Some(parent) = hardlink.relative_path.parent() {
                if !parent.as_os_str().is_empty() {
                    paths.insert(parent.display().to_string());
                }
            }
            paths.insert(hardlink.source_relative_path.display().to_string());
        }
        paths.into_iter().collect()
    }

    pub(in crate::fuzz) fn random_cwd(&self, rng: &mut StdRng) -> PathBuf {
        if self.directories.is_empty() || !rng.random_bool(0.5) {
            return PathBuf::from(".");
        }
        let idx = rng.random_range(0..self.directories.len());
        self.directories[idx].relative_path.clone()
    }
}

pub(super) fn generate_missing_operands(rng: &mut StdRng) -> Vec<String> {
    let mut missing = BTreeSet::new();
    let target_count = rng.random_range(2..=6);
    while missing.len() < target_count {
        missing.insert(random_missing_operand(rng));
    }
    missing.into_iter().collect()
}

fn random_missing_operand(rng: &mut StdRng) -> String {
    match rng.random_range(0..5) {
        0 => format!(
            "{}{}",
            random_name_component(rng, 5, 12),
            rng.random_range(100..10000)
        ),
        1 => format!(
            "{}/{}",
            random_name_component(rng, 4, 10),
            random_file_name(rng)
        ),
        2 => format!(
            "{}/{}",
            random_name_component(rng, 4, 10),
            random_name_component(rng, 4, 10)
        ),
        3 => format!(".{}", random_name_component(rng, 3, 8)),
        _ => format!(
            "{}-{}",
            random_name_component(rng, 4, 10),
            rng.random_range(100..10000)
        ),
    }
}

fn generate_symlink_specs(
    rng: &mut StdRng,
    directory_pool: &[PathBuf],
    existing_targets: &[PathBuf],
    occupied_paths: &mut BTreeSet<PathBuf>,
    symlink_budget: usize,
    allow_dangling_symlinks: bool,
) -> Vec<SymlinkSpec> {
    #[cfg(unix)]
    {
        let target_count = if symlink_budget == 0 {
            0
        } else {
            rng.random_range(0..=symlink_budget)
        };
        let mut symlinks = Vec::new();
        let mut attempts = 0usize;
        while symlinks.len() < target_count && attempts < target_count * 40 + 20 {
            attempts += 1;
            let mut relative_path = PathBuf::new();
            if !directory_pool.is_empty() && rng.random_bool(0.7) {
                let idx = rng.random_range(0..directory_pool.len());
                relative_path.push(&directory_pool[idx]);
            }
            relative_path.push(random_symlink_name(rng));

            if !occupied_paths.insert(relative_path.clone()) {
                continue;
            }

            let parent = relative_path.parent().unwrap_or_else(|| Path::new(""));
            let target =
                random_symlink_target(rng, parent, existing_targets, allow_dangling_symlinks);
            symlinks.push(SymlinkSpec {
                relative_path,
                target,
            });
        }
        symlinks
    }
    #[cfg(not(unix))]
    {
        let _ = (
            rng,
            directory_pool,
            existing_targets,
            occupied_paths,
            symlink_budget,
            allow_dangling_symlinks,
        );
        Vec::new()
    }
}

fn random_symlink_target(
    rng: &mut StdRng,
    parent: &Path,
    existing_targets: &[PathBuf],
    allow_dangling_symlinks: bool,
) -> PathBuf {
    if !existing_targets.is_empty() && (!allow_dangling_symlinks || rng.random_bool(0.75)) {
        let idx = rng.random_range(0..existing_targets.len());
        let target = &existing_targets[idx];
        if !allow_dangling_symlinks || rng.random_bool(0.7) {
            relative_path_from(parent, target)
        } else {
            target.clone()
        }
    } else {
        random_dangling_target(rng)
    }
}

fn relative_path_from(base: &Path, target: &Path) -> PathBuf {
    let base_components: Vec<_> = base.components().collect();
    let target_components: Vec<_> = target.components().collect();
    let mut shared = 0usize;
    while shared < base_components.len()
        && shared < target_components.len()
        && base_components[shared] == target_components[shared]
    {
        shared += 1;
    }

    let mut relative = PathBuf::new();
    for _ in shared..base_components.len() {
        relative.push("..");
    }
    for component in target_components.iter().skip(shared) {
        relative.push(component.as_os_str());
    }

    if relative.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        relative
    }
}

fn random_dangling_target(rng: &mut StdRng) -> PathBuf {
    match rng.random_range(0..4) {
        0 => PathBuf::from(format!("missing-{}", rng.random_range(100..10000))),
        1 => {
            let mut path = PathBuf::from("missing");
            path.push(random_name_component(rng, 4, 10));
            path.push(random_file_name(rng));
            path
        }
        2 => PathBuf::from(format!(
            "ghost-{}.{}",
            random_name_component(rng, 3, 8),
            random_name_component(rng, 2, 4)
        )),
        _ => {
            let mut path = PathBuf::new();
            path.push(random_name_component(rng, 4, 10));
            path.push(random_name_component(rng, 4, 10));
            path
        }
    }
}

fn random_relative_dir(rng: &mut StdRng) -> PathBuf {
    let depth = rng.random_range(1..=3);
    let mut path = PathBuf::new();
    for _ in 0..depth {
        path.push(random_name_component(rng, 3, 10));
    }
    path
}

fn random_file_name(rng: &mut StdRng) -> String {
    let ext_pool = ["txt", "bin", "dat", "log", "cfg", "tmp", "md"];
    let stem = random_name_component(rng, 3, 12);
    let ext = ext_pool[rng.random_range(0..ext_pool.len())];
    match rng.random_range(0..6) {
        0 => format!("{stem}.{ext}"),
        1 => format!(".{stem}.{ext}"),
        2 => format!("{stem}-{}", rng.random_range(0..1000)),
        3 => format!("{stem}_{:02}.{ext}", rng.random_range(0..100)),
        4 => format!("{}.{}", random_name_component(rng, 1, 4), ext),
        _ => stem,
    }
}

fn random_symlink_name(rng: &mut StdRng) -> String {
    match rng.random_range(0..4) {
        0 => format!("{}-link", random_name_component(rng, 3, 10)),
        1 => format!("ln-{}", random_name_component(rng, 3, 10)),
        2 => format!("{}.lnk", random_name_component(rng, 3, 10)),
        _ => format!(".{}-sym", random_name_component(rng, 3, 8)),
    }
}

pub(super) fn random_file_mode(rng: &mut StdRng) -> u32 {
    const MODES: &[u32] = &[
        0o400, 0o444, 0o600, 0o640, 0o644, 0o666, 0o700, 0o744, 0o755, 0o777, 0o4755, 0o2755,
        0o1755,
    ];
    MODES[rng.random_range(0..MODES.len())]
}

fn random_directory_mode(rng: &mut StdRng) -> u32 {
    const MODES: &[u32] = &[
        0o700, 0o711, 0o750, 0o755, 0o770, 0o775, 0o777, 0o1777, 0o2755,
    ];
    MODES[rng.random_range(0..MODES.len())]
}

pub(super) fn random_file_contents(rng: &mut StdRng) -> Vec<u8> {
    match rng.random_range(0..9) {
        0 => Vec::new(),
        1 => random_bytes(rng, 1, 64),
        2 => random_bytes(rng, 65, 2048),
        3 => random_bytes(rng, 4097, 16384),
        4 => random_printable_text_bytes(rng),
        5 => random_line_text_bytes(rng),
        6 => random_repeated_pattern_bytes(rng),
        7 => random_zero_heavy_bytes(rng),
        _ => random_incrementing_bytes(rng),
    }
}

fn random_printable_text_bytes(rng: &mut StdRng) -> Vec<u8> {
    let alphabet =
        b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 .,;:_-+/()[]{}!?";
    let len = rng.random_range(8..=512);
    (0..len)
        .map(|_| {
            let idx = rng.random_range(0..alphabet.len());
            alphabet[idx]
        })
        .collect()
}

fn random_line_text_bytes(rng: &mut StdRng) -> Vec<u8> {
    let line_count = rng.random_range(1..=24);
    let mut out = Vec::new();
    for line_idx in 0..line_count {
        let repeat_count = rng.random_range(1..=8);
        let tail = "x".repeat(repeat_count);
        let line = format!(
            "{}:{}:{}\n",
            line_idx,
            random_name_component(rng, 3, 10),
            tail
        );
        out.extend_from_slice(line.as_bytes());
    }
    out
}

fn random_repeated_pattern_bytes(rng: &mut StdRng) -> Vec<u8> {
    let pattern = random_bytes(rng, 1, 16);
    let repeat_count = rng.random_range(1..=128);
    let mut out = Vec::with_capacity(pattern.len() * repeat_count);
    for _ in 0..repeat_count {
        out.extend_from_slice(&pattern);
    }
    out
}

fn random_zero_heavy_bytes(rng: &mut StdRng) -> Vec<u8> {
    let len = rng.random_range(1..=1024);
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        if rng.random_bool(0.7) {
            out.push(0);
        } else {
            out.push(rng.random::<u8>());
        }
    }
    out
}

fn random_incrementing_bytes(rng: &mut StdRng) -> Vec<u8> {
    let len = rng.random_range(1..=512);
    let start = rng.random::<u8>();
    (0..len)
        .map(|idx| start.wrapping_add((idx % 251) as u8))
        .collect()
}

// Bytes on which the utilities' shell-quoting specifications actually branch.
// `/` and NUL are excluded so every generated name stays a legal POSIX filename,
// and everything here is valid UTF-8 so the JSON repro bundles keep working.
const QUOTE_TRIGGER_CHARS: &[char] = &[
    '\'', ' ', '#', '~', '{', '}', '$', '!', '"', '&', '(', ')', '*', ';', '<', '=', '>', '[', ']',
    '^', '`', '|', '?', '\\', ':', '\t', 'é',
];

/// One in this many name components is generated with quote triggers, so the
/// existing plain-name coverage is preserved while the quoting paths are reached.
const QUOTE_TRIGGER_ONE_IN: u32 = 4;

pub(in crate::fuzz) fn contains_quote_trigger(text: &str) -> bool {
    text.chars().any(|ch| QUOTE_TRIGGER_CHARS.contains(&ch))
}

/// A name component carrying at least one shell-quote trigger, mixed with
/// ordinary characters so operands stay realistic rather than degenerate.
pub(super) fn random_quote_trigger_component(
    rng: &mut StdRng,
    min_len: usize,
    max_len: usize,
) -> String {
    let plain = b"abcdefghijklmnopqrstuvwxyz0123456789";
    let len = if max_len <= min_len {
        min_len.max(1)
    } else {
        rng.random_range(min_len.max(1)..=max_len)
    };
    let trigger_at = rng.random_range(0..len);
    let mut out = String::with_capacity(len + 1);
    for position in 0..len {
        if position == trigger_at {
            let idx = rng.random_range(0..QUOTE_TRIGGER_CHARS.len());
            out.push(QUOTE_TRIGGER_CHARS[idx]);
        } else {
            let idx = rng.random_range(0..plain.len());
            out.push(char::from(plain[idx]));
        }
    }
    out
}

pub(super) fn random_name_component(rng: &mut StdRng, min_len: usize, max_len: usize) -> String {
    if max_len > 0 && rng.random_range(0..QUOTE_TRIGGER_ONE_IN) == 0 {
        return random_quote_trigger_component(rng, min_len, max_len);
    }
    let alphabet = b"abcdefghijklmnopqrstuvwxyz0123456789-_";
    let leading_alphabet = b"abcdefghijklmnopqrstuvwxyz0123456789_";
    let len = if max_len <= min_len {
        min_len
    } else {
        rng.random_range(min_len..=max_len)
    };
    let mut out = String::with_capacity(len);
    if len == 0 {
        return out;
    }
    let idx = rng.random_range(0..leading_alphabet.len());
    out.push(char::from(leading_alphabet[idx]));
    for _ in 1..len {
        let idx = rng.random_range(0..alphabet.len());
        out.push(char::from(alphabet[idx]));
    }
    out
}

fn random_bytes(rng: &mut StdRng, min_len: usize, max_len: usize) -> Vec<u8> {
    let len = if max_len <= min_len {
        min_len
    } else {
        rng.random_range(min_len..=max_len)
    };
    (0..len).map(|_| rng.random::<u8>()).collect()
}

pub(super) fn random_system_state(rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint {
    generate_fixture_blueprint(rng, max_fs_entries, true)
}

pub(super) fn line_system_state(_rng: &mut StdRng, _max_fs_entries: usize) -> FixtureBlueprint {
    generate_line_fixture_blueprint()
}
