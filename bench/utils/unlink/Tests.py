"""GNU parity cases for unlink."""

import fcntl
import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
UTILITY = "unlink"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build the two targets only for runtime cases; local Make targets use -n0."""
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def assert_parity(
    executables: tuple[Path, Path],
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> None:
    """Compare a read-only scenario, including stderr on error exits."""
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, cwd, input_data=input_data)
    actual = run_bench_utility(candidate, args, cwd, input_data=input_data)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)

# Missing operands report a failure and usage guidance.
def test_missing_operand_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    assert_parity(executables, [], tmp_path)

# Extra operands are rejected without deleting either file.
def test_extra_operand_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    (ref_dir / "a").write_bytes(b"hello a")
    (bench_dir / "a").write_bytes(b"hello a")
    (ref_dir / "b").write_bytes(b"hello b")
    (bench_dir / "b").write_bytes(b"hello b")

    reference, candidate = executables
    ref = run_coreutils_utility(reference, UTILITY, ["a", "b"], ref_dir)
    bench = run_bench_utility(candidate, ["a", "b"], bench_dir)
    assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)

    for dir in (ref_dir, bench_dir):
        assert (dir / "a").read_bytes() == b"hello a"
        assert (dir / "b").read_bytes() == b"hello b"

# Deleting a regular file preserves unrelated files.
def test_regular_file_deletion_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    (ref_dir / "target").write_bytes(b"hello")
    (bench_dir / "target").write_bytes(b"hello")

    reference, candidate = executables
    ref = run_coreutils_utility(reference, UTILITY, ["target"], ref_dir)
    bench = run_bench_utility(candidate, ["target"], bench_dir)
    assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)

    assert not (ref_dir / "target").exists()
    assert not (bench_dir / "target").exists()

# Deleting a symbolic link preserves its target.
def test_symlink_deletion_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables

    for dir in (ref_dir, bench_dir):
        (dir / "target").write_bytes(b"hello")
        (dir / "link").symlink_to("target")

    ref = run_coreutils_utility(reference, UTILITY, ["link"], ref_dir)
    bench = run_bench_utility(candidate, ["link"], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 0

    for dir in (ref_dir, bench_dir):
        assert not (dir / "link").is_symlink()
        assert (dir / "target").read_bytes() == b"hello"

# A dangling symbolic link can be removed.
def test_dangling_symlink_deletion_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables

    for dir in (ref_dir, bench_dir):
        (dir / "target").write_bytes(b"hello")
        (dir / "link").symlink_to("target")
        (dir / "target").unlink()

    ref = run_coreutils_utility(reference, UTILITY, ["link"], ref_dir)
    bench = run_bench_utility(candidate, ["link"], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 0

    for dir in (ref_dir, bench_dir):
        assert not (dir / "link").is_symlink()
        assert not (dir / "target").exists()

# Deleting one hard-link name preserves the other name.
def test_hard_link_deletion_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables

    for dir in (ref_dir, bench_dir):
        (dir / "target").write_bytes(b"hello")
        (dir / "alias").hardlink_to(dir / "target")

    ref = run_coreutils_utility(reference, UTILITY, ["alias"], ref_dir)
    bench = run_bench_utility(candidate, ["alias"], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 0

    for dir in (ref_dir, bench_dir):
        assert not (dir / "alias").exists()
        assert (dir / "target").read_bytes() == b"hello"
        assert (dir / "target").stat().st_nlink == 1

# A nonexistent pathname produces a deletion error.
def test_missing_path_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables

    ref = run_coreutils_utility(reference, UTILITY, ["nothing"], ref_dir)
    bench = run_bench_utility(candidate, ["nothing"], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 1

# An empty pathname produces a deletion error.
def test_empty_path_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables

    ref = run_coreutils_utility(reference, UTILITY, [""], ref_dir)
    bench = run_bench_utility(candidate, [""], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 1

# A directory operand is rejected without deleting its contents.
def test_directory_operand_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    for dir in (ref_dir, bench_dir):
        (dir / "folder").mkdir()
        (dir / "folder" / "target").write_bytes(b"hello")
    reference, candidate = executables

    ref = run_coreutils_utility(reference, UTILITY, ["folder"], ref_dir)
    bench = run_bench_utility(candidate, ["folder"], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 1
    for dir in (ref_dir, bench_dir):
        assert (dir / "folder").is_dir()
        assert (dir / "folder" / "target").read_bytes() == b"hello"

# Help displays the requested message without deleting files.
def test_help_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    assert_parity(executables, ["--help"], tmp_path)

# Version displays the requested message without deleting files.
def test_version_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    assert_parity(executables, ["--version"], tmp_path)

# An invalid option produces the GNU diagnostic.
def test_invalid_option_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    assert_parity(executables, ["--bad"], tmp_path)

# Help and version respect GNU option precedence.
def test_option_precedence_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    for args in [
        ["--help", "--version"],
        ["--version", "--help"],
        ["--help", "--bad"],
        ["--bad", "--help"]
    ]:
        assert_parity(executables, args, tmp_path)

# The option delimiter permits a pathname beginning with a hyphen.
def test_option_like_path_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables
    (ref_dir / "--help").write_bytes(b"hello")
    (bench_dir / "--help").write_bytes(b"hello")

    ref = run_coreutils_utility(reference, UTILITY, ["--", "--help"], ref_dir)
    bench = run_bench_utility(candidate, ["--", "--help"], bench_dir)
    assert_result_matches_reference(
        ref, bench, ignore_stderr_when_exit_nonzero=False
    )
    assert ref[2] == bench[2] == 0
    for dir in (ref_dir, bench_dir):
        assert not (dir / "--help").exists()

# A non-writable parent directory prevents deletion and preserves the file.
def test_no_permission_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path 
) -> None:
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    try:
        for dir in (ref_dir, bench_dir):
            (dir / "target").write_bytes(b"hello")
            dir.chmod(0o555)
        reference, candidate = executables

        ref = run_coreutils_utility(reference, UTILITY, ["target"], ref_dir)
        bench = run_bench_utility(candidate, ["target"], bench_dir)
        assert_result_matches_reference(
            ref, bench, ignore_stderr_when_exit_nonzero=False
        )
        assert ref[2] == bench[2] == 1
        assert ref[2] == bench[2] == 1
        for dir in (ref_dir, bench_dir):
            assert (dir / "target").read_bytes() == b"hello"
    finally:
        ref_dir.chmod(0o755)
        bench_dir.chmod(0o755)
        


# Check each proof module as well as the entry contract required by make check.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename", ["UnlinkCore.dfy", "UnlinkProof.dfy", "Unlink.dfy"]
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the Dafny proof surface, not GNU runtime behavior.
    run_dafny_verify(PROJECT / filename)
