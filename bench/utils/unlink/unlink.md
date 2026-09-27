# unlink

## Scope for maintainer review

- Reference: `coreutils/src/unlink.c` and `coreutils/doc/coreutils.texi`
  (`unlink invocation`). 
  - Commit: `2cf491412c199e2211880ec3f4ba387026638a33`.
  - License: GPL-3.0-or-later.
- Model/API revision: `bench/core` at
  `8bc3d29a3c4161526d42b35b4d14449fe74e3719`.
- AllowedInput:
  - Finite argument lists.
  - Options: `--help`, `--version`, and unambiguous long-option abbreviations.
  - `--` ends option parsing.
  - Deletion requires exactly one pathname.
  - Missing/extra operands and invalid options are errors.
- EnvironmentProfile: Linux, C locale, current user permissions. No stdin use
  or changes to credentials or umask.
- Observation: stdout, stderr, exit status, and filesystem effects. Unlinking
  a symlink preserves its target. Unlinking a hard-link name preserves other
  names. Dangling links are accepted; directories and missing paths fail.
- TrustedOperations: shared parser, `UnlinkPath`, `QuoteArgument`, `QuoteafPath`,
  `GetCLocaleErrnoText`, and stream writes. No options omitted due to IO API limits.

## Specification and proof

- SpecificationEntry: `UnlinkSpec.Spec(raw, io, exit)`. Help/version output,
  operand errors, deletion outcome, and exit status. Success: 0. Errors: 1.
- Frame: modifies `fsRegion`, `stdoutRegion`, and `stderrRegion`. Reads these
  regions plus the required clock and trusted filesystem/stream regions.
- TerminationPolicy: finite Core branches and Decode traversal. CLI uses
  `decreases *`; whole-process termination is not proved.
- CLI boundary: first help/version option wins. Parse failures honor earlier
  help/version requests by reparsing the prefix. Entry `RunCore` ensures Spec.
- Normal, boundary, and error behavior: deletion returns 0; operand, option,
  or deletion errors report diagnostics and return 1. Symlink targets and other
  hard-link names are preserved. Empty paths and directories fail.

Filesystem and parser correctness are trusted. Help/version and missing-operand
output use whole-append APIs; other diagnostics use partial-write contracts.
Closed-stream and `/dev/full` parity is unproved.

## Contribution and review evidence

Examples assume `FILE` and the file named `--help` are removable regular files.

| Command | Result | Exit |
| --- | --- | --- |
| `unlink FILE` | Remove the named entry | 0 |
| `unlink` | Missing operand diagnostic | 1 |
| `unlink FIRST SECOND` | Extra operand diagnostic; no deletion | 1 |
| `unlink --help --bad` | Display help | 0 |
| `unlink --bad --help` | Invalid option diagnostic | 1 |
| `unlink -- --help` | Remove the file named `--help` | 0 |

Deleting a symlink target or accepting extra operands violates the stated behavior.

- Runtime: 2 Dafny Decode cases and 15 GNU comparison cases passed, including
  permission-denied diagnostics and file preservation.
- Last proof run: 172 verified, 0 errors. Core proof does not cover all CLI exits.
- Fuzzer: 16 fixed scenarios plus generated inputs. Seed 1: 20/20 matches;
  no mismatches, timeouts, or incomplete observations. Finite tests are not
  proof of full parity.
- Final contribution gate: `make check TASK=unlink` reported
  `unlink: checks passed`. Proof tests: 3 passed, 15 deselected. Runtime report:
  `_build/contribution_checks/unlink/implementation-tests.xml` (15 passed,
  no failures, errors, or skipped cases). Final gate output was supplied by
  the contributor; the runtime report was inspected locally.
- Remaining review: upstream test comments and public profile review.

Maintainer scope/specification approval is pending. Report commands, versions,
final results, and actual AI assistance in the PR. Keep evaluator-only cases
and reference answers outside the public description/profile. Report model
gaps to maintainers; final specification approval requires human review.
