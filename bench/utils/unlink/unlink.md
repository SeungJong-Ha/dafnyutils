# unlink NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node unlink invocation`
- Source line range: 11114-11139
- Implementation: `coreutils/src/unlink.c` at submodule commit
  `2cf491412c199e2211880ec3f4ba387026638a33`
- License: GPL-3.0-or-later

This file summarizes the upstream GNU `unlink` behavior relevant to the benchmark.

## `unlink`: Remove a file name

`unlink` removes one specified file name using the system's `unlink` operation.
It is a smaller interface than `rm`: it takes a single file name and does not
offer recursive or interactive removal.

```text
unlink filename
```

Removing a symbolic link removes the link itself, leaving its target in place.
If a file has other hard-link names, those names remain usable. GNU `unlink`
does not remove directories.

The command accepts `--help` and `--version`. To remove a name beginning with
`-`, prefix it with `./`; for example, `unlink ./--help` removes the file named
`--help` instead of displaying help.

### Benchmark-Supported Behavior

The benchmark handles one pathname, including regular files and symbolic links,
plus `--help`, `--version`, `--`, and operand, option, and deletion errors.
No options are excluded by `IO.dfy`.

### Scope and model

- **Input and environment:** Finite arguments, long-option abbreviations, Linux
  filesystem, current user permissions, and C-locale diagnostics; stdin is unused.
- **Observation:** Output streams, exit status, and modeled filesystem. Help,
  version, and operand errors leave files unchanged. A failed `UnlinkPathSpec`
  does not guarantee filesystem preservation; maintainer review is pending.
- **Trusted API:** Shared parser, `UnlinkPathSpec`, errno text, argument/path quoting, and stream append
  contracts in `bench/core` revision `4ac0d9b34816c54c822bd9870794aafae1df3c13`.
- **Proof:** `Unlink.RunCore` ensures `UnlinkSpec.Spec` through `UnlinkProof`.
  `Decode` terminates; whole-process termination is not proved.

### Exit Status

The supported command exits with status 0 after a successful removal or a help
or version request. Operand, option, and deletion errors exit with status 1.
