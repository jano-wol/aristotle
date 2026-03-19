# Aristotle Project

Lean project scaffold for theorem proving problems, aligned with the [Aristotle](https://aristotle.harmonic.fun) Mathlib version.

## Requirements

- elan

## Setup

```bash
./scripts/configure.sh
```

## Cleanup

```bash
./scripts/clear.sh
```

## Notes

- Uses Lean `v4.28.0` and Mathlib aligned with current Aristotle.
- When versions update: edit `lean-toolchain` and `lakefile.toml`, then run `./scripts/clear.sh` and `./scripts/configure.sh`.
- Problems are in `problems/`, past server responses in `server_responses/`.
