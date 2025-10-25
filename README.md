# Aristotle Project

Lean theorem proving using Mathlib and the Aristotle API.

## Dependencies

- git
- python3
- elan (Lean version manager)

## Setup

Run the configuration script from the root of the repo:
```bash
./scripts/configure.sh
```

## Usage

To solve a problem, call from the root of the repo:
```bash
./scripts/solve.sh
```

On first run, you'll be prompted to create an API key file - follow the prompt's instructions to place it in the correct location. Select a problem from the interactive list. Generated solutions can be collected in `solutions/`.

To check project status:
```bash
./scripts/status.sh
```

## Notes

- Uses Lean `v4.20.0-rc5` and Mathlib aligned with current Aristotle.
- When Aristotle updates Lean/Mathlib: edit `lean-toolchain` and `lakefile.toml` (rev), then run `./scripts/configure.sh`.
- Add new problems as `.lean` files in `problems/` directory.
