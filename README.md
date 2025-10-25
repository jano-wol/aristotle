# Aristotle Project

Lean theorem proving using Mathlib and the Aristotle API.

## Setup

Install Elan (Lean version manager): https://github.com/leanprover/elan

Create `aristotle_api_key.txt` in the project root with your Aristotle API key.

Run the configuration script from the root of the repo:
```bash
./scripts/configure.sh
```

This will create a Python virtual environment, install dependencies, and download ~6GB of Mathlib.

## Usage

To solve a problem, call from the root of the repo:
```bash
./scripts/solve.sh
```

Select a problem from the interactive list. Solutions are saved to `solutions/`.

To check project status:
```bash
./scripts/status.sh
```

## Notes

- Uses Lean `v4.20.0-rc5` and Mathlib aligned with current Aristotle.
- When Aristotle updates Lean/Mathlib: edit `lean-toolchain` and `lakefile.toml` (rev), then run `./scripts/configure.sh`.
- Add new problems as `.lean` files in `problems/` directory.
