# Aristotle Project

Shell scripts for easier interaction with the Aristotle API. Provides convenient commands to submit Lean theorem proving problems and retrieve solutions.

## Requirements

- Aristotle API key (subscribe for one at https://aristotle.harmonic.fun)
- git
- python3
- elan

## Setup

Run the configuration script from the root of the repo to set up the environment (Lean, Mathlib, Python dependencies):
```bash
./scripts/configure.sh
```

## Usage

To solve a problem, call from the root of the repo:
```bash
./scripts/solve.sh
```

On first run, you'll be prompted to create an API key file - follow the prompt's instruction to place it in the correct location. Select a problem from the interactive list. Solutions will be saved to `solutions/` once complete.

To check the status of submitted problems on the Aristotle API (queued, in progress, completed):
```bash
./scripts/status.sh
```

To collect a completed solution from the server (only needed if `solve.sh` was interrupted locally):
```bash
./scripts/get_solution.sh
```

To clean up all generated files (venv, .lake, API key):
```bash
./scripts/clear.sh
```

## Notes

- Uses Lean `v4.20.0-rc5` and Mathlib aligned with current Aristotle.
- When Aristotle updates Lean/Mathlib: edit `lean-toolchain` and `lakefile.toml` (rev), then run `./scripts/configure.sh`.
- Add new problems as `.lean` files in `problems/` directory.
