# Aristotle Project

Lean theorem proving projects using Mathlib and the Aristotle engine.

## Prerequisites

- **Python 3** (for aristotlelib)
- **Elan** (Lean version manager): https://github.com/leanprover/elan
  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

## Installation

Run the configuration script:

```bash
./scripts/configure.sh
```

This will:
- Create a Python virtual environment (`venv/`)
- Install Python dependencies (aristotlelib)
- Download Lean dependencies (~5.5GB of Mathlib to `.lake/`)
- Verify the installation

The script is **idempotent** - safe to run multiple times.

## Configuration

- **Lean version**: `v4.20.0-rc5` (defined in `lean-toolchain`)
- **Mathlib commit**: `d62eab0cc36ea522904895389c301cf8d844fd69` (defined in `lakefile.toml`)
- **Python dependencies**: See `requirements.txt`

## Project Structure

```
aristotle/
├── requirements.txt     # Python dependencies
├── lakefile.toml        # Lean project configuration
├── lean-toolchain       # Lean version
├── .lake/              # Lean dependencies (6GB, gitignored)
├── venv/               # Python virtual environment (gitignored)
├── problems/           # Your Lean theorem proving problems
│   ├── komal.lean
│   ├── ppp_easy.lean
│   ├── ppp_open.lean
│   └── ...
├── solutions/          # Generated solutions from Aristotle (gitignored)
└── scripts/            # Scripts directory
    ├── configure.sh    # Setup script
    ├── prove.sh        # Aristotle prover wrapper
    ├── status.sh       # Status checker wrapper
    └── utils/          # Python utilities
        ├── init.sh     # Common script initialization
        ├── prove.py    # Aristotle prover
        ├── status.py   # Status checker
        └── utils.py    # Shared utilities
```

## Usage

### Run Aristotle Prover

```bash
./scripts/prove.sh
```

This will activate the virtual environment and run the prover on the default problem.

### Check Project Status

```bash
./scripts/status.sh
```

This will list all your Aristotle projects and their status.

### Build Lean Projects

```bash
lake build
```

### Add New Problems

Simply create a new `.lean` file in the `problems/` directory:

```bash
touch problems/MyNewTheorem.lean
```

All Mathlib imports will work automatically!

## Notes

- The `.lake/` directory (6GB) contains Lean dependencies, shared by all problems
- The `venv/` directory contains Python dependencies
- The `solutions/` directory will contain generated solutions from Aristotle
- All are in `.gitignore` and `.lake/` and `venv/` will be recreated by `configure.sh`
- All scripts in `scripts/` use `scripts/utils/init.sh` for common initialization
- Scripts automatically activate the virtual environment when needed
