#!/bin/bash

# Aristotle Prover Script
# Activates virtual environment and runs the prove.py script

set -e  # Exit on error

# Source common initialization
source "$(dirname "$0")/utils/init.sh"

# Change to project root
ensure_project_root

# Activate virtual environment
activate_venv

# Run the prove.py script
echo -e "${BLUE}Running Aristotle prover...${NC}"
python "$PROVE_PY" "$@"
