#!/bin/bash

# Aristotle Solver Script
# Activates virtual environment and runs the solve.py script

set -e  # Exit on error

# Source common initialization
source "$(dirname "$0")/utils/init.sh"

# Change to project root
ensure_project_root

# Activate virtual environment
activate_venv

# Run the solve.py script
echo -e "${BLUE}Running Aristotle solver...${NC}"
python "$SOLVE_PY" "$@"
