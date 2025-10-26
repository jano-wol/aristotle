#!/bin/bash

# Aristotle Get Solution Script
# Activates virtual environment and runs the get_solution.py script

set -e  # Exit on error

# Source common initialization
source "$(dirname "$0")/utils/init.sh"

# Change to project root
ensure_project_root

# Activate virtual environment
activate_venv

# Run the get_solution.py script
echo -e "${BLUE}Getting solution for Aristotle project...${NC}"
python "$GET_SOLUTION_PY" "$@"
