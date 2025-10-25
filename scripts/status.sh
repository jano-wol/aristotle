#!/bin/bash

# Aristotle Status Script
# Activates virtual environment and runs the status.py script

set -e  # Exit on error

# Source common initialization
source "$(dirname "$0")/utils/init.sh"

# Change to project root
ensure_project_root

# Activate virtual environment
activate_venv

# Run the status.py script
echo -e "${BLUE}Checking Aristotle project status...${NC}"
python "$STATUS_PY" "$@"
