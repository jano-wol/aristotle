#!/bin/bash
# Common initialization for Aristotle project scripts
# This file should be sourced by other scripts using: source "$(dirname "$0")/utils/init.sh"

# Determine the project root directory (parent of scripts/)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Define important directories
SCRIPTS_DIR="$PROJECT_ROOT/scripts"
UTILS_DIR="$SCRIPTS_DIR/utils"
PROBLEMS_DIR="$PROJECT_ROOT/problems"
SOLUTIONS_DIR="$PROJECT_ROOT/solutions"
VENV_DIR="$PROJECT_ROOT/venv"
LAKE_DIR="$PROJECT_ROOT/.lake"

# Define Python script paths
PROVE_PY="$UTILS_DIR/prove.py"
STATUS_PY="$UTILS_DIR/status.py"

# Colors for output
export GREEN='\033[0;32m'
export BLUE='\033[0;34m'
export YELLOW='\033[1;33m'
export RED='\033[0;31m'
export NC='\033[0m' # No Color

# Helper function to activate virtual environment
activate_venv() {
    if [ ! -d "$VENV_DIR" ]; then
        echo -e "${RED}Error: Virtual environment not found at $VENV_DIR${NC}"
        echo "Please run configure.sh first."
        exit 1
    fi
    source "$VENV_DIR/bin/activate"
}

# Helper function to check if we're in the project root
ensure_project_root() {
    cd "$PROJECT_ROOT"
}
