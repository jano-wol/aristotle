#!/bin/bash

# Aristotle Project Setup Script
# Sets up Python virtual environment and Lean dependencies
# Can be run multiple times safely (idempotent)

set -e  # Exit on error

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$PROJECT_DIR"

echo "================================================"
echo "Aristotle Project Setup"
echo "================================================"
echo ""

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# ============================================
# 1. Check Prerequisites
# ============================================

echo -e "${BLUE}Checking prerequisites...${NC}"

if ! command -v python3 &> /dev/null; then
    echo "Error: python3 is not installed. Please install Python 3."
    exit 1
fi

if ! command -v elan &> /dev/null; then
    echo "Error: elan (Lean version manager) is not installed."
    echo "Please install it from: https://github.com/leanprover/elan"
    echo "Run: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    exit 1
fi

if ! command -v lake &> /dev/null; then
    echo "Error: lake (Lean build tool) is not found."
    echo "Make sure elan is properly installed and in your PATH."
    exit 1
fi

echo -e "${GREEN}✓ All prerequisites found${NC}"
echo ""

# ============================================
# 2. Setup Python Virtual Environment
# ============================================

if [ -d "venv" ]; then
    echo -e "${YELLOW}Python virtual environment already exists${NC}"
else
    echo -e "${BLUE}Creating Python virtual environment...${NC}"
    python3 -m venv venv
    echo -e "${GREEN}✓ Python virtual environment created${NC}"
fi

echo -e "${BLUE}Installing Python dependencies...${NC}"
source venv/bin/activate
pip install --upgrade pip -q
pip install -r requirements.txt
echo -e "${GREEN}✓ Python dependencies installed${NC}"
echo ""

# ============================================
# 3. Setup Lean Dependencies
# ============================================

if [ -d ".lake" ]; then
    echo -e "${YELLOW}Lean .lake directory already exists${NC}"
    echo -e "${BLUE}Verifying Lean dependencies...${NC}"
    # Just verify, don't rebuild unless necessary
    lake build --no-build > /dev/null 2>&1 || {
        echo -e "${YELLOW}Dependencies need updating...${NC}"
        lake update
    }
else
    echo -e "${BLUE}Setting up Lean dependencies...${NC}"
    echo "This will download ~5.5GB of Mathlib and may take several minutes..."
    lake update
    echo -e "${GREEN}✓ Lean dependencies installed${NC}"
fi

echo ""

# ============================================
# 4. Verify Installation
# ============================================

echo -e "${BLUE}Verifying installation...${NC}"

# Check Lean toolchain
EXPECTED_LEAN_VERSION=$(cat lean-toolchain | tr -d '\n')
ACTUAL_LEAN_VERSION=$(lake env lean --version | head -n 1 | grep -o 'v[0-9.a-z-]*' || echo "unknown")

echo "  Lean toolchain: $EXPECTED_LEAN_VERSION"
if lake build --no-build > /dev/null 2>&1; then
    echo -e "  Lean workspace: ${GREEN}OK${NC}"
else
    echo -e "  Lean workspace: ${YELLOW}Needs configuration${NC}"
fi

# Check Python environment
if python -c "import aristotlelib" 2> /dev/null; then
    echo -e "  Python aristotlelib: ${GREEN}OK${NC}"
else
    echo -e "  Python aristotlelib: ${YELLOW}WARNING - import failed${NC}"
fi

echo ""
echo "================================================"
echo -e "${GREEN}Setup Complete!${NC}"
echo "================================================"
echo ""
echo "To activate the Python environment:"
echo "  source venv/bin/activate"
echo ""
echo "To build Lean projects:"
echo "  lake build"
echo ""
echo "Project structure:"
echo "  - projects/     : Your Lean theorem proving projects"
echo "  - prove.py      : Aristotle prover script"
echo "  - status.py     : Status checking script"
echo ""
