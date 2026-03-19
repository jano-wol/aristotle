#!/bin/bash
set -e

source "$(dirname "$0")/utils/init.sh"
ensure_project_root

echo "================================================"
echo "Aristotle Project Setup"
echo "================================================"
echo ""

echo -e "${BLUE}Checking prerequisites...${NC}"

if ! command -v elan &> /dev/null; then
    echo "Error: elan (Lean version manager) is not installed."
    echo "Install: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    exit 1
fi

if ! command -v lake &> /dev/null; then
    echo "Error: lake (Lean build tool) is not found."
    exit 1
fi

echo -e "${GREEN}✓ All prerequisites found${NC}"
echo ""

if [ -d "$LAKE_DIR" ]; then
    echo -e "${YELLOW}Lean .lake directory already exists${NC}"
    echo -e "${BLUE}Verifying Lean dependencies...${NC}"
    lake build --no-build > /dev/null 2>&1 || {
        echo -e "${YELLOW}Dependencies need updating...${NC}"
        lake update
    }
else
    echo -e "${BLUE}Setting up Lean dependencies...${NC}"
    echo "This will download ~6GB of Mathlib and may take several minutes..."
    lake update
    echo -e "${GREEN}✓ Lean dependencies installed${NC}"
fi

echo ""

echo -e "${BLUE}Verifying installation...${NC}"

EXPECTED_LEAN_VERSION=$(cat lean-toolchain | tr -d '\n')
echo "  Lean toolchain: $EXPECTED_LEAN_VERSION"
if lake build --no-build > /dev/null 2>&1; then
    echo -e "  Lean workspace: ${GREEN}OK${NC}"
else
    echo -e "  Lean workspace: ${YELLOW}Needs configuration${NC}"
fi

echo ""
echo "================================================"
echo -e "${GREEN}Setup Complete!${NC}"
echo "================================================"
