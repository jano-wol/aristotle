#!/bin/bash

# Aristotle Clear Script
# Removes all generated/downloaded files: venv, .lake, and API key

set -e  # Exit on error

# Source common initialization
source "$(dirname "$0")/utils/init.sh"

# Change to project root
ensure_project_root

echo "================================================"
echo "Aristotle Project Cleanup"
echo "================================================"
echo ""
echo "This will remove:"
echo "  - Python virtual environment (venv/)"
echo "  - Lean dependencies (.lake/)"
echo "  - API key file (scripts/utils/aristotle_api_key.txt)"
echo ""
read -p "Are you sure? (y/N): " -n 1 -r
echo ""

if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Cleanup cancelled."
    exit 0
fi

echo ""

# Remove venv
if [ -d "$VENV_DIR" ]; then
    echo -e "${BLUE}Removing Python virtual environment...${NC}"
    rm -rf "$VENV_DIR"
    echo -e "${GREEN}✓ venv removed${NC}"
else
    echo -e "${YELLOW}venv directory not found, skipping${NC}"
fi

# Remove .lake
if [ -d "$LAKE_DIR" ]; then
    echo -e "${BLUE}Removing Lean dependencies...${NC}"
    rm -rf "$LAKE_DIR"
    echo -e "${GREEN}✓ .lake removed${NC}"
else
    echo -e "${YELLOW}.lake directory not found, skipping${NC}"
fi

# Remove API key
API_KEY_FILE="$UTILS_DIR/aristotle_api_key.txt"
if [ -f "$API_KEY_FILE" ]; then
    echo -e "${BLUE}Removing API key file...${NC}"
    rm -f "$API_KEY_FILE"
    echo -e "${GREEN}✓ API key removed${NC}"
else
    echo -e "${YELLOW}API key file not found, skipping${NC}"
fi

echo ""
echo "================================================"
echo -e "${GREEN}Cleanup Complete!${NC}"
echo "================================================"
echo ""
echo "Run ./scripts/configure.sh to set up again."
echo ""
