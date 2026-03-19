#!/bin/bash
set -e

source "$(dirname "$0")/utils/init.sh"
ensure_project_root

echo "================================================"
echo "Aristotle Project Cleanup"
echo "================================================"
echo ""
echo "This will remove:"
echo "  - Lean dependencies (.lake/)"
echo ""
read -p "Are you sure? (y/N): " -n 1 -r
echo ""

if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Cleanup cancelled."
    exit 0
fi

echo ""

if [ -d "$LAKE_DIR" ]; then
    echo -e "${BLUE}Removing Lean dependencies...${NC}"
    rm -rf "$LAKE_DIR"
    echo -e "${GREEN}✓ .lake removed${NC}"
else
    echo -e "${YELLOW}.lake directory not found, skipping${NC}"
fi

echo ""
echo "================================================"
echo -e "${GREEN}Cleanup Complete!${NC}"
echo "================================================"
echo ""
echo "Run ./scripts/configure.sh to set up again."
echo ""
