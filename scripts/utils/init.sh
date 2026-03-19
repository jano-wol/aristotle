#!/bin/bash
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LAKE_DIR="$PROJECT_ROOT/.lake"

export GREEN='\033[0;32m'
export BLUE='\033[0;34m'
export YELLOW='\033[1;33m'
export RED='\033[0;31m'
export NC='\033[0m'

ensure_project_root() {
    cd "$PROJECT_ROOT"
}
