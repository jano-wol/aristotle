"""Utility functions for Aristotle project."""

import sys
from pathlib import Path


def load_api_key():
    """Load Aristotle API key from aristotle_api_key.txt"""
    api_key_file = Path(__file__).parent / "aristotle_api_key.txt"

    if not api_key_file.exists():
        print("Error: aristotle_api_key.txt not found!", file=sys.stderr)
        print("", file=sys.stderr)
        print("Please create the file with your API key:", file=sys.stderr)
        print(f"  echo 'your_key_here' > {api_key_file}", file=sys.stderr)
        print("", file=sys.stderr)
        sys.exit(1)

    api_key = api_key_file.read_text().strip()

    if not api_key:
        print("Error: aristotle_api_key.txt is empty!", file=sys.stderr)
        sys.exit(1)

    return api_key
