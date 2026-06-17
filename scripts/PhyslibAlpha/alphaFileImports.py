#!/usr/bin/env python3

import os
import re
from pathlib import Path

def main():
    # Get the current working directory
    script_dir = Path.cwd()
    physlib_alpha_dir = script_dir / "PhyslibAlpha"
    physlib_alpha_lean = script_dir / "PhyslibAlpha.lean"

    # Check if PhyslibAlpha directory exists
    if not physlib_alpha_dir.exists():
        print(f"Error: {physlib_alpha_dir} directory not found")
        return False

    # Check if PhyslibAlpha.lean file exists
    if not physlib_alpha_lean.exists():
        print(f"Error: {physlib_alpha_lean} file not found")
        return False

    # Get all .lean files in PhyslibAlpha directory
    lean_files = sorted([f.name for f in physlib_alpha_dir.glob("*.lean")])

    if not lean_files:
        print(f"No .lean files found in {physlib_alpha_dir}")
        return True

    # Read PhyslibAlpha.lean and extract imports
    with open(physlib_alpha_lean, 'r') as f:
        content = f.read()

    # Extract import statements (looking for "import PhyslibAlpha.<module>" where <module> is a direct file, not nested)
    import_pattern = r'import\s+PhyslibAlpha\.(\w+)(?:\s|$)'
    imports = set(re.findall(import_pattern, content))
    imported_files = {f"{name}.lean" for name in imports}

    # Check for missing imports
    missing = set(lean_files) - imported_files

    if missing:
        print(f"Error: The following .lean files are not imported in {physlib_alpha_lean}:")
        for file in sorted(missing):
            module_name = file.replace(".lean", "")
            print(f"  - public import PhyslibAlpha.{module_name}")
        return False
    else:
        print(f"✓ All {len(lean_files)} .lean files in {physlib_alpha_dir} are imported in {physlib_alpha_lean}")
        return True

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
