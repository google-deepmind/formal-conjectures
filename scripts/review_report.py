#!/usr/bin/env python3
"""Compatibility entry point for the shared report contract."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "toolkit"))
from conjectures.report import *
if __name__ == "__main__":
    main()
