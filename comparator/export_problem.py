#!/usr/bin/env python3
"""Repository entry point for the shared native exporter adapter."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "toolkit"))
from conjectures import exporter
exporter.ROOT = Path(__file__).resolve().parents[1]
from conjectures.exporter import *
if __name__ == "__main__":
    main()
