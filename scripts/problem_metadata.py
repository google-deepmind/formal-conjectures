"""Repository entry point for shared native metadata readers."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'toolkit'))
from conjectures.metadata import metadata_rows, unconditional_proof, proof_links
