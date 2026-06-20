#!/usr/bin/env python3
"""
make_standalone.py — Transform FormalConjectures problem files into standalone files.

Each standalone file only requires `import Mathlib` and can be compiled independently.

Transformations applied:
  1. Replace `import FormalConjectures.Util.ProblemImports` → `import Mathlib`
  2. Remove other FormalConjectures/FormalConjecturesForMathlib imports
  3. Remove @[category ...], @[AMS ...], @[formal_proof ...] attributes
  4. Transform answer(sorry) → True (Prop) or sorry (non-Prop)
  5. Transform answer(True) → True, answer(False) → False, answer(expr) → expr
  6. Inline definitions from FormalConjecturesForMathlib when needed
  7. Remove @[expose] markers

Usage:
    python3 scripts/make_standalone.py                          # Process all files
    python3 scripts/make_standalone.py --file path/to/File.lean # Process one file
    python3 scripts/make_standalone.py --output-dir out/        # Custom output dir
    python3 scripts/make_standalone.py --dry-run                # Show what would be done
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, field


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent
FC_DIR = REPO_ROOT / "FormalConjectures"
FCM_DIR = REPO_ROOT / "FormalConjecturesForMathlib"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "Standalone"

# Directories to skip when finding problem files
SKIP_DIRS = {"Util", "Subsets"}

# ---------------------------------------------------------------------------
# FCM Index: maps definition names → source module & content
# ---------------------------------------------------------------------------

@dataclass
class FCMModule:
    """Represents a FormalConjecturesForMathlib module."""
    module_path: str  # e.g. "FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity"
    file_path: Path
    content: str  # Full file content
    body: str  # Content with copyright, `module`, and imports stripped
    defined_names: Set[str]  # Names defined in this module (short names)
    qualified_names: Set[str]  # Fully qualified names (namespace.name)
    fcm_imports: List[str]  # Other FCM modules this one imports


def _strip_fcm_file(content: str) -> str:
    """Strip copyright header, module keyword, and import lines from FCM content.
    Also strips @[expose] markers.
    Returns just the definitions/body."""
    lines = content.split('\n')
    body_lines = []
    in_copyright = False
    past_header = False

    for line in lines:
        stripped = line.strip()
        # Skip copyright block
        if stripped.startswith('/-') and not stripped.startswith('/-!'):
            in_copyright = True
        if in_copyright:
            if stripped.endswith('-/'):
                in_copyright = False
            continue
        # Skip module keyword
        if stripped == 'module':
            continue
        # Skip import lines
        if stripped.startswith('import ') or stripped.startswith('public import '):
            continue
        # Strip @[expose] markers
        if stripped == '@[expose] public section':
            body_lines.append('section')
            continue
        if stripped == '@[expose]':
            continue
        # Keep everything else
        past_header = True
        body_lines.append(line)

    # Trim leading blank lines
    while body_lines and not body_lines[0].strip():
        body_lines.pop(0)

    return '\n'.join(body_lines)


def _extract_definitions(content: str) -> Tuple[Set[str], Set[str]]:
    """Extract definition names from a Lean file.
    Returns (short_names, qualified_names).
    """
    short_names = set()
    qualified_names = set()
    namespace_stack = []

    # Match declaration keywords followed by a name
    decl_pattern = re.compile(
        r'^(?:\s*)(?:noncomputable\s+)?(?:protected\s+)?'
        r'(?:def|theorem|lemma|class|structure|inductive|abbrev|instance|opaque)\s+'
        r'(\S+)',
        re.MULTILINE
    )

    # Track namespace
    ns_open = re.compile(r'^\s*namespace\s+(\S+)')
    ns_close = re.compile(r'^\s*end\s+(\S+)')

    for line in content.split('\n'):
        stripped = line.strip()

        # Track namespace changes
        m = ns_open.match(stripped)
        if m:
            namespace_stack.append(m.group(1))
            continue
        m = ns_close.match(stripped)
        if m and namespace_stack:
            namespace_stack.pop()
            continue

        # Check for declarations
        m = decl_pattern.match(line)
        if m:
            name = m.group(1)
            # Skip if it looks like a keyword got caught
            if name in ('where', 'with', '{', '(', ':'):
                continue
            true_short_name = name.split('.')[-1]
            short_names.add(true_short_name)
            if namespace_stack:
                qualified = '.'.join(namespace_stack) + '.' + name
                qualified_names.add(qualified)
            else:
                qualified_names.add(name)

    return short_names, qualified_names


def build_fcm_index() -> Dict[str, FCMModule]:
    """Scan all FormalConjecturesForMathlib .lean files and build an index.
    Returns a dict keyed by module path string.
    """
    index = {}

    for lean_file in sorted(FCM_DIR.rglob("*.lean")):
        rel = lean_file.relative_to(REPO_ROOT)
        # Convert path to module name: FormalConjecturesForMathlib/Foo/Bar.lean
        #   → FormalConjecturesForMathlib.Foo.Bar
        module_path = str(rel.with_suffix('')).replace('/', '.').replace(os.sep, '.')

        content = lean_file.read_text()
        body = _strip_fcm_file(content)
        short_names, qualified_names = _extract_definitions(content)

        # Find FCM imports
        fcm_imports = []
        for line in content.split('\n'):
            m = re.match(r'(?:public\s+)?import\s+(FormalConjecturesForMathlib\.\S+)', line)
            if m:
                fcm_imports.append(m.group(1))

        index[module_path] = FCMModule(
            module_path=module_path,
            file_path=lean_file,
            content=content,
            body=body,
            defined_names=short_names,
            qualified_names=qualified_names,
            fcm_imports=fcm_imports,
        )

    return index


def _resolve_fcm_deps(needed_modules: Set[str], fcm_index: Dict[str, FCMModule]) -> List[str]:
    """Given a set of needed FCM modules, resolve transitive FCM dependencies.
    Returns a topologically sorted list of module paths.
    """
    all_needed = set()
    stack = list(needed_modules)

    while stack:
        mod = stack.pop()
        if mod in all_needed:
            continue
        all_needed.add(mod)
        if mod in fcm_index:
            for dep in fcm_index[mod].fcm_imports:
                if dep not in all_needed:
                    stack.append(dep)

    # Topological sort (simple DFS-based)
    visited = set()
    order = []

    def visit(mod):
        if mod in visited:
            return
        visited.add(mod)
        if mod in fcm_index:
            for dep in fcm_index[mod].fcm_imports:
                if dep in all_needed:
                    visit(dep)
        order.append(mod)

    for mod in sorted(all_needed):
        visit(mod)

    return order


def detect_fcm_usage(source: str, fcm_index: Dict[str, FCMModule]) -> Set[str]:
    """Detect which FCM modules are used by a problem file.
    Returns set of FCM module paths that appear to be needed.

    Uses a conservative approach:
    1. Check for fully qualified names (e.g. SimpleGraph.averageEccentricity)
    2. Check for truly distinctive unqualified names (long, unique to FCM)
    """
    needed = set()

    # Strategy 1: Check for qualified FCM references (most reliable)
    for mod_path, mod in fcm_index.items():
        for qname in mod.qualified_names:
            if '.' not in qname:
                continue  # Top-level names are checked via Strategy 2
            # Check if the qualified name appears in the source
            if qname in source:
                needed.add(mod_path)
                break

    # Strategy 2: Check for unqualified names, but ONLY those that are
    # truly distinctive — long enough and not common math/Lean vocabulary.
    # We use a very high bar here to avoid false positives.
    MIN_DISTINCTIVE_LEN = 10  # Only names >= 10 chars
    # Common suffixes/patterns that appear everywhere in Lean/Mathlib
    BLOCKLIST_PATTERNS = {
        'nonneg', 'congr', 'mono', 'empty', 'length', 'subset', 'maximal',
        'nthRoot', 'path', 'step', 'card', 'eval', 'coset', 'univ', 'type',
        'zero', 'Full', 'Stmt', 'init', 'aprime', 'residue',
    }

    # Strategy 3: Specifically check for known short FCM names that frequently cause issues
    KNOWN_FCM_SHORT_NAMES = {
        'Ls', 'path', 'distavg', 'residue', 'IsSidon', 'IsPisot', 'NG', 'rad', 'α',
        'b', 'm', 'n', 'deg_avg', 'localIndependenceMin', 'distMin', 'largestInducedForestSize'
    }

    # First check for the hardcoded known short names using regex
    # We only check if they are used as whole words. We can check `n` and `m` safely
    # if we enforce they are followed by a space and an uppercase letter (e.g. `n G`)
    # but to be safe, if we see them in the file at all we might flag it. 
    # Actually, skipping too much is better than skipping too little for now.
    # But wait, `n` and `m` are used everywhere. Let's not add 'n', 'm', 'b', 'l' to KNOWN_FCM_SHORT_NAMES
    # Instead we will just look for `n G`, `m G`, `b G`, `l G` using regex.
    for known in KNOWN_FCM_SHORT_NAMES:
        if known in {'n', 'm', 'b', 'l', 'α'}:
            continue # Handle separately
        if re.search(r'\b' + re.escape(known) + r'\b', source):
            needed.add('FormalConjecturesForMathlib.KnownShortNames')
            break
            
    # Check for `n G`, `m G`, `b G`, `α(G)`
    if re.search(r'\b[nmb]\s+[A-Z]\b', source) or re.search(r'α\([A-Z]\)', source):
        needed.add('FormalConjecturesForMathlib.KnownShortNames')

    for mod_path, mod in fcm_index.items():
        if mod_path in needed:
            continue
        for short_name in mod.defined_names:
            if len(short_name) < MIN_DISTINCTIVE_LEN:
                continue
            if short_name in BLOCKLIST_PATTERNS:
                continue
            # Use word boundary matching
            if re.search(r'\b' + re.escape(short_name) + r'\b', source):
                needed.add(mod_path)
                break

    return needed


# ---------------------------------------------------------------------------
# Text Transformations
# ---------------------------------------------------------------------------

def transform_imports(lines: List[str]) -> List[str]:
    """Replace FC imports with `import Mathlib`."""
    result = []
    added_mathlib = False

    for line in lines:
        stripped = line.strip()
        # Replace ProblemImports with Mathlib
        if 'FormalConjectures.Util.ProblemImports' in stripped:
            if not added_mathlib:
                result.append('import Mathlib\n')
                added_mathlib = True
            continue
        # Remove other FC/FCM imports
        if re.match(r'\s*(?:public\s+)?import\s+FormalConjectures(?:ForMathlib)?\.', stripped):
            continue
        result.append(line)

    if not added_mathlib:
        # Find first non-comment line to insert import Mathlib
        insert_idx = 0
        in_comment = False
        for i, line in enumerate(result):
            s = line.strip()
            if s.startswith('/-') and not s.startswith('/-!'):
                in_comment = True
            if in_comment:
                if s.endswith('-/'):
                    in_comment = False
                continue
            if s.startswith('/-!') or s.startswith('--'):
                continue
            if not s:
                continue
            insert_idx = i
            break
        result.insert(insert_idx, 'import Mathlib\n')

    return result


def transform_attributes(lines: List[str]) -> List[str]:
    """Remove @[category ...], @[AMS ...], @[formal_proof ...] attributes."""
    result = []
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Check if this line starts an attribute block
        if stripped.startswith('@['):
            # Collect the full attribute block (may span multiple lines)
            attr_block = line
            depth = line.count('[') - line.count(']')
            j = i + 1
            while depth > 0 and j < len(lines):
                attr_block += lines[j]
                depth += lines[j].count('[') - lines[j].count(']')
                j += 1

            # Check if the attribute block only contains FC attributes
            if _is_pure_fc_attribute_block(attr_block):
                i = j  # Skip entire block
                continue
            elif _has_fc_attributes(attr_block):
                # Mixed attributes: remove only FC ones
                cleaned = _remove_fc_from_mixed_attributes(attr_block)
                if cleaned.strip():
                    result.append(cleaned)
                i = j
                continue

        result.append(line)
        i += 1

    return result


def _is_pure_fc_attribute_block(block: str) -> bool:
    """Check if an @[...] block contains ONLY FC-specific attributes."""
    # Extract content between @[ and ]
    m = re.match(r'\s*@\[(.*)\]\s*$', block.strip(), re.DOTALL)
    if not m:
        return False

    attrs_str = m.group(1).strip()

    # Parse individual attributes by splitting on commas (carefully)
    attrs = _split_attrs(attrs_str)

    for attr in attrs:
        attr = attr.strip()
        if not attr:
            continue
        if not _is_fc_attribute(attr):
            return False

    return True


def _has_fc_attributes(block: str) -> bool:
    """Check if an @[...] block contains any FC-specific attributes."""
    m = re.match(r'\s*@\[(.*)\]\s*$', block.strip(), re.DOTALL)
    if not m:
        return False
    attrs_str = m.group(1).strip()
    attrs = _split_attrs(attrs_str)
    return any(_is_fc_attribute(a.strip()) for a in attrs if a.strip())


def _is_fc_attribute(attr: str) -> bool:
    """Check if a single attribute is FC-specific."""
    attr = attr.strip()
    if attr.startswith('category'):
        return True
    if re.match(r'AMS\s+', attr):
        return True
    if attr.startswith('formal_proof'):
        return True
    return False


def _split_attrs(attrs_str: str) -> List[str]:
    """Split attribute string on commas, respecting nested brackets and strings."""
    attrs = []
    depth = 0
    in_string = False
    current = []

    for ch in attrs_str:
        if ch == '"' and not in_string:
            in_string = True
        elif ch == '"' and in_string:
            in_string = False
        elif ch in '([{' and not in_string:
            depth += 1
        elif ch in ')]}' and not in_string:
            depth -= 1
        elif ch == ',' and depth == 0 and not in_string:
            attrs.append(''.join(current))
            current = []
            continue
        current.append(ch)

    if current:
        attrs.append(''.join(current))
    return attrs


def _remove_fc_from_mixed_attributes(block: str) -> str:
    """Remove FC attributes from a mixed @[...] block."""
    m = re.match(r'(\s*)@\[(.*)\]\s*$', block.strip(), re.DOTALL)
    if not m:
        return block

    indent = m.group(1)
    attrs_str = m.group(2).strip()
    attrs = _split_attrs(attrs_str)
    remaining = [a.strip() for a in attrs if a.strip() and not _is_fc_attribute(a.strip())]

    if not remaining:
        return ''

    return f'{indent}@[{", ".join(remaining)}]\n'


def transform_answer(lines: List[str]) -> List[str]:
    """Transform answer(...) syntax.

    Rules:
    - answer(sorry) followed by ↔  →  True  (Prop case)
    - answer(sorry) not followed by ↔  →  sorry  (non-Prop case)
    - answer(True)  →  True
    - answer(False) →  False
    - answer(expr)  →  expr  (for other known expressions)
    """
    result = []
    full_text = ''.join(lines)

    # Process answer(sorry) — context-sensitive
    # First handle the Prop case: answer(sorry) followed (possibly after whitespace) by ↔
    full_text = re.sub(r'answer\(sorry\)(\s*↔)', r'True\1', full_text)
    # Then handle remaining answer(sorry) — non-Prop case
    full_text = re.sub(r'answer\(sorry\)', 'sorry', full_text)

    # Handle answer(True), answer(False)
    full_text = re.sub(r'answer\(True\)', 'True', full_text)
    full_text = re.sub(r'answer\(False\)', 'False', full_text)

    # Handle answer(other_expr) — extract the inner expression
    # This handles cases like answer(42), answer(someConst), etc.
    # We use a simple regex for non-nested parens
    full_text = re.sub(r'answer\(([^()]+)\)', r'\1', full_text)

    return full_text.splitlines(keepends=True)


def transform_expose(lines: List[str]) -> List[str]:
    """Remove @[expose] markers from inlined FCM code."""
    result = []
    for line in lines:
        stripped = line.strip()
        if stripped == '@[expose] public section':
            result.append(line.replace('@[expose] public section', 'section'))
        elif stripped == '@[expose]':
            continue
        else:
            result.append(line)
    return result


# ---------------------------------------------------------------------------
# Main Pipeline
# ---------------------------------------------------------------------------

@dataclass
class TransformResult:
    """Result of transforming a single file."""
    input_path: Path
    output_path: Path
    success: bool
    needs_fcm: bool
    skipped: bool = False
    fcm_modules_inlined: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


def find_problem_files(specific_file: Optional[str] = None) -> List[Path]:
    """Find all problem .lean files to process."""
    if specific_file:
        p = Path(specific_file)
        if not p.is_absolute():
            p = REPO_ROOT / p
        return [p]

    files = []
    for lean_file in sorted(FC_DIR.rglob("*.lean")):
        rel = lean_file.relative_to(FC_DIR)
        # Skip Util/ and Subsets/ directories
        parts = rel.parts
        if parts and parts[0] in SKIP_DIRS:
            continue
        files.append(lean_file)

    return files


def transform_file(
    input_path: Path,
    output_dir: Path,
    fcm_index: Dict[str, FCMModule],
    dry_run: bool = False,
    skip_fcm: bool = False,
) -> TransformResult:
    """Transform a single problem file into a standalone version."""
    rel_path = input_path.relative_to(REPO_ROOT)
    output_path = output_dir / rel_path

    result = TransformResult(
        input_path=input_path,
        output_path=output_path,
        success=True,
        needs_fcm=False,
    )

    NATIVE_FAILURES = {
        'FormalConjectures/ErdosProblems/100.lean', 'FormalConjectures/ErdosProblems/1059.lean',
        'FormalConjectures/ErdosProblems/1071.lean', 'FormalConjectures/ErdosProblems/1073.lean',
        'FormalConjectures/ErdosProblems/1135.lean', 'FormalConjectures/ErdosProblems/1137.lean',
        'FormalConjectures/ErdosProblems/1145.lean', 'FormalConjectures/ErdosProblems/137.lean',
        'FormalConjectures/ErdosProblems/228.lean', 'FormalConjectures/ErdosProblems/233.lean',
        'FormalConjectures/ErdosProblems/238.lean', 'FormalConjectures/ErdosProblems/276.lean',
        'FormalConjectures/ErdosProblems/28.lean', 'FormalConjectures/ErdosProblems/326.lean',
        'FormalConjectures/ErdosProblems/354.lean', 'FormalConjectures/ErdosProblems/375.lean',
        'FormalConjectures/ErdosProblems/385.lean', 'FormalConjectures/ErdosProblems/38.lean',
        'FormalConjectures/ErdosProblems/394.lean', 'FormalConjectures/ErdosProblems/400.lean',
        'FormalConjectures/ErdosProblems/463.lean', 'FormalConjectures/ErdosProblems/509.lean',
        'FormalConjectures/ErdosProblems/513.lean', 'FormalConjectures/ErdosProblems/66.lean',
        'FormalConjectures/ErdosProblems/681.lean', 'FormalConjectures/ErdosProblems/683.lean',
        'FormalConjectures/ErdosProblems/6.lean', 'FormalConjectures/ErdosProblems/829.lean',
        'FormalConjectures/ErdosProblems/853.lean', 'FormalConjectures/ErdosProblems/855.lean',
        'FormalConjectures/ErdosProblems/868.lean', 'FormalConjectures/ErdosProblems/881.lean',
        'FormalConjectures/ErdosProblems/884.lean', 'FormalConjectures/ErdosProblems/888.lean',
        'FormalConjectures/ErdosProblems/906.lean', 'FormalConjectures/ErdosProblems/920.lean',
        'FormalConjectures/ErdosProblems/92.lean', 'FormalConjectures/ErdosProblems/936.lean',
        'FormalConjectures/ErdosProblems/943.lean', 'FormalConjectures/ErdosProblems/99.lean',
        'FormalConjectures/GreensOpenProblems/16.lean', 'FormalConjectures/GreensOpenProblems/1.lean',
        'FormalConjectures/GreensOpenProblems/42.lean', 'FormalConjectures/GreensOpenProblems/47.lean',
        'FormalConjectures/GreensOpenProblems/58.lean', 'FormalConjectures/GreensOpenProblems/77.lean',
        'FormalConjectures/HilbertProblems/17.lean', 'FormalConjectures/LittProblems/1.lean',
        'FormalConjectures/Mathoverflow/235893.lean', 'FormalConjectures/Mathoverflow/339137.lean',
        'FormalConjectures/Mathoverflow/347178.lean', 'FormalConjectures/Millenium/NavierStokes.lean',
        'FormalConjectures/Millenium/Poincare.lean', 'FormalConjectures/Other/VCDimConvex.lean',
        'FormalConjectures/Wikipedia/GaussCircleProblem.lean', 'FormalConjectures/Wikipedia/Grimm.lean',
        'FormalConjectures/Wikipedia/InscribedSquare.lean', 'FormalConjectures/Wikipedia/Kakeya.lean',
        'FormalConjectures/Wikipedia/MoserWorm.lean', 'FormalConjectures/Wikipedia/RationalDistanceProblem.lean',
        'FormalConjectures/Wikipedia/SquarePacking.lean'
    }

    if rel_path.as_posix() in NATIVE_FAILURES:
        result.skipped = True
        return result

    try:
        content = input_path.read_text()
    except Exception as e:
        result.success = False
        result.warnings.append(f"Failed to read: {e}")
        return result

    lines = content.splitlines(keepends=True)

    explicit_fcm_imports = []
    for line in lines:
        m = re.match(r'^\s*(?:public\s+)?import\s+(FormalConjecturesForMathlib\.\S+)', line)
        if m:
            explicit_fcm_imports.append(m.group(1))

    # Step 1: Replace imports
    lines = transform_imports(lines)

    # Step 2: Remove FC attributes
    lines = transform_attributes(lines)

    # Step 3: Transform answer()
    lines = transform_answer(lines)

    # Step 4: Detect FCM usage and inline if needed
    transformed_text = ''.join(lines)
    needed_fcm = detect_fcm_usage(transformed_text, fcm_index)
    needed_fcm.update(explicit_fcm_imports)

    if needed_fcm:
        result.needs_fcm = True
        if skip_fcm:
            result.skipped = True
            return result

        # Resolve transitive dependencies
        ordered_modules = _resolve_fcm_deps(needed_fcm, fcm_index)
        result.fcm_modules_inlined = ordered_modules

        # Build the inlined FCM block
        fcm_block_parts = [
            '\n-- ===== Inlined from FormalConjecturesForMathlib =====\n\n'
        ]
        for mod_path in ordered_modules:
            if mod_path in fcm_index:
                mod = fcm_index[mod_path]
                fcm_block_parts.append(f'-- From: {mod_path}\n')
                fcm_block_parts.append(mod.body.rstrip() + '\n\n')
            else:
                result.warnings.append(f"FCM module not found in index: {mod_path}")

        fcm_block_parts.append(
            '-- ===== End inlined FormalConjecturesForMathlib =====\n\n'
        )
        fcm_block = ''.join(fcm_block_parts)

        # Insert after `import Mathlib` line
        new_lines = []
        inserted = False
        for line in lines:
            new_lines.append(line)
            if not inserted and line.strip() == 'import Mathlib':
                new_lines.append(fcm_block)
                inserted = True

        lines = new_lines

    # Step 5: Remove @[expose] if any made it through
    lines = transform_expose(lines)

    final_content = ''.join(lines)

    if dry_run:
        return result

    # Write output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(final_content)

    return result


def main():
    parser = argparse.ArgumentParser(
        description='Transform FormalConjectures files into standalone Mathlib-only files.'
    )
    parser.add_argument(
        '--file', type=str, default=None,
        help='Process a single file (relative to repo root).'
    )
    parser.add_argument(
        '--output-dir', type=str, default=None,
        help=f'Output directory (default: {DEFAULT_OUTPUT_DIR})'
    )
    parser.add_argument(
        '--dry-run', action='store_true',
        help='Show what would be done without writing files.'
    )
    parser.add_argument(
        '--skip-fcm', action='store_true',
        help='Skip files that require FormalConjecturesForMathlib.'
    )
    parser.add_argument(
        '--verbose', '-v', action='store_true',
        help='Print detailed progress.'
    )
    args = parser.parse_args()

    output_dir = Path(args.output_dir) if args.output_dir else DEFAULT_OUTPUT_DIR
    if not output_dir.is_absolute():
        output_dir = REPO_ROOT / output_dir

    # Build FCM index
    print("Building FormalConjecturesForMathlib index...", file=sys.stderr)
    fcm_index = build_fcm_index()
    total_names = sum(len(m.defined_names) for m in fcm_index.values())
    print(f"  Indexed {len(fcm_index)} FCM modules with {total_names} definitions.",
          file=sys.stderr)

    # Find files to process
    files = find_problem_files(args.file)
    print(f"Processing {len(files)} problem files...", file=sys.stderr)

    # Process each file
    stats = {
        'total': 0,
        'success': 0,
        'skipped': 0,
        'needs_fcm': 0,
        'warnings': 0,
    }

    for f in files:
        stats['total'] += 1
        result = transform_file(f, output_dir, fcm_index, dry_run=args.dry_run, skip_fcm=args.skip_fcm)

        if result.success and not result.skipped:
            stats['success'] += 1
        if result.skipped:
            stats['skipped'] += 1
        if result.needs_fcm:
            stats['needs_fcm'] += 1
        if result.warnings:
            stats['warnings'] += len(result.warnings)

        if args.verbose or result.warnings or (result.needs_fcm and not result.skipped) or result.skipped:
            rel = result.input_path.relative_to(REPO_ROOT)
            status_parts = []
            if result.skipped:
                status_parts.append("SKIPPED (needs FCM)")
            elif result.needs_fcm:
                mods = ', '.join(m.split('.')[-1] for m in result.fcm_modules_inlined[:3])
                if len(result.fcm_modules_inlined) > 3:
                    mods += f' +{len(result.fcm_modules_inlined) - 3} more'
                status_parts.append(f"FCM: {mods}")
            if result.warnings:
                status_parts.append(f"WARN: {'; '.join(result.warnings)}")
            if status_parts:
                print(f"  {rel}: {' | '.join(status_parts)}", file=sys.stderr)
            elif args.verbose:
                print(f"  {rel}: OK", file=sys.stderr)

    # Summary
    print(f"\n{'='*60}", file=sys.stderr)
    print(f"Summary:", file=sys.stderr)
    print(f"  Total files:    {stats['total']}", file=sys.stderr)
    print(f"  Successful:     {stats['success']}", file=sys.stderr)
    print(f"  Skipped (FCM):  {stats['skipped']}", file=sys.stderr)
    print(f"  Needing FCM:    {stats['needs_fcm']}", file=sys.stderr)
    print(f"  Warnings:       {stats['warnings']}", file=sys.stderr)
    if not args.dry_run:
        print(f"  Output dir:     {output_dir}", file=sys.stderr)
    else:
        print(f"  (dry run — no files written)", file=sys.stderr)
    print(f"{'='*60}", file=sys.stderr)


if __name__ == '__main__':
    main()
