#!/usr/bin/env python3
"""Turn a marked-up module and a manifest into a Challenge/Solution workspace.

**This file is the placeholder for a dependency, and it is meant to be
deleted.** `leanprover/lean-eval#536` extracts lean-eval's generator core into
`leanprover/lean-eval-generator`, consumed as a pinned dependency by lean-eval
and by this importer, and says in as many words that the Formal Conjectures
importer does not fork the generation logic. Until that repository exists there
is nothing to pin, so this module stands in for it, deliberately holding
everything that is not Formal Conjectures' to own:

- the workspace layout and every file emitted into it;
- which generated module imports which, and where the scope directives are
  restated so the same statement text elaborates in all three files;
- the lakefile, the toolchain file and the Mathlib requirement;
- the fixed Solution adapter that pins the statement;
- the Comparator `config.json` shape.

It reads nothing from this repository except the marked-up module, the
manifest, and the workspace test template it copies. It never resolves a
declaration, reads Lean source, or runs Lean. When `lean-eval-generator` lands,
this file is deleted, `generate` becomes a call into the pinned package, and
`scripts/fc_leaneval_importer.py` does not change.

See `comparator/OWNERSHIP.md` for the line counts either side of that deletion.
"""

import json
import pathlib

from leaneval_interface import slug

ROOT = pathlib.Path(__file__).resolve().parent.parent
# The workspace test template lean-eval's generator supplies for its own
# workspaces; it is vendored here only while this module stands in for it.
TEMPLATE_DIR = ROOT / "comparator" / "templates"

PROOF_SUFFIX = ":= by\n  sorry"


def lakefile(package, mathlib_rev):
    """Mathlib at the target revision, and nothing else.

    The workspace used to require Formal Conjectures too, so that the
    Challenge could import the problem's module. lean-eval vendors its
    problems and cannot fetch that repository at evaluation time, so the
    closure travels in `ChallengeDeps.lean` instead and the require is gone.
    The commit the copy came from is recorded in `manifest.json`, which is
    where a reader should look for it.
    """
    return f"""name = "{package}"
testDriver = "workspace_test"
defaultTargets = ["ChallengeDeps", "Challenge", "Solution", "Submission"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{mathlib_rev}"

[[lean_lib]]
name = "ChallengeDeps"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Submission"

[[lean_exe]]
name = "workspace_test"
root = "WorkspaceTest"
"""


def _readme(package, manifest, target):
    holes_line = (
        "\nFill each definition hole in `Submission.lean` too. Hole answers "
        "also get a\nhuman check, because a hole can be gamed in ways the "
        "comparator cannot see.\nChecking holes needs a comparator built at "
        f"commit `{target.comparator[:8]}`, which\nadded definition "
        "support.\n"
        if manifest.holes
        else ""
    )
    fields = "".join(
        f"- {label}: {' '.join(str(value).split())}\n"
        for label, value in (("Source", manifest.source_url),)
        if value
    )
    return (
        f"# {package}\n\n"
        f"A comparator challenge for `{manifest.theorem}`, generated from\n"
        f"`{manifest.source.path}` in google-deepmind/formal-conjectures.\n\n"
        + fields
        + "\nProve the statement in `Submission.lean`, keeping it as it stands; "
        "put helper\nmodules under `Submission/` if you need them. Do not "
        "modify `Challenge.lean` or\n`Solution.lean`: the trusted statement "
        "lives there, and `Solution.lean` closes it\nwith your `Submission` "
        "theorem, so it fails to compile if the submission proves\nanything "
        "else.\n"
        "\nComparator accepts the workspace only if the statement is proved "
        "under the\naxioms in `config.json`. `sorry` adds `sorryAx`, which is "
        "not permitted, and\nclosing the goal with the imported original "
        "fails the same way, since that is\n`sorry` too. `lake test` runs "
        "comparator, from `PATH` or `COMPARATOR_BIN`.\n"
        "\nIf comparator fails with `incompatible header` on an `.olean`, the "
        "mismatch is\nbetween this workspace's toolchain and the one "
        "`lean4export` was built with,\nnever a problem with the proof: copy "
        "this workspace's `lean-toolchain` into\nyour `lean4export` checkout, "
        "rebuild it, and clear `.lake/build` here.\n"
        + holes_line
        + "\nFetch the Mathlib cache before the first build; a cold build takes "
        "the best\npart of an hour without it:\n\n"
        "    lake exe cache get\n"
        "    lake build\n"
    )


HELPERS = (
    "import Mathlib\n\n"
    "/-! Helper lemmas for the submission go here, or in further modules\n"
    "under `Submission/`, each imported from `Submission.lean`. -/\n\n"
    "namespace Submission\n\nend Submission\n"
)


def generate(marked_up, manifest, target):
    """The workspace files for one problem, as a path-to-content mapping.

    Pure: it writes nothing, and it reads nothing but its two arguments and
    the workspace test template. Putting the result on disk is the caller's.

    The three Lean files carry the same statement text, so what that text
    needs to elaborate has to be restated in each: that is what the module's
    `scope` region is for, and placing it is this side's job. `ChallengeDeps`
    takes the module's dependency region and the `import Mathlib` that makes
    the workspace stand on Mathlib alone; the other three import it.
    """
    package = slug(manifest.id)
    header = marked_up.scope.strip("\n")
    header = header + "\n\n" if header else ""
    holes = marked_up.holes.strip("\n")
    holes = holes + "\n\n" if holes else ""
    statement = marked_up.statement.strip("\n")

    signature = statement.rstrip()
    if signature.endswith(PROOF_SUFFIX):
        signature = signature[: -len(PROOF_SUFFIX)].rstrip()

    challenge = "import ChallengeDeps\n\n" + header + holes + statement + "\n"

    # The participant's file. The statement sits inside `namespace Submission`
    # so nothing here can collide with, or stand in for, the trusted names.
    submission = (
        "import ChallengeDeps\nimport Submission.Helpers\n\n"
        + header
        + "namespace Submission\n\n"
        + holes
        + statement
        + "\n\nend Submission\n"
    )

    # The fixed adapter, lean-eval's shape: it restates the trusted statement
    # and closes it with the Submission theorem, so it fails to compile the
    # moment the submission proves anything else. The participant never edits
    # it, which is what keeps the statement pinned.
    # `@[reducible]`: the Challenge's statement mentions the Solution's copy of
    # the hole and the Submission theorem's type mentions the participant's, so
    # the adapter only typechecks if the unifier unfolds one into the other.
    # Default transparency does, but the one workspace known to have built at
    # LeanEval's toolchain marks it reducible, and there is no reason to be the
    # first to find out whether that mattered.
    delegated = "".join(
        f"@[reducible] noncomputable def {hole.name} : {hole.type} :="
        f"\n  Submission.{hole.name}\n\n"
        for hole in manifest.holes
    )
    solution = (
        "import ChallengeDeps\nimport Submission\n\n"
        + header
        + delegated
        + signature
        + " :=\n  Submission."
        + manifest.theorem
        + "".join(" " + argument for argument in manifest.apply_arguments)
        + "\n"
    )

    config = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [manifest.theorem],
        "permitted_axioms": list(manifest.permitted_axioms),
        "enable_nanoda": False,
    }
    if manifest.holes:
        # Comparator's documented no-hole config carries no such field.
        config["definition_names"] = manifest.hole_names()

    return {
        # The workspace is built where it is going, not where it was made:
        # these are LeanEval's pins, and the manifest carries this repository's
        # beside them.
        "lakefile.toml": lakefile(package, target.mathlib_revision),
        "lean-toolchain": target.lean_toolchain + "\n",
        "README.md": _readme(package, manifest, target),
        "ChallengeDeps.lean": "import Mathlib\n\n"
        + marked_up.dependencies.strip("\n")
        + "\n",
        "Challenge.lean": challenge,
        "Solution.lean": solution,
        "Submission.lean": submission,
        "Submission/Helpers.lean": HELPERS,
        "WorkspaceTest.lean": (TEMPLATE_DIR / "WorkspaceTest.lean").read_text(
            encoding="utf-8"
        ),
        "config.json": json.dumps(config, indent=2) + "\n",
        # The manifest crosses into the workspace unaltered. lean-eval#536
        # requires it to record the FC source commit and declaration id, and
        # this side neither supplies nor edits those.
        "manifest.json": manifest.to_json(),
    }
