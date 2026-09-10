# Catalog and rendering contract

Lean declarations and their attributes are the source of truth. The native
catalog is their public, versioned representation. The website, CLI, status
checker, and proof-link checker consume that representation. Verso renders the
same source; HTML is never parsed to recover mathematical metadata.

## Static endpoints

Paths are relative to the deployed site's base URL.

| Path | Purpose | Consumer |
|---|---|---|
| `data/catalog-manifest.json` | Current snapshot's SHA-256, byte length, count, provenance, and schema link | All catalog readers |
| `data/conjectures.json` | Native schema-2 problems and module documentation | Website, CLI, checks |
| `data/schemas/catalog-v2.schema.json` | Full publication profile | Validators and client authors |
| `data/schemas/catalog-manifest-v1.schema.json` | Descriptor contract | Validators and client authors |
| `data/rendered/<catalog-sha256>/<module-file>.json` | One module's Verso documentation, code, referenced hovers, and contributors | Problem pages |
| `data/rendered/<catalog-sha256>/modules.json` | Complete Verso source-page navigation, including utility libraries | Full and preview builds |
| `data/schemas/website-modules-v1.schema.json` | Source-page index contract | Website tooling |
| `data/schemas/website-rendering-v1.schema.json` | Rendering contract | Website tooling |
| `data/evidence.json` | Validated contribution evidence and availability | Website |
| `data/work.json` | Observed PR context and availability | Website |
| `src/` | Full Verso annotated source pages | Readers following source links |

`<module-file>` is the source module's file path with `.json` replacing `.lean`.
Decode Lean quoted name components before mapping them to file paths; URL-encode
each path component. For example, `FormalConjectures.ErdosProblems.«92»` maps to
`FormalConjectures/ErdosProblems/92.json`.

This is a static JSON interface on GitHub Pages. It needs no API server, database,
authentication, or additional build system. Search runs locally over the catalog.
The schemas use [JSON Schema Draft 2020-12](https://json-schema.org/draft/2020-12/schema).
This interface does not claim JSON:API compliance: its existing native contract
already represents FC's data, without a resource-envelope migration.

## One snapshot

1. Fetch the manifest.
2. Fetch `conjectures.json` and check the raw byte length and SHA-256 before using it.
3. Validate the complete publication profile, problem count, and matching provenance.
4. For rich rendering, request the module under that catalog digest and check its
   `catalog_sha256` and exact `module` fields.

The CLI caches validated snapshots. The browser shares one in-flight catalog
request and caches module requests for the page session. JSON is compact UTF-8;
transport compression is the host's responsibility. The manifest describes the
uncompressed entity bytes, not compressed transfer bytes. No separately maintained
compressed catalog or search database is published.

A deployment change can interrupt a download. Report that mismatch and retry a
fresh manifest; never combine snapshots or silently substitute older data. A digest
path prevents an older page from reading a newer module rendering. GitHub Pages
does not promise to retain old deployments, so a missing rendering stays visibly
unavailable. Historical evidence remains in its immutable archive.

## Identity and meaning

Identity is repository, exact source commit, module, and declaration. Display
names are labels; they cannot replace quoted Lean names in exact joins. A short
problem query can match multiple variants. Evidence for one variant or revision
does not automatically apply to another.

`schemaVersion: 2` retains the existing native fields and their meanings.
`moduleDocstrings` stores module documentation once, keyed by module name.
`formalProofs` retains each proof's kind, URL, and conditions separately.
`hasSorryFreeProof` is an extracted observation, not independent verification.
`answerKinds` records answer interpretation. Source docstrings and exact GitHub
links provide source context without guessing citations from rendered HTML.

The publication profile requires statements, module documentation, and provenance;
partial `extract_names --exclude` output is not a full published catalog. A nullable
docstring records unavailable documentation. Empty arrays record no extracted
entries, not missing transport. Consumers must distinguish these states.

Publication emits finite numbers and unique object members. Object member order
has no meaning; native array order is retained. Compatible optional fields may be
added; readers may ignore unknown fields. Removing fields, changing their meaning,
or changing required types requires a new contract version. Schemas are packaged
and published from the same checkout as the producer.

## Build ownership

`.github/workflows/build-and-docs.yml` remains the orchestrator. Lake owns Lean
compilation and dependency pins. `extract_names` reads the shared elaborated
metadata. The publication script adds provenance and validates completeness.
Verso's existing literate build owns rendering. Its fragment step binds rendering
to the catalog from that build. Node builds the static pages and derives display
labels without publishing another semantic catalog.

A full build publishes catalog, rendering, schemas, and pages together. A
website-only build reads the existing published snapshot and uses its rendering
origin explicitly. It downloads the full Verso module index under the same catalog
digest; it never reconstructs an incomplete index from problem declarations. A
missing or mismatched index stops the preview build. It cannot bootstrap the first catalog deployment.

Evidence archives own review and verification results. The board owns observed
queue context. They join to the catalog by exact target references; neither can
rewrite statements or maintainer status. Missing optional feeds are visible and
non-blocking. Invalid catalog integrity is blocking.
