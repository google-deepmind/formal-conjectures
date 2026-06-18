# Difficulty Voting

The Formal Conjectures theorem page includes a giscus-backed difficulty voting
widget. A 1-10 range control selects a difficulty bucket for the current
theorem, and the embedded giscus panel stores reactions and optional comments in
GitHub Discussions.

## Architecture

```
Theorem page (voting.js)
  |-- Range input selects a difficulty bucket
  |-- giscus embeds the matching GitHub Discussion
  `-- GitHub Discussions stores reactions/comments
```

The site does not run a voting backend. GitHub authentication, reaction state,
and discussion creation are handled by giscus.

## Discussion Mapping

Each theorem/difficulty pair maps to a stable giscus discussion term:

```
Difficulty <n>/10: <theorem display name> [<stable hash>]
```

The hash is derived from the theorem's fully qualified Lean name, so title
truncation does not create collisions. giscus uses strict title matching and
the repository's `Polls` discussion category.

The numeric bucket is intentionally stable even if the label wording changes
later.

## Difficulty Scale

The scale measures the expected mathematical advance required, rather than time
to solve.

| Score | Label | Description |
|---:|---|---|
| 1 | Student-level | Suitable for a strong student or reading-course project. |
| 2 | Graduate-level | Requires standard graduate material and careful work. |
| 3 | Advanced graduate | A hard graduate or seminar problem, but not really research-level. |
| 4 | Entry-level research | Plausible as a first research problem with good guidance. |
| 5 | Standard research | Approachable to an experienced specialist using current methods. |
| 6 | Nonstandard research | Existing techniques may apply only indirectly; likely needs a clever adaptation. |
| 7 | Methodologically difficult | A genuinely new trick or local method seems likely to be required. |
| 8 | Expert-level | Several experts could reasonably have thought seriously about it; a solution would be notable. |
| 9 | Breakthrough | Would likely unlock progress beyond the problem itself. |
| 10 | Landmark breakthrough | Field-shaping or Millennium-class; use sparingly. |

## Client Configuration

The giscus configuration lives at the top of `src/js/voting.js`. It chooses the
discussion repository from the current hostname, so a forked GitHub Pages test
site does not write votes to the upstream repository.

| Host | Repository | Repo ID | Category | Category ID |
|---|---|---|---|---|
| `google-deepmind.github.io` | `google-deepmind/formal-conjectures` | `R_kgDOOogmBw` | `Polls` | `DIC_kwDOOogmB84C3u0D` |
| `paul-lez.github.io` | `Paul-Lez/formal-conjectures` | `R_kgDORiWUfA` | `Polls` | `DIC_kwDORiWUfM4C_btZ` |

Unknown hosts fall back to the upstream repository. If a new test deployment
host or discussion category is added, update this table using the giscus setup
page or GitHub GraphQL API.

## Local Development

1. Build and serve the site:

   ```bash
   cd site
   ./dev.sh
   ```

2. Open a theorem page, adjust the difficulty slider, and confirm that the
   giscus panel switches buckets.

3. A real vote requires the giscus GitHub App to be installed on the configured
   repository and a signed-in GitHub user to react or comment in the embedded
   panel.

## Notes

- The slider value is stored in `localStorage` only as a convenience for the
  current visitor. The public vote data lives in GitHub Discussions.
- The giscus iframe emits metadata so the page can show the reaction count for
  the selected bucket when a discussion exists.
- The legacy Cloudflare Worker under `worker/` is not used by the current
  theorem-page difficulty widget.
