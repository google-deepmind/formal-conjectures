# Giscus Voting

The Formal Conjectures theorem page includes two giscus-backed voting surfaces:

- a theorem-level reaction discussion where emoji reactions mean `True`,
  `False`, and `Like`;
- a 1-10 difficulty widget where the range control selects a difficulty bucket
  for the current theorem.

Both surfaces store their public state in GitHub Discussions. The site remains
static: GitHub authentication, reaction state, comments, and discussion creation
are handled by giscus.

## Architecture

```
Theorem page (voting.js)
  |-- Theorem reaction panel embeds one per-theorem Discussion
  |-- Difficulty range selects one per-theorem/per-score Discussion
  |-- giscus_voting.js relabels theorem reaction emojis in the iframe
  `-- GitHub Discussions stores reactions/comments
```

There is no voting backend.

## Discussion Mapping

The theorem-level reaction panel maps each theorem to a stable discussion term:

```
Conjecture discussion: <theorem display name> [<stable hash>]
```

Within that discussion, giscus reactions carry the following meanings:

| Emoji | Meaning |
|---|---|
| 👍 | I believe the conjecture is true. |
| 👎 | I believe the conjecture is false. |
| ❤️ | I like this conjecture. |

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

2. Open a theorem page. Confirm that the theorem reaction panel loads one
   discussion, while adjusting the difficulty slider switches the difficulty
   panel between bucket discussions.

3. A real vote requires the giscus GitHub App to be installed on the configured
   repository and a signed-in GitHub user to react or comment in the embedded
   panel.

## Notes

- The slider value is stored in `localStorage` only as a convenience for the
  current visitor. The public vote data lives in GitHub Discussions.
- The giscus iframe emits metadata so the page can show the reaction count for
  the selected theorem reaction panel or difficulty bucket when a discussion
  exists.
- `giscus_voting.js` applies the custom reaction labels only to the theorem
  reaction panel, not to the difficulty panel.
- The legacy Cloudflare Worker under `worker/` is not used by the current
  theorem-page difficulty widget.
