# Voting System

The Formal Conjectures website includes a voting, truth prediction, and difficulty rating system backed by GitHub Discussions. GitHub OAuth is used for identity verification — the consent screen requires zero permissions ("Verify your GitHub identity").

## Architecture

```
Browser (voting.js)
  ├── Reads: GET /discussions → App Engine proxy → GitHub GraphQL (read-only PAT)
  └── Writes: directly → GitHub GraphQL (user's OAuth token)
        ├── Likes = HEART reactions on Discussion
        ├── Truth predictions = THUMBS_UP / THUMBS_DOWN reactions
        └── Difficulty ratings = comments matching /^difficulty [0-9]$/i
```

All data is stored as native GitHub Discussions features (reactions and comments) on the repository. There is no separate database.

## How Votes Work

- Each user can vote once per theorem (like/unlike toggle via HEART reaction)
- Discussions are created lazily: a Discussion is created when a logged-in user first views a theorem detail page (or when the first interaction occurs)
- Discussion titles are the fully-qualified Lean theorem name

## Truth Predictions

- Users can predict whether a conjecture is true (thumbs up) or false (thumbs down)
- Each user can have one prediction per theorem; changing your prediction removes the old one
- The browse page shows aggregated prediction counts

## Difficulty Ratings

- Users can rate the difficulty of each theorem on a 0–9 scale
- Ratings are stored as discussion comments matching `difficulty N`
- Submitting a new rating deletes the previous rating comment
- The browse page shows the average difficulty alongside the vote count

## Consent Modal

The first time a user clicks vote, predict, or rate difficulty, a modal dialog explains:
- Why GitHub login is needed (identity verification only, zero permissions)
- That all activity is public (stored as GitHub Discussions, visible to anyone)
- What specifically is stored (heart reactions, thumbs reactions, comments)

The acknowledgement is stored in `localStorage` so it only appears once.

## OAuth Flow

1. User clicks a voting/prediction/rating action
2. Consent modal appears (first time only) explaining public nature of activity
3. Browser redirects to `https://github.com/login/oauth/authorize` with `client_id` and `redirect_uri` (no scopes — zero permissions)
4. GitHub redirects back to the page with `?code=...`
5. `voting.js` detects the code, POSTs `{ code }` to the App Engine proxy's `/token` endpoint
6. The proxy exchanges the code for an access token using the client secret
7. `voting.js` fetches `/user` from GitHub to get the username
8. Token and username are stored in `localStorage`

## Client Configuration

Constants at the top of `src/js/voting.js`:

| Constant | Description |
|---|---|
| `WORKER_URL` | URL of the App Engine proxy |
| `GH_CLIENT_ID` | GitHub App client ID |
| `REPO_OWNER` | GitHub repo owner |
| `REPO_NAME` | GitHub repo name |
| `REPO_ID` | GitHub repo GraphQL node ID |

## Setting Up for Development

1. **Register a GitHub App** at https://github.com/settings/apps
   - Enable Discussions: Read & Write permission
   - Set the callback URL to your local dev URL (e.g., `http://localhost:8000`)
   - Install it on the target repo
2. **Create a fine-grained PAT** with read-only Discussions access for the read proxy
3. **Set up the App Engine proxy** — see [`appengine/README.md`](../appengine/README.md)
4. **Update `voting.js` constants** — point `WORKER_URL` to `http://localhost:8080`, set `GH_CLIENT_ID`
5. **Start the proxy**: `cd appengine && npm start`
6. **Build and serve the site**: `npm run build && cd site && python3 -m http.server 8000`

## Deploying to Production

1. **Create a GitHub App** (or reuse the dev one) — set the **Authorization callback URL** to your production site URL
2. **Deploy the App Engine proxy** — see [`appengine/README.md`](../appengine/README.md)
3. **Update `voting.js` constants** — set `WORKER_URL` to your deployed proxy URL and `GH_CLIENT_ID` to your production client ID
4. **Build and deploy the site**: `npm run build` and deploy the `site/` directory (e.g., via GitHub Pages)

## Limitations

- GitHub GraphQL API has rate limits (5000 points/hour for authenticated users)
- The `GET /discussions` endpoint paginates through all discussions, which may be slow with very large numbers
- Vote counts are cached in memory after the first fetch within a page session
- The App Engine proxy caches discussion data for 60 seconds
