# OAuth Proxy & Discussions Reader — App Engine

A repo-agnostic App Engine service that provides GitHub App OAuth token exchange and a read-only proxy for GitHub Discussions data. One deployment can serve multiple repositories — any repo with the GitHub App installed works automatically.

## Default Shared Proxy

The Formal Conjectures project runs a shared proxy on the `formal-conjectures-web-worker` GCP project. This is used by the default `voting.js` configuration, so **forkers do not need to deploy their own proxy**.

The shared proxy:
- Handles OAuth token exchange for the [formal-conjectures-voting](https://github.com/apps/formal-conjectures-voting) GitHub App (`Iv23lid2mjCGp7EIKrJn`)
- Reads discussions from any repo where the app is installed, via `?owner=X&repo=Y`
- Uses GitHub App installation tokens — no per-repo PAT needed

To use the shared proxy with a new fork:
1. Install the GitHub App on your fork: https://github.com/apps/formal-conjectures-voting/installations/new
2. That's it. The proxy automatically obtains an installation token for your repo.

## Running Your Own Proxy

If you prefer to run your own proxy (e.g. for a private fork, or to avoid depending on the shared service), follow the steps below.

### Prerequisites

- [Node.js](https://nodejs.org/) >= 20
- [Google Cloud SDK](https://cloud.google.com/sdk/docs/install) (`gcloud` CLI)
- A GCP project with App Engine enabled

### Setup

```bash
cd site/appengine
npm install
```

### Creating the GitHub App

1. Go to https://github.com/settings/apps/new
2. Fill in:
   - **App name**: anything (e.g. "FC Voting")
   - **Homepage URL**: your site URL
   - **Callback URL**: your site URL (must match where users are redirected after OAuth)
   - **Webhook**: uncheck "Active" (not needed)
3. Under **Permissions > Repository permissions**, set **Discussions** to **Read & write**
4. Click **Create GitHub App**
5. Note the **App ID** (shown at the top of the app's settings page)
6. Copy the **Client ID** (`GH_CLIENT_ID`)
7. Click **Generate a new client secret** and copy it (`GH_CLIENT_SECRET`)
8. Scroll to **Private keys** and click **Generate a private key** — save the downloaded PEM file (`GH_APP_PRIVATE_KEY`)
9. **Install the app** on your repo: go to https://github.com/settings/apps, click your app, then **Install App**, and select the target repository

### Secrets

The server loads secrets from environment variables if set, otherwise from [Google Cloud Secret Manager](https://cloud.google.com/secret-manager). This means local dev uses env vars and production uses Secret Manager — same code, no config files with real secrets.

#### Storing secrets in Secret Manager (production)

```bash
echo -n "your_client_id" | gcloud secrets create GH_CLIENT_ID --data-file=-
echo -n "your_client_secret" | gcloud secrets create GH_CLIENT_SECRET --data-file=-
gcloud secrets create GH_APP_PRIVATE_KEY --data-file=path/to/private-key.pem
```

Grant the App Engine service account access:

```bash
PROJECT_ID=$(gcloud config get-value project)
for SECRET in GH_CLIENT_ID GH_CLIENT_SECRET GH_APP_PRIVATE_KEY; do
  gcloud secrets add-iam-policy-binding $SECRET \
    --member="serviceAccount:${PROJECT_ID}@appspot.gserviceaccount.com" \
    --role="roles/secretmanager.secretAccessor"
done
```

### Local Development

```bash
cd site/appengine
export GH_APP_ID=your_app_id
export GH_CLIENT_ID=your_client_id
export GH_CLIENT_SECRET=your_client_secret
export GH_APP_PRIVATE_KEY="$(cat path/to/private-key.pem)"
export ALLOWED_ORIGIN=http://localhost:8000
node server.js
```

Then edit `src/js/voting.js` to point `WORKER_URL` at `http://localhost:8080` and serve the site:

```bash
cd site/site
python3 -m http.server 8000
```

### Deploy

Edit `app.yaml` to set `ALLOWED_ORIGIN` and `GH_APP_ID` for your deployment, then:

```bash
gcloud app deploy
```

Secrets are loaded from Secret Manager automatically at startup.

Your service will be available at `https://PROJECT_ID.REGION_ID.r.appspot.com`. Update `WORKER_URL` in `voting.js` to point to this URL.

## API Endpoints

### `POST /token`

OAuth code exchange. Receives `{ "code": "..." }` and exchanges it for a GitHub access token using the GitHub App's client secret.

### `GET /discussions?owner=OWNER&repo=REPO`

Returns aggregated discussion data for the given repository. The proxy obtains a GitHub App installation token for the repo automatically (the app must be installed there). Includes vote counts (HEART reactions), truth predictions (THUMBS_UP/DOWN), and average difficulty ratings (parsed from comments). Response is cached for 60 seconds.

## Configuration

| Variable | Source | Description |
|---|---|---|
| `ALLOWED_ORIGIN` | `app.yaml` / env | CORS allowed origin(s), comma-separated |
| `GH_APP_ID` | `app.yaml` / env | GitHub App ID (not a secret) |
| `GH_CLIENT_ID` | Secret Manager / env | GitHub App client ID |
| `GH_CLIENT_SECRET` | Secret Manager / env | GitHub App client secret |
| `GH_APP_PRIVATE_KEY` | Secret Manager / env | GitHub App private key (PEM) |

## Cost

App Engine standard F1 instances include 28 free instance hours/day. With `max_instances: 1` in `app.yaml`, this proxy stays well within the free tier for typical usage.
