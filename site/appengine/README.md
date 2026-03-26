# App Engine Proxy

Handles GitHub App OAuth token exchange and anonymous discussion reads for the voting system. One deployment serves all forks.

For an overview of the voting system, see [`docs/voting.md`](../docs/voting.md).

## Shared Proxy

The default deployment at `formal-conjectures-web-worker.uc.r.appspot.com` is used automatically by the CI workflow. Forkers don't need their own proxy — just install the [formal-conjectures-voting](https://github.com/apps/formal-conjectures-voting) GitHub App on their fork.

The shared proxy:
- Uses GitHub App installation tokens (works for any repo where the app is installed)
- Only serves `google-deepmind/formal-conjectures` and its forks
- Allows any `*.github.io` origin via CORS
- Routes OAuth callbacks so a single registered callback URL works for all forks

## Running Your Own Proxy

### Prerequisites

- [Node.js](https://nodejs.org/) >= 22
- [Google Cloud SDK](https://cloud.google.com/sdk/docs/install)
- A GCP project with App Engine enabled

### Create a GitHub App

1. Go to https://github.com/settings/apps/new
2. Set **Callback URL** to `https://YOUR_PROJECT.REGION.r.appspot.com/oauth/callback`
3. Uncheck **Webhook > Active**
4. Under **Repository permissions**, set **Discussions** to **Read & write**
5. Click **Create GitHub App**
6. Note the **App ID**, copy the **Client ID**
7. Generate a **client secret** and a **private key** (PEM file)
8. Install the app on your target repo(s)

### Store Secrets

```bash
gcloud config set project YOUR_PROJECT
gcloud services enable secretmanager.googleapis.com

echo -n "your_client_id" | gcloud secrets create GH_CLIENT_ID --data-file=-
echo -n "your_client_secret" | gcloud secrets create GH_CLIENT_SECRET --data-file=-
gcloud secrets create GH_APP_PRIVATE_KEY --data-file=path/to/private-key.pem

PROJECT_ID=$(gcloud config get-value project)
for SECRET in GH_CLIENT_ID GH_CLIENT_SECRET GH_APP_PRIVATE_KEY; do
  gcloud secrets add-iam-policy-binding $SECRET \
    --member="serviceAccount:${PROJECT_ID}@appspot.gserviceaccount.com" \
    --role="roles/secretmanager.secretAccessor"
done
```

### Deploy

Edit `app.yaml` to set `GH_APP_ID` to your App ID, then:

```bash
cd site/appengine
npm install
gcloud app deploy
```

Update `WORKER_URL` in `voting.js` to your App Engine URL.

### Local Development

```bash
cd site/appengine && npm install
export GH_APP_ID=your_app_id
export GH_CLIENT_ID=your_client_id
export GH_CLIENT_SECRET=your_client_secret
export GH_APP_PRIVATE_KEY="$(cat path/to/private-key.pem)"
export ALLOWED_ORIGIN=http://localhost:8000
node server.js
```

Proxy runs on `http://localhost:8080`. Secrets from env vars skip Secret Manager.

## API Endpoints

### `POST /token`

Exchanges a GitHub OAuth `code` for an access token. Body: `{ "code": "..." }`.

### `GET /oauth/callback?return_to=URL`

OAuth redirect bounce. Validates `return_to` is `*.github.io` or localhost, appends the `code` parameter, and redirects.

### `GET /discussions?owner=OWNER&repo=REPO`

Aggregated discussion data (votes, predictions, difficulty). Uses GitHub App installation tokens. Cached 60 seconds. Returns 403 if the repo is not `google-deepmind/formal-conjectures` or a fork of it.

## Configuration

| Variable | Source | Description |
|---|---|---|
| `ALLOWED_ORIGIN` | `app.yaml` / env | Extra CORS origins (`.github.io` allowed automatically) |
| `GH_APP_ID` | `app.yaml` / env | GitHub App ID |
| `GH_CLIENT_ID` | Secret Manager / env | GitHub App client ID |
| `GH_CLIENT_SECRET` | Secret Manager / env | GitHub App client secret |
| `GH_APP_PRIVATE_KEY` | Secret Manager / env | GitHub App private key (PEM) |

## Cost

App Engine F1 instances include 28 free instance-hours/day. With `max_instances: 1`, this stays within the free tier.
