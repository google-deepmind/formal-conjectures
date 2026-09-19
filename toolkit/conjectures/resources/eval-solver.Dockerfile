# Minimal Harbor solver recipe: the exact Lean toolchain for the exported workspaces.
# It contains no toolkit, verifier tools, credentials or reference answers. Harness
# agents install their own clients; the exported task adds the workspace at /app.
ARG BASE_IMAGE=debian:bookworm-slim@sha256:88200866dfff7ea7f5cbcb6ec7c8a701889efe6fe859fe64d6990e4b07ea4171
FROM ${BASE_IMAGE}
ARG LEAN_TOOLCHAIN
ARG ELAN_VERSION=v4.2.4
ARG ELAN_SHA256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git python3 zstd \
    && rm -rf /var/lib/apt/lists/* \
    && groupadd -g 1000 fc && useradd -m -u 1000 -g 1000 -d /home/fc fc \
    && mkdir -p /app && chown 1000:1000 /app
USER 1000:1000
ENV HOME=/home/fc PATH=/home/fc/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN curl -fsSL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz" -o /tmp/elan.tar.gz \
    && echo "${ELAN_SHA256}  /tmp/elan.tar.gz" | sha256sum -c - \
    && tar -xzf /tmp/elan.tar.gz -C /tmp && /tmp/elan-init -y --no-modify-path --default-toolchain "${LEAN_TOOLCHAIN}" \
    && rm -f /tmp/elan.tar.gz /tmp/elan-init && lean --version
WORKDIR /app
CMD ["sleep", "infinity"]
