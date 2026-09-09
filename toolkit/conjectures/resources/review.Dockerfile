# Trusted production recipe. Build context contains this file only, never PR files.
ARG BASE_IMAGE
FROM ${BASE_IMAGE}
ARG FC_REV
ARG LEAN_VERSION
ARG LEAN_SHA256
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git python3 zstd build-essential ripgrep && rm -rf /var/lib/apt/lists/*
RUN curl -fL "https://github.com/leanprover/lean4/releases/download/${LEAN_VERSION}/lean-${LEAN_VERSION#v}-linux.tar.zst" -o /tmp/lean.tar.zst \
    && echo "${LEAN_SHA256}  /tmp/lean.tar.zst" | sha256sum -c - \
    && tar --zstd -xf /tmp/lean.tar.zst -C /opt && mv /opt/lean-* /opt/lean && rm /tmp/lean.tar.zst
ENV PATH="/opt/lean/bin:${PATH}" HOME=/tmp
RUN mkdir -p /opt/review-cache /tmp/.cache && chown -R 65534:65534 /opt/review-cache /tmp/.cache
USER 65534:65534
WORKDIR /opt/review-cache
RUN git init && git remote add origin https://github.com/google-deepmind/formal-conjectures.git \
    && git fetch --depth 1 origin "$FC_REV" && git checkout --detach FETCH_HEAD \
    && lake exe cache get && lake --wfail build FormalConjecturesUtil FormalConjecturesForMathlib \
    && printf '%s\n' "$FC_REV" > .fc-revision \
    && rm -rf .git .agents .claude .github scripts site /tmp/.cache \
    && rm -rf FormalConjectures .lake/build/lib/lean/FormalConjectures && mkdir FormalConjectures
CMD ["sleep", "infinity"]
