# Trusted build environment; reviewer containers run with networking disabled.
FROM ubuntu:24.04
ARG TARGETARCH
ARG FC_REV=d33e35a5f45386a173b31159ae6598b1968bc463
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git python3 zstd build-essential ripgrep && rm -rf /var/lib/apt/lists/*
RUN arch=linux; if [ "$TARGETARCH" = arm64 ]; then arch=linux_aarch64; fi; \
    curl -fL "https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-${arch}.tar.zst" \
    | tar --zstd -x -C /opt && mv /opt/lean-* /opt/lean
ENV PATH="/opt/lean/bin:${PATH}"
WORKDIR /workspace
RUN mkdir /sources /skill /output && chown 65534:65534 /workspace /output
ENV HOME=/tmp
USER 65534:65534
RUN git init && git remote add origin https://github.com/google-deepmind/formal-conjectures.git \
    && git fetch --depth 1 origin "$FC_REV" && git checkout --detach FETCH_HEAD \
    && lake exe cache get && lake --wfail build FormalConjecturesUtil FormalConjecturesForMathlib \
    && printf '%s\n' "$FC_REV" > /workspace/.fc-revision \
    && rm -rf .git .agents .claude .github scripts site /tmp/.cache \
    && rm -rf FormalConjectures .lake/build/lib/lean/FormalConjectures \
    && mkdir FormalConjectures
CMD ["sleep", "infinity"]
