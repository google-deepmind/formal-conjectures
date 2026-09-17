# Trusted Harbor verifier recipe. Build with an empty context: every input is a pinned
# argument, and no task, candidate or agent file enters the image.
# Tool pins must equal conjectures.proof.PINS; the verifier rechecks them at runtime.
ARG BASE_IMAGE=debian:bookworm-slim@sha256:88200866dfff7ea7f5cbcb6ec7c8a701889efe6fe859fe64d6990e4b07ea4171
ARG GO_IMAGE=golang:1.24-bookworm@sha256:1a6d4452c65dea36aac2e2d606b01b4a029ec90cc1ae53890540ce6173ea77ac
ARG RUST_IMAGE=rust:1-bookworm@sha256:9a73a5088750b4c95158ab26629c854c3d6fc4b173cb7bc8079ad252d8ed7bfa

FROM ${GO_IMAGE} AS landrun
ARG LANDRUN_REPOSITORY
ARG LANDRUN_REV
RUN git init /src && git -C /src fetch --depth 1 "https://github.com/${LANDRUN_REPOSITORY}.git" "${LANDRUN_REV}" \
    && git -C /src checkout --detach FETCH_HEAD && cd /src && go build -o landrun ./cmd/landrun

FROM ${RUST_IMAGE} AS nanoda
ARG NANODA_REPOSITORY
ARG NANODA_REV
RUN git init /src && git -C /src fetch --depth 1 "https://github.com/${NANODA_REPOSITORY}.git" "${NANODA_REV}" \
    && git -C /src checkout --detach FETCH_HEAD && cd /src && cargo build --release

FROM ${BASE_IMAGE}
ARG FC_REPOSITORY
ARG FC_COMMIT
ARG GENERATOR_REPOSITORY
ARG GENERATOR_REV
ARG COMPARATOR_REPOSITORY
ARG COMPARATOR_REV
ARG ELAN_VERSION=v4.2.4
ARG ELAN_SHA256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential ca-certificates curl git libseccomp2 python3 zstd \
    && rm -rf /var/lib/apt/lists/* \
    && groupadd -g 1000 fc && useradd -m -u 1000 -g 1000 -d /home/fc fc \
    && mkdir -p /opt/fc /opt/fc-tools /app && chown 1000:1000 /opt/fc /opt/fc-tools /app
USER 1000:1000
ENV HOME=/home/fc PATH=/home/fc/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN curl -fsSL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz" -o /tmp/elan.tar.gz \
    && echo "${ELAN_SHA256}  /tmp/elan.tar.gz" | sha256sum -c - \
    && tar -xzf /tmp/elan.tar.gz -C /tmp && /tmp/elan-init -y --no-modify-path --default-toolchain none \
    && rm -f /tmp/elan.tar.gz /tmp/elan-init
RUN git init /opt/fc && git -C /opt/fc fetch --depth 1 "https://github.com/${FC_REPOSITORY}.git" "${FC_COMMIT}" \
    && git -C /opt/fc checkout --detach FETCH_HEAD \
    && test "$(git -C /opt/fc rev-parse HEAD)" = "${FC_COMMIT}"
COPY --from=landrun --chown=1000:1000 /src /opt/fc-tools/landrun
COPY --from=nanoda --chown=1000:1000 /src /opt/fc-tools/nanoda
RUN for tool in "generator ${GENERATOR_REPOSITORY} ${GENERATOR_REV}" "comparator ${COMPARATOR_REPOSITORY} ${COMPARATOR_REV}"; do \
        set -- $tool; git init "/opt/fc-tools/$1" \
        && git -C "/opt/fc-tools/$1" fetch --depth 1 "https://github.com/$2.git" "$3" \
        && git -C "/opt/fc-tools/$1" checkout --detach FETCH_HEAD \
        && (cd "/opt/fc-tools/$1" && lake --wfail build) || exit 1; \
    done \
    && cd /opt/fc/comparator/verifier && lake build lean4export/lean4export \
    && elan default "$(cat /opt/fc/lean-toolchain)" \
    && rm -rf /home/fc/.cache
WORKDIR /app
CMD ["sleep", "infinity"]
