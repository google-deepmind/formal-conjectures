# Qualification-only layout adapter; dependencies come from the production recipe.
ARG REVIEW_IMAGE
FROM ${REVIEW_IMAGE}
USER root
RUN ln -s /opt/review-cache /workspace && mkdir /sources /skill /output \
    && chown 65534:65534 /output
USER 65534:65534
WORKDIR /workspace
