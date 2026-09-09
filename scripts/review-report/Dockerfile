# Adapt a reviewed FC evaluation cache for the Actions pilot.
ARG REVIEW_EVAL_IMAGE=fc-review-cache
FROM ${REVIEW_EVAL_IMAGE}
USER root
RUN ln -s /workspace /opt/review-cache
USER 65534:65534
