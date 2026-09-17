# Suite images for one frozen evaluation core. The build context contains suite-core.json only.
# The verifier target prepares every case with the trusted controller in the pinned verifier
# base; the solver target receives only the resulting shared packages.
ARG VERIFIER_BASE
ARG SOLVER_BASE

FROM ${VERIFIER_BASE} AS verifier
COPY --chown=1000:1000 suite-core.json /tmp/suite-core.json
USER root
RUN mkdir -p /opt/fc-suite /tests && chown 1000:1000 /opt/fc-suite \
    && printf '#!/bin/sh\nset -eu\nexport PYTHONPATH=/opt/fc/toolkit\nexec python3 -m conjectures.eval_verifier --submission /app --out /logs/verifier\n' > /tests/test.sh \
    && chmod 0755 /tests/test.sh
USER 1000:1000
RUN PYTHONPATH=/opt/fc/toolkit python3 -m conjectures.eval_suite prepare --core /tmp/suite-core.json --out /opt/fc-suite \
    && chmod -R a-w /opt/fc-suite/packages \
    && rm -rf /home/fc/.cache /tmp/suite-core.json
WORKDIR /app

FROM ${SOLVER_BASE} AS solver
COPY --from=verifier --chown=1000:1000 /opt/fc-suite/packages /opt/fc-suite/packages
WORKDIR /app
