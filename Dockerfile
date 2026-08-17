# compile react frontend
FROM node:20-slim AS web
WORKDIR /web
# copy manifests first so npm ci stays cached when only the source code changes
COPY web/package.json web/package-lock.json ./
RUN npm ci
COPY web/ ./
# produces /web/dist
RUN npm run build

# python image that is in prod
FROM python:3.12-slim

WORKDIR /app
# unbuffered output so docker logs show up immediately
ENV PYTHONUNBUFFERED=1
# put lake/lean on the path
ENV PATH="/root/.elan/bin:${PATH}"

# install dependencies
RUN apt-get update && apt-get install -y --no-install-recommends graphviz git curl ca-certificates && rm -rf /var/lib/apt/lists/*

# install elan but no default toolchain yet
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none

# install a lean compiler for each version dir in compile-env
COPY compile-env compile-env
RUN for v in compile-env/*/; do \
      tc="$(cat "${v}lean-toolchain")"; \
      elan toolchain install "$tc" && elan default "$tc"; \
    done
# download .olean files of mathlib for each lean version
RUN for v in compile-env/*/; do \
      ( cd "$v" && \
        for i in 1 2 3 4 5; do \
          lake update && lake exe cache get && break; \
          echo "mathlib fetch attempt $i for $v failed, retrying"; \
          [ "$i" = 5 ] && exit 1; \
        done ) || exit 1; \
    done

# requirements first so pip install stays cached when only the app code changes
COPY requirements.txt .
# keep pip's downloads out of the layer
RUN pip install --no-cache-dir -r requirements.txt

# copy the app
COPY api/ api/
COPY scripts/ scripts/
COPY data/ data/
# copy the built frontend from the node image without bringing along node
COPY --from=web /web/dist web/dist

# documents the port. -p 80:8000 in remote_deploy.sh is what actually publishes it
EXPOSE 8000
# serve the flask app with gunicorn.
# 0.0.0.0 means listen on all interfaces, so docker's forwarded traffic can reach it.
# api.app:app tells gunicorn where to find the application object
CMD ["gunicorn", "--bind", "0.0.0.0:8000", "api.app:app"]
