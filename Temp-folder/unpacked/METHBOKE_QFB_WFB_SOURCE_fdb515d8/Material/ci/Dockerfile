# Bootstrap only. Subsequent runs execute the last compatible PASSED image.
FROM ubuntu:24.04

ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.33.0
ARG ELAN_VERSION=v4.2.4
ARG ELAN_SHA256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install --yes --no-install-recommends \
      ca-certificates curl git build-essential python3 rsync zstd time \
    && rm -rf /var/lib/apt/lists/*

# The checksum is the official release asset digest, recorded on 2026-11-17.
RUN curl --fail --location --retry 3 \
      "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz" \
      --output /tmp/elan.tar.gz \
    && printf '%s  %s\n' "${ELAN_SHA256}" /tmp/elan.tar.gz | sha256sum --check --strict \
    && tar -xzf /tmp/elan.tar.gz -C /tmp \
    && /tmp/elan-init -y --no-modify-path --default-toolchain none \
    && rm -f /tmp/elan.tar.gz /tmp/elan-init

ENV PATH="/root/.elan/bin:${PATH}"
RUN elan toolchain install "${LEAN_TOOLCHAIN}" \
    && elan default "${LEAN_TOOLCHAIN}" \
    && mkdir -p /workspace /opt/material-registry

WORKDIR /workspace
CMD ["/bin/bash"]
