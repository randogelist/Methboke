# Published only after compilation and fresh audits pass. No compiler runs here.
# Subsequent CI invokes this exact image with the pinned host Lean mount read-only.
FROM ubuntu:24.04
RUN apt-get update && apt-get install --yes --no-install-recommends \
      python3 git ca-certificates curl zstd libstdc++6 libgmp10 libtinfo6 \
    && rm -rf /var/lib/apt/lists/*
COPY Material /workspace/Material
COPY LEAN_CUTOUTS /workspace/LEAN_CUTOUTS
WORKDIR /workspace
CMD ["python3", "Material/ci/native_build.py", "--jobs", "2"]
