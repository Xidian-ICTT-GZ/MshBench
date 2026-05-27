# VeriC-Rt: LLM-Generated Formal Specifications with Verifier-Guided Repair
#
# Base: Ubuntu 22.04
# Includes: VeriFast v26.01, LLVM/Clang 12, OpenJDK 11, Rust nightly
#
# Build:
#   docker build -t veric-rt .
#
# Run:
#   docker run -it --rm \
#     -v $(pwd):/workspace \
#     -e API_URL="your-api-url" \
#     -e API_KEY="your-api-key" \
#     veric-rt
#
# Run experiment inside container:
#   python -m pipeline.run_spec_experiment \
#     --benchmark-root ground_true \
#     --metadata data/benchmark_metadata.csv \
#     --data-dir data/benchmark \
#     --config pipeline/configs/llm_spec_experiment.json \
#     --languages c,java \
#     --pass-k 5 \
#     --max-rounds 3 \
#     --workers 4 \
#     --run-prefix output_docker \
#     --progress-every 10

FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# ------------------------------------------------------------------
# Use Tsinghua mirror for faster APT in China
# ------------------------------------------------------------------
RUN sed -i 's@archive.ubuntu.com@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list \
 && sed -i 's@security.ubuntu.com@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list

# ------------------------------------------------------------------
# Install system dependencies
# ------------------------------------------------------------------
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
    wget \
    curl \
    tar \
    xz-utils \
    build-essential \
    python3 \
    python3-pip \
    python3-venv \
    openjdk-11-jdk \
    libffi-dev \
    zlib1g-dev \
    llvm-12 \
    clang-12 \
    ca-certificates \
    git \
 && rm -rf /var/lib/apt/lists/*

# ------------------------------------------------------------------
# LLVM/Clang paths
# ------------------------------------------------------------------
ENV PATH="/usr/lib/llvm-12/bin:${PATH}"
ENV LD_LIBRARY_PATH=""
ENV LD_LIBRARY_PATH="/usr/lib/llvm-12/lib:${LD_LIBRARY_PATH}"

# ------------------------------------------------------------------
# Install VeriFast v26.01
# ------------------------------------------------------------------
ENV VERIFAST_DIR=/opt/verifast

RUN mkdir -p ${VERIFAST_DIR} \
 && cd /tmp \
 && wget -q -O verifast.tar.gz \
    https://github.com/verifast/verifast/releases/download/26.01/verifast-26.01-linux.tar.gz \
 && tar xzf verifast.tar.gz -C ${VERIFAST_DIR} --strip-components=1 \
 && rm verifast.tar.gz

ENV PATH="${VERIFAST_DIR}/bin:${VERIFAST_DIR}/vfdeps/bin:${PATH}"

# ------------------------------------------------------------------
# Install Rust nightly (for Rust benchmarks)
# ------------------------------------------------------------------
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain nightly-2025-11-25

ENV PATH="$HOME/.cargo/bin:${PATH}"

# ------------------------------------------------------------------
# Set working directory
# ------------------------------------------------------------------
WORKDIR /workspace

# ------------------------------------------------------------------
# Default command: interactive shell
# ------------------------------------------------------------------
CMD ["/bin/bash"]
