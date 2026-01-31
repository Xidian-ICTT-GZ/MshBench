# ===============================
# Dockerfile for VeriFast 26.01 (x86_64)
# ===============================
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# -------------------------------
# ★ 关键：切换 Ubuntu apt 源为清华镜像
# -------------------------------
RUN sed -i 's@archive.ubuntu.com@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list \
 && sed -i 's@security.ubuntu.com@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list

# -------------------------------
# 安装基础工具和依赖
# -------------------------------
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
    wget \
    curl \
    tar \
    xz-utils \
    build-essential \
    python3 \
    python3-pip \
    openjdk-11-jdk \
    libffi-dev \
    zlib1g-dev \
    llvm-12 \
    clang-12 \
    ca-certificates \
 && rm -rf /var/lib/apt/lists/*

# -------------------------------
# LLVM 环境
# -------------------------------
ENV PATH="/usr/lib/llvm-12/bin:${PATH}"

ENV LD_LIBRARY_PATH=""
ENV LD_LIBRARY_PATH="/usr/lib/llvm-12/lib:${LD_LIBRARY_PATH}"

# -------------------------------
# 安装 VeriFast 26.01（二进制）
# -------------------------------
ENV VERIFAST_DIR=/opt/verifast

RUN mkdir -p ${VERIFAST_DIR} \
 && cd /tmp \
 && wget -O verifast.tar.gz \
    https://github.com/verifast/verifast/releases/download/26.01/verifast-26.01-linux.tar.gz \
 && tar xzf verifast.tar.gz -C ${VERIFAST_DIR} --strip-components=1 \
 && rm verifast.tar.gz

# VeriFast 加入 PATH
ENV PATH="${VERIFAST_DIR}/bin:${VERIFAST_DIR}/vfdeps/bin:${PATH}"


# -------------------------------
# 安装 Rust (nightly)
# -------------------------------
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain nightly-2025-11-25

# 将 Rust 的 bin 添加到 PATH，每次 shell 自动生效
ENV PATH="$HOME/.cargo/bin:$PATH"
WORKDIR /workspace
CMD ["/bin/bash"]
