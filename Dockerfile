
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive


RUN sed -i 's@archive.ubuntu.com@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list \
 && sed -i 's@security.ubuntu.com@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list


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


ENV PATH="/usr/lib/llvm-12/bin:${PATH}"

ENV LD_LIBRARY_PATH=""
ENV LD_LIBRARY_PATH="/usr/lib/llvm-12/lib:${LD_LIBRARY_PATH}"


ENV VERIFAST_DIR=/opt/verifast

RUN mkdir -p ${VERIFAST_DIR} \
 && cd /tmp \
 && wget -O verifast.tar.gz \
    https://github.com/verifast/verifast/releases/download/26.01/verifast-26.01-linux.tar.gz \
 && tar xzf verifast.tar.gz -C ${VERIFAST_DIR} --strip-components=1 \
 && rm verifast.tar.gz


ENV PATH="${VERIFAST_DIR}/bin:${VERIFAST_DIR}/vfdeps/bin:${PATH}"



RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain nightly-2025-11-25


ENV PATH="$HOME/.cargo/bin:$PATH"
WORKDIR /workspace
CMD ["/bin/bash"]
