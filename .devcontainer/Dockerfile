FROM hakarlsson/hol:t2

ARG Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-debian-8.11.zip"
ARG GCC_ARM8_URL="https://developer.arm.com/-/media/Files/downloads/gnu-a/8.2-2018.08/gcc-arm-8.2-2018.08-x86_64-aarch64-elf.tar.xz"
ARG GCC_ARM_URL="https://developer.arm.com/-/media/Files/downloads/gnu-rm/7-2018q2/gcc-arm-none-eabi-7-2018-q2-update-linux.tar.bz2"
ARG GCC_RISCV_URL="https://static.dev.sifive.com/dev-tools/riscv64-unknown-elf-gcc-8.3.0-2019.08.0-x86_64-linux-ubuntu14.tar.gz"

ENV PATH="$PATH:/opt/hol_t2/bin"
ENV DEBIAN_FRONTEND=noninteractive

RUN apt update && apt install -y git build-essential gnupg2 python3 wget unzip

RUN cd /opt/hol_t2/examples/l3-machine-code/common && Holmake
RUN cd /opt/hol_t2/examples/l3-machine-code/arm8/model && Holmake
RUN cd /opt/hol_t2/examples/l3-machine-code/arm8/step && Holmake
RUN cd /opt/hol_t2/examples/l3-machine-code/m0/model && Holmake
RUN cd /opt/hol_t2/examples/l3-machine-code/m0/step && Holmake


RUN wget $Z3_URL -O /tmp/z3.zip && unzip /tmp/z3.zip -d /opt && rm /tmp/z3.zip
RUN mkdir /opt/gcc-arm-none-eabi-7-2018-q2u && wget -qO- $GCC_ARM_URL | tar -xj -C "/opt/gcc-arm-none-eabi-7-2018-q2u" --strip-components=1
RUN mkdir /opt/gcc-arm8-8.2-2018.08-aarch64-elf && wget -qO- $GCC_ARM8_URL | tar -xJ -C "/opt/gcc-arm8-8.2-2018.08-aarch64-elf" --strip-components=1
RUN mkdir /opt/gcc-riscv64-unknown-elf-8.3.0-2019.08.0 && wget -qO- $GCC_RISCV_URL | tar -xz -C "/opt/gcc-riscv64-unknown-elf-8.3.0-2019.08.0" --strip-components=1
RUN mkdir /opt/embexp-logs \
 && git clone https://github.com/kth-step/EmbExp-Logs.git
RUN mkdir /opt/embexp && cd /opt/embexp \
 && git clone https://github.com/kth-step/EmbExp-ProgPlatform.git \
 && GIT_URL_BOX_HTTPS=https://github.com/kth-step/EmbExp-Box.git

RUN git clone https://github.com/herd/herdtools7.git /opt/herdtools7
RUN git clone https://github.com/litmus-tests/litmus-tests-riscv.git /opt/litmus-tests-riscv

ENV HOLDIR="/opt/hol_t2"
RUN apt install -y silversearcher-ag
