FROM rust:1.78

ADD . /Reef

RUN chmod u+x /Reef/tests/scripts/* && apt-get update && \
    apt-get install -y build-essential nlohmann-json3-dev libgmp-dev nasm time libunbound-dev && \
    cd /Reef && cargo build --release && export PATH=/Reef/target/release/:$PATH && \
    mkdir -p /Reef/tests/results/memory && mdkir -p /Reef/tests/results/timings && \
    mkdir

WORKDIR "/Reef"
CMD "/bin/bash"


