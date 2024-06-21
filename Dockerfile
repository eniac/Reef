FROM rust:1.78

ADD . /Reef

RUN chmod u+x /Reef/tests/scripts/* && apt-get update && \
    apt-get install -y build-essential nlohmann-json3-dev libgmp-dev nasm time libunbound-dev && \
    git clone https://github.com/iden3/circom.git && cd circom && \
    cargo build --release && cargo install --path circom && \
    cd /Reef && cargo build --release && export PATH=/Reef/target/release/:$PATH && \
    cd /Reef/match_cpp && make

WORKDIR "/Reef"
CMD "/bin/bash"


