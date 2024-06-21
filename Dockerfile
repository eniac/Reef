FROM rust:1.78

ADD . /Reef

RUN apt-get update && \
    apt-get install -y build-essential nlohmann-json3-dev libgmp-dev nasm && \
    cd /Reef && cargo build --release && export PATH=/Reef/target/release/:$PATH

WORKDIR "/Reef"
CMD "/bin/bash"


