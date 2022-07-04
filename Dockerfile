# Here the build environment is set up
FROM ubuntu:18.04 AS environment

RUN apt update
RUN apt install -y cmake g++ python3.7 python3.7-dev python3.7-venv python3-pip libgmp3-dev wget unzip git chezscheme
RUN python3.7 -m pip install pytest
RUN python3.7 -m pip install Cython
# Install Cairo
RUN wget https://github.com/starkware-libs/cairo-lang/releases/download/v0.9.0/cairo-lang-0.9.0.zip
RUN python3.7 -m pip install contextvars
RUN unzip cairo-lang-0.9.0.zip
RUN python3.7 -m pip install cairo-lang-0.9.0.zip

# Build the Idris2 compiler
# https://github.com/idris-lang/Idris2/blob/main/INSTALL.md
RUN wget https://github.com/idris-lang/Idris2/archive/9e92e7ded05741aa7d030f815c0441867b77ad0b.zip
RUN unzip 9e92e7ded05741aa7d030f815c0441867b77ad0b.zip
WORKDIR /Idris2-9e92e7ded05741aa7d030f815c0441867b77ad0b/

RUN make bootstrap SCHEME=chezscheme9.5
# ENV PATH="/Idris2/build/exec/:${PATH}"
RUN make install

ENV PATH="/root/.idris2/bin:${PATH}"
RUN make clean && make all && make install && make install-api

RUN python3.7 -m pip install hypothesis


# Here we build the idrisToCairo compiler
FROM environment AS compiler
COPY . /app/
WORKDIR /app/
RUN rm -rf build/
RUN make build
RUN make install-lib

RUN cp -r build/exec/* /usr/local/bin/
