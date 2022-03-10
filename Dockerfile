# Here the build environment is set up
FROM ubuntu:18.04 AS environment

RUN apt update
RUN apt install -y cmake g++ python3.7 python3.7-dev python3.7-venv python3-pip libgmp3-dev wget unzip git chezscheme

# Install Cairo
RUN wget https://github.com/starkware-libs/cairo-lang/releases/download/v0.7.0/cairo-lang-0.7.0.zip
RUN pip3 install contextvars
RUN unzip cairo-lang-0.7.0.zip
RUN pip3 install cairo-lang-0.7.0.zip

# Build the Idris2 compiler
# https://github.com/idris-lang/Idris2/blob/main/INSTALL.md
RUN wget https://github.com/idris-lang/Idris2/archive/9a9412e1a2ac555f05edb7c33036e91ff3c60555.zip
RUN unzip 9a9412e1a2ac555f05edb7c33036e91ff3c60555.zip
WORKDIR /Idris2-9a9412e1a2ac555f05edb7c33036e91ff3c60555/

RUN make bootstrap SCHEME=chezscheme9.5
# ENV PATH="/Idris2/build/exec/:${PATH}"
RUN make install

ENV PATH="/root/.idris2/bin:${PATH}"
RUN make clean && make all && make install && make install-api

RUN pip3 install hypothesis


# Here we build the idrisToCairo compiler
FROM environment AS compiler
COPY . /app/
WORKDIR /app/
RUN rm -rf build/
RUN make build
RUN make install-lib

RUN cp -r build/exec/* /usr/local/bin/