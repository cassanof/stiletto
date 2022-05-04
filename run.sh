#!/bin/bash
make clean
make test
dune build --profile release
./test
