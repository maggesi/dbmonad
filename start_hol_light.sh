#!/bin/bash

# Configurations
DOCKER_IMAGE='mia-immagine'

# This directory
# GIT_ROOT_DIR="$( git rev-parse --show-toplevel )"
# SRC_DIR="$GIT_ROOT_DIR"
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SRC_DIR="$SCRIPT_DIR"

echo "Info: Work directory is $SRC_DIR"

docker run --rm -it -h hol-light -v "$SRC_DIR:/home/opam/work" \
  $DOCKER_IMAGE ./dmtcp_restart_script.sh