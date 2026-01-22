#!/bin/bash

# QTL Translator entrypoint script
# Runs from /home/qtl-translator/work directory (mounted volume)
# Executes the qtl-translator JAR with all provided arguments

java -jar /home/qtl-translator/qtl-translator.jar "$@"
