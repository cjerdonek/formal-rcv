#!/usr/bin/env sh
cabal run rcv_testcase -- \
       --rcv-path=../../../open-rcv-tests \
       --case=6 \
       --verbose \
       ./dist/build/rcv_election/rcv_election
