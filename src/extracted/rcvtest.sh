#!/usr/bin/env sh
cabal run -- --constants=../../../open-rcv-tests/tests/constants.json --tests=../../../open-rcv-tests/tests/irv.json $@
