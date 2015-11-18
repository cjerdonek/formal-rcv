#!/usr/bin/env sh
cabal run -- --rcv-path=../../../open-rcv-tests \
	--case=6 \
	--verbose \
	echo '{"rounds":[{"elected":["Bob"],"totals":{"Bob":2,"Ann":0,"Carol":1}}]}'
