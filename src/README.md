# Formal RCV source

## Building

### Prerequisites

Install Coq. This project currently builds with
[Version8.4pl6](https://coq.inria.fr/coq-84) Install the
[Haskell Platform](https://www.haskell.org/platform/) be sure to get
at least GHC 7.8

run make in the source directory:
```
make
```

This should build all of the Coq files in the directory. Building the
Coq files also checks the proof of correctness for the implementation
of ranked choice voting.

To build the docs for the Coq files run:
```
make html
```

This will place docs in a folder named HTML

Then move to the extracted folder
```
cd extracted
```

Create a cabal sandbox

```
cabal sandbox init
```

and run

```
cabal install --run-tests
```

to build the haskell and the dependencies, running the quickcheck
tests that have been extracted from Coq




