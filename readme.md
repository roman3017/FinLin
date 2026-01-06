# Formal Verification with Lean4

The main purpose of this repository is a formal verification of results showing that all functions on finite sets are linear upon a suitable injective embedding:

 - http://arxiv.org/abs/2510.20167

All results are fully verified and the status is here:

 - https://roman3017.github.io/FinLin/blueprint/dep_graph_document.html
 - https://roman3017.github.io/FinLin

## Build

```sh
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env

lake update
lake exe cache get
lake build

lake build FinLin.finmap
lake env lean FinLin/finmap.lean

#leanblueprint all
#leanblueprint serve
```

## References

 - https://github.com/PatrickMassot/leanblueprint
