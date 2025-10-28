# Formal Verification with Lean4

The main purpose of this repository is formal verification of results in this report:

 - http://arxiv.org/abs/2510.20167

All results are fully verified and the status is here:

 - https://roman3017.github.io/FinLin/blueprint/dep_graph_document.html
 - https://roman3017.github.io/FinLin

## Build

```sh
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env

lake exe cache get
lake build

lake build FinLin.finmap
lake env lean FinLin/finmap.lean

#leanblueprint all
#leanblueprint serve
```

## References

 - https://github.com/PatrickMassot/leanblueprint
