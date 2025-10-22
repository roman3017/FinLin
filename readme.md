# Formal Verification with Lean4

The main purpose of this repository is formal verification of results in this report:

 - https://doi.org/10.13140/RG.2.2.27652.59523

The current status is here:

 - https://roman3017.github.io/FinLin

## Build

```sh
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env

lake exe cache get
lake build

lake build FinLin.Main
lake env lean FinLin/Main.lean

leanblueprint all
leanblueprint serve
```

## References

 - https://github.com/PatrickMassot/leanblueprint
