# Formal Verification with Lean4

The main purpose of this repository is formal verification of this article:

TODO: add link

## Build

```sh
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env

lake update
lake build

lake build FinLin.Main
lake env lean FinLin/Main.lean
```
