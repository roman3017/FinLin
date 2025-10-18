# Verification

## Build

```sh
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env

lake update
lake build

lake build FinLin.Main
lake env lean FinLin/Main.lean
```
