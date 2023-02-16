# Call-by-name refinement type checker

## What do you need?
- OCaml 4.13
- OPAM (https://opam.ocaml.org/)
- HoIce (https://github.com/hopv/hoice)

## How to install
$ opam pin add cbn-ref git@github.com:ryosu-sato/cbn-ref.git

## How to use
$ cbn-ref <input.in>

## Benchmark programs
The benchmark programs used in the paper are in "benchmark" directory.
You can reproduce the experiments by executing "exp.fish"
if you have installed LiquidHaskell.
