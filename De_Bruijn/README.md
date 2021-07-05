# De Bruijn encoding and initial semantics in HOL Light #

This repository contains scripts for the HOL Light theorem prover about
the initial semantics for higher-order syntax using the De Bruijn encoding.

The principal file is `De_Bruijn/make.ml".  Use it as a guide to explore
the other files in order and to load the formalization.

To load this formalization in HOL Light, add this directory to the
load_path of HOL Light, then use the command
```
needs "De_Bruijn/make.ml";;
```