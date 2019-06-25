
#### This is a codebase accompanying our paper, "A Functional Proof Pearl: Inverting the Ackermann Hierarchy", submitted to APLAS 2019. 

Our paper hyperlinks to this repository extensively, allowing curious readers to jump to real compilable definitions whenever we reference them in our text. 

This Coq development is split between parallel efforts in unary-encoded and binary-encoded inputs to our functions. We provide a Makefile, but if users prefer to compile by hand, we recommend the following order of compilation: 
```
COQC prelims.v
COQC repeater.v
COQC increasing_expanding.v
COQC inverse.v
COQC countdown.v
COQC applications.v
COQC inv_ack.v
COQC bin_prelims.v
COQC bin_repeater.v
COQC bin_inverse.v
COQC bin_countdown.v
COQC bin_applications.v
COQC bin_inv_ack.v
```

In addition to this, we provide two minimal standalone files that show all our techniques independently of the rest of the development.
- `inv_ack_standalone.v` independently demonstrates all our flavors of inverse Ackermann.
- `inv_hyperop_standalone.v` does the same for the inverse hyperoperation hierarchy.

We test the time bounds we claim in two ways. 
- In `inv_ack_test.v`, we test our definitions in Gallina itself. We invite readers to open that file and click through it.
- In the files `test_runtime_ocaml.ml` and `bin_test_runtime_ocaml.ml`, we extract our key contributions to OCaml and then run the same benchmarks on them. Readers can build and run them using our Makefile ("make test") or using ocamlc.
