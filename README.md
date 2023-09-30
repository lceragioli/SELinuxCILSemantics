# SELinuxCILSemantics
An executable semantics for SELinux's CIL configuration language

### Requirements

Ocaml, Ocamllex, Ocamlyacc >= 4.12.0
Dune >= 3.8.1

### Overview

We give an executable semantics for SELinux's CIL configuration language. More in detail, we give a pair of implementations: a first simple one which is a direct encoding of the one presented in the paper [toappear], and a second more efficient implementation.

- CILsemantics.mli : computes our paper semantics
- CILsemanticsE.mli : returns the same result but is implemented with tail recursion

### Compilation

To compile run
```
dune build
```
Depending on you system, you may need to run the following before compiling to use the correct version of ocaml

```
opam switch 4.12.0
eval $(opam env)
```

### How to use our semantics

Just clone this repo and use our module as a library, an example of usage is our executable ComputeSem.ml wich just print the permissions of a given configuration (as secilc and sesearch --allow whould do).
```
 let config = SELinuxCILSem.CILsyntax.removeIN (SELinuxCILSem.CILparser.main SELinuxCILSem.CILlexer.token lexbuf) in
 let semantics = SELinuxCILSem.CILsemanticsE.get_semantics (config)
```

### Tests

The `test` directory contains both hand-crafted and real-world examples of CIL configurations, as well as a generator for random CIL configurations.

To performs all the tests run the following
```
dune test
```
If you want to change the tests you can:

 - edit, add or remove test cases from the directory "test/test-cases". and/or
 - change the parameters for generating random configurations at the beginning of "test/testCILsem.ml"

### Project structure

Here is a description of content of the repository

```
README.md                      <-- This file
dune                           <-- dune configuration file
dune-project                   <-- dune configuration file

bin/                           <-- directory for applications using our semantics which comes as a library
   computeSem                  <-- our example application that just prints the allows of a configuration
   dune                        <-- dune configuration file

lib/                           <-- our SELinux CIL library
   CILlexer.mll                <-- specification file for ocamllex
   CILparser.mly               <-- specification file for ocamlyacc
   CILsyntax.ml - .mli         <-- module for abstract syntax of CIL
   CILsyntaxE.ml - .mli        <-- module for an efficient representation of CIL configurations
   CILsemantics.ml - .mli      <-- module for CIL semantics as it is given in the paper
   CILsemanticsE.ml - .mli     <-- module for CIL semantics in a more efficient (tail recoursive) version
   CILclass.ml - .mli          <-- module with class and operations related functions
   CILenv.ml - .mli            <-- module for environment rho and frame fr
   CILenvE.ml - .mli           <-- module for an efficient representation of environment rho and frame fr
   Utils.ml                    <-- module with utilities data structures and functions 
   dune                        <-- dune configuration file
  
test/                          <-- files and code for testing
   dune                        <-- dune configuration file
   Generate.ml - .mli          <-- module for generating random CIL configurations
   testCILsem.ml               <-- for testing the paper semantics with generated configurations
   testCILsemInt.ml            <-- for testing the paper semantics with the configurations in the test-cases directory
   testCILsemIntE.ml           <-- for testing the efficient semantics with the configurations in the test-cases directory
   real-world/                 <-- directory with real-world configurations
   test-cases/                 <-- directory with hand-crafted intricate CIL configurations

```
