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

The `test` directory contains the source code for testing our semantics with both hand-crafted and random CIL configurations.

Since the tests compare our semantics with the behaviour of the CIL compiler, you need secilc (for compiling CIL configurations) and sesearch (for inspecting the compiled file) to be installed in your system.

To test the paper semantics with the hand-crafted configurations contained in the directory `testCases`, run
```
dune exec testCILSem
```

To test the efficent implementation of our semantics with the hand-crafted configurations contained in the directory `testCases`, run
```
dune exec testCILSemE
```

To test the paper semantics with some randomly generate tests use
```
dune exec testCILSemRand <max-declaration-num> <max-commands-num> <max-names-num> <config-num> 
```
Where
 - `max-declaration-num` : the test will generate configurations with number of declarations from 1 to max-declaration-num
 - `max-commands-num` : the test will generate configurations with number of commands from 1 to max-commands-num
 - `max-names-num` : the test will generate configurations with number of different names from 1 to max-name-num
 - `config-num` : for each combination in the ranges above, the test will generate config-num configurations

For all tests, the results are displayed on screen, and for each configuration a file .diff will be created in the same directory with the differences between our semantics and the compiler behaviour.
Automatically generated configurations can be found inside the folder `GeneratedTestCases` (that is created when running `testCILSemRand`).

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
   testCILSemRand.ml           <-- for testing the paper semantics with generated configurations
   testCILSem.ml               <-- for testing the paper semantics with the configurations in the test-cases directory
   testCILSemE.ml              <-- for testing the efficient semantics with the configurations in the test-cases directory

testCases/                     <-- directory with hand-crafted intricate CIL configurations

```
