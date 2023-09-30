(lang dune 2.9)

(name SELinuxCILSem)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Lorenzo Ceragioli")

(maintainers "Lorenzo Ceragioli")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name SELinuxCILSem)
 (synopsis "Executable Semantics for SELinux CIL configuration Language")
 (description "We define a parser and an executable semantics for the SELinux CIL configuration Language")
 (depends 
  ocaml 
  dune
  ocamllex
  ocamlyacc
  )
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
