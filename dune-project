(lang dune 2.5)
(name duet)
(using menhir 2.0)
(generate_opam_files true)

(package
  (name duet)
  (synopsis "Duet")
  (version ~dev)
  (license MIT)
  (description "Duet static analyzer.")
  (homepage https://github.com/zkincaid/duet)
  (depends
    batteries
    ppx_deriving
    mlgmpidl
    camlidl
    apron
    z3
    ntl
    ocamlgraph))

(package
  (name pa)
  (synopsis "Predicate Automata library")
  (license MIT))
