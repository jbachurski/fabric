(lang dune 3.16)

(using ctypes 0.3)

(name fabric)

(generate_opam_files true)

(source
 (github jbachurski/fabric))

(authors "Jakub Bachurski")

; (maintainers "")

; (license LICENSE)

; (documentation https://url/to/documentation)

(package
 (name fabric)
 (depends
  (ocaml
   (>= 5.0.0))
  dune
  (alcotest :with-test)
  core
  core_unix
  ctypes-foreign
  ppx_jane
  angstrom))

;  (synopsis "A short synopsis")
;  (description "A longer description")
;  (tags (topics "to describe" your project)
