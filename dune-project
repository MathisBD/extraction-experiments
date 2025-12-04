(lang dune 3.16)

(using coq 0.9)

(name extraction-experiments)

(generate_opam_files true)

(package
 (name extraction-experiments)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (synopsis "Extraction experiments")
 (depends
   (rocq-prover (= 9.0.0))
   pvec))
