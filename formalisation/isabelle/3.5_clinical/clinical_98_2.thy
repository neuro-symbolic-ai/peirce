theory clinical_98_2
imports Main


begin

typedecl entity
typedecl event

consts
  MutationLocus :: "entity ⇒ bool"
  Codon600 :: "entity ⇒ bool"
  Exon15 :: "entity ⇒ bool"
  V600E :: "entity ⇒ bool"
  BRAFGene :: "entity ⇒ bool"
  Corresponds :: "entity ⇒ entity ⇒ bool"
  BRAFV600E :: "entity"

(* Explanation 1: The mutation locus found in codon 600 of exon 15 (V600E) of the BRAF gene specifically corresponds to the mutation BRAF V600E *)
axiomatization where
  explanation_1: "∃x y. MutationLocus x ∧ Codon600 y ∧ Exon15 y ∧ V600E y ∧ BRAFGene x ∧ Corresponds x BRAFV600E"


theorem hypothesis:
 assumes asm: "MutationLocus x ∧ Codon600 y ∧ Exon15 y ∧ V600E y ∧ BRAFGene x ∧ Corresponds x BRAFV600E"
 (* Hypothesis: BRAF V600E is the most common BRAF mutation and results in constitutive hyperactivation and oncogenic transformation *)
 shows "∃x y z e. BRAFV600E x ∧ Mutation y ∧ Common z ∧ BRAFMutation x y ∧ ResultsIn e ∧ Patient e x ∧ Hyperactivation e ∧ Transformation e"
  sledgehammer
  oops

end
