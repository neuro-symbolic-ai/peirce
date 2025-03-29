theory clinical_98_10
imports Main


begin

typedecl entity
typedecl event

consts
  MutationLocus :: "entity ⇒ bool"
  Codon600 :: "entity ⇒ bool"
  Exon15 :: "entity ⇒ bool"
  BRAFGene :: "entity ⇒ bool"
  Equivalent :: "entity ⇒ entity ⇒ bool"
  BRAFV600E :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  Corresponds :: "entity ⇒ bool"
  FoundIn :: "entity ⇒ bool"
  Locus :: "entity ⇒ bool"

(* Explanation 1: The mutation locus found in codon 600 of exon 15 (V600E) of the BRAF gene is equivalent to the mutation BRAF V600E. *)
axiomatization where
  explanation_1: "∀x y. MutationLocus x ∧ Codon600 x ∧ Exon15 x ∧ BRAFGene y ∧ Equivalent x (BRAFV600E y)"

(* Explanation 2: If a mutation is BRAF V600E, then it corresponds to the mutation locus found in codon 600 of exon 15 of the BRAF gene. *)
axiomatization where
  explanation_2: "∀x y. Mutation x ∧ BRAFV600E x ⟶ (∃z. Corresponds z ∧ MutationLocus z ∧ Codon600 z ∧ Exon15 z ∧ BRAFGene z)"

(* Explanation 3: If a mutation is not found in the locus of codon 600 of exon 15 of the BRAF gene, then it is not the mutation BRAF V600E. *)
axiomatization where
  explanation_3: "∀x y. Mutation x ∧ ¬FoundIn x ∧ Locus x ∧ Codon600 x ∧ Exon15 x ∧ BRAFGene x ⟶ ¬BRAFV600E x"


theorem hypothesis:
 assumes asm: "BRAFV600E x ∧ Mutation y ∧ Common y x ∧ ResultsIn z ∧ Hyperactivation z ∧ Transformation z"
  (* Hypothesis: BRAF V600E is the most common BRAF mutation and results in constitutive hyperactivation and oncogenic transformation. *)
 shows "∃x y z. BRAFV600E x ∧ Mutation y ∧ Common y x ∧ ResultsIn z ∧ Hyperactivation z ∧ Transformation z"
proof -
  (* From the premise, we know that BRAF V600E is a mutation and it is common, results in hyperactivation and oncogenic transformation. *)
  from asm have "BRAFV600E x ∧ Mutation y ∧ Common y x ∧ ResultsIn z ∧ Hyperactivation z ∧ Transformation z" <ATP>
  (* There is a logical relation Implies(C, B), Implies(mutation is BRAF V600E, mutation BRAF V600E) *)
  (* We already have BRAFV600E x, so we can infer mutation locus found in codon 600 of exon 15 of the BRAF gene. *)
  then have "MutationLocus x ∧ Codon600 x ∧ Exon15 x ∧ BRAFGene x" for x <ATP>
  (* There is a logical relation Implies(C, A), Implies(mutation is BRAF V600E, mutation locus found in codon 600 of exon 15 of the BRAF gene) *)
  (* We already have BRAFV600E x, so we can infer mutation locus found in codon 600 of exon 15 of the BRAF gene. *)
  then have "MutationLocus x" for x <ATP>
  (* We have all the necessary conditions to satisfy the hypothesis. *)
  then show ?thesis <ATP>
qed

end
