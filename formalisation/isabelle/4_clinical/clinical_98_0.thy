theory clinical_98_0
imports Main

begin

typedecl entity
typedecl event

consts
  MutationLocus :: "entity ⇒ bool"
  Common :: "entity ⇒ bool"
  Codon :: "entity ⇒ bool"
  Exon :: "entity ⇒ bool"
  BRAF_Gene :: "entity ⇒ bool"
  Found :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  BRAF :: "entity ⇒ bool"
  Division :: "entity ⇒ bool"
  Differentiation :: "entity ⇒ bool"
  Secretion :: "entity ⇒ bool"
  Affect :: "event ⇒ bool"
  BRAF_mutV600E :: "entity ⇒ bool"
  Hyperactivation :: "entity ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  Survival :: "entity ⇒ bool"
  Transformation :: "entity ⇒ bool"
  Cause :: "event ⇒ bool"
  BRAF_V600E :: "entity ⇒ bool"
  BRAF_Mutation :: "entity ⇒ bool"
  Result :: "event ⇒ bool"

(* Explanation 1: The most common mutation locus is found in codon 600 of exon 15 (V600E) of the BRAF gene. *)
axiomatization where
  explanation_1: "∃x y z e. MutationLocus x ∧ Common x ∧ Codon y ∧ Exon z ∧ BRAF_Gene z ∧ Found e ∧ Agent e x ∧ Patient e y ∧ In y z"

(* Explanation 2: A mutation in BRAF affects cell division, differentiation and secretion. *)
axiomatization where
  explanation_2: "∃x y z w e. Mutation x ∧ BRAF y ∧ Division z ∧ Differentiation w ∧ Secretion w ∧ Affect e ∧ Agent e x ∧ Patient e z ∧ Patient e w"

(* Explanation 3: BRAF mutV600E [causes] constitutive hyperactivation, proliferation, differentiation, survival, and oncogenic transformation. *)
axiomatization where
  explanation_3: "∃x y z w v u e1. BRAF_mutV600E x ∧ Hyperactivation y ∧ Proliferation z ∧ Differentiation w ∧ Survival v ∧ Transformation u ∧ Cause e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Patient e1 z ∧ Patient e1 w ∧ Patient e1 v ∧ Patient e1 u"

theorem hypothesis:
  assumes asm: "BRAF_V600E x ∧ BRAF_Mutation y"
  (* Hypothesis: BRAF V600E is the most common BRAF mutation and results in constitutive hyperactivation and oncogenic transformation. *)
  shows "∀x y e1 e2. BRAF_V600E x ∧ BRAF_Mutation y ⟶ (Common y ∧ Result e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Hyperactivation e2 ∧ Transformation e2 ∧ Agent e2 x)"
  sledgehammer
  oops

end
