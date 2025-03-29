theory clinical_43_1
imports Main

begin

typedecl entity
typedecl event

consts
  ClinicalTrial :: "entity ⇒ bool"
  NCT03568656 :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  CBP :: "entity ⇒ bool"
  Has :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  EligibilityCriteria :: "event ⇒ bool"
  CREBBP :: "entity ⇒ bool"
  AnotherNameFor :: "entity ⇒ entity ⇒ bool"
  Gene :: "entity ⇒ bool"
  EligibilityCriterion :: "event ⇒ bool"
  Targets :: "event ⇒ bool"

(* Explanation 1: Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm *)
axiomatization where
  explanation_1: "∃x y z e. ClinicalTrial x ∧ NCT03568656 x ∧ Mutation y ∧ CBP z ∧ Has e ∧ Agent e x ∧ Patient e y ∧ In y z ∧ EligibilityCriteria e"

(* Explanation 2: CBP is another name for CREBBP *)
axiomatization where
  explanation_2: "∀x y. CBP x ∧ CREBBP y ⟶ AnotherNameFor x y"

(* Explanation 3: If a clinical trial has a mutation in a gene as an eligibility criterion, then the trial targets that gene *)
axiomatization where
  explanation_3: "∀x y z e1 e2. ClinicalTrial x ∧ Mutation y ∧ Gene z ∧ Has e1 ∧ Agent e1 x ∧ Patient e1 y ∧ In y z ∧ EligibilityCriterion e1 ⟶ (Targets e2 ∧ Agent e2 x ∧ Patient e2 z)"

theorem hypothesis:
  assumes asm: "NCT03568656 x ∧ CREBBP y"
  (* Hypothesis: NCT03568656 targets CREBBP *)
  shows "∃x y e. NCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y"
proof -
  (* From the known information, we have NCT03568656 x and CREBBP y. *)
  from asm have "NCT03568656 x ∧ CREBBP y" by simp
  (* Explanation 1 provides that Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm. *)
  (* Explanation 2 states that CBP is another name for CREBBP. *)
  (* Explanation 3 states that if a clinical trial has a mutation in a gene as an eligibility criterion, then the trial targets that gene. *)
  (* We have a logical relation Implies(A, D), which means if Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm, then the trial targets that gene. *)
  (* Since CBP is another name for CREBBP, we can substitute CREBBP for CBP in the context of targeting. *)
  from explanation_1 have "∃e. Targets e ∧ Agent e x ∧ Patient e y" sledgehammer
  then show ?thesis <ATP>
qed

end
