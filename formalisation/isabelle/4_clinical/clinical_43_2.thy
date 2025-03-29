theory clinical_43_2
imports Main

begin

typedecl entity
typedecl event

consts
  ClinicalTrial :: "entity ⇒ bool"
  NCT03568656 :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  CBP :: "entity ⇒ bool"
  CREBBP :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Has :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  EligibilityCriteriaFor :: "entity ⇒ entity ⇒ bool"
  MutationArm :: "entity"
  AnotherNameFor :: "entity ⇒ entity ⇒ bool"
  Gene :: "entity ⇒ bool"
  EligibilityCriterionFor :: "entity ⇒ entity ⇒ bool"
  Targets :: "event ⇒ bool"

(* Explanation 1: Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm *)
axiomatization where
  explanation_1: "∃x y z e. ClinicalTrial x ∧ NCT03568656 x ∧ Mutation y ∧ CBP z ∧ In y z ∧ Has e ∧ Agent e x ∧ Patient e y ∧ EligibilityCriteriaFor y MutationArm"

(* Explanation 2: CBP is another name for CREBBP *)
axiomatization where
  explanation_2: "∀x y. CBP x ∧ CREBBP y ⟶ AnotherNameFor x y"

(* Explanation 3: If a clinical trial has a mutation in a gene as an eligibility criterion, then the trial targets that gene *)
axiomatization where
  explanation_3: "∀x y z e1 e2. ClinicalTrial x ∧ Mutation y ∧ Gene z ∧ In y z ∧ Has e1 ∧ Agent e1 x ∧ Patient e1 y ∧ EligibilityCriterionFor y x ⟶ (Targets e2 ∧ Agent e2 x ∧ Patient e2 z)"

(* Explanation 4: If CBP is another name for CREBBP, then a clinical trial with a mutation in CBP as an eligibility criterion targets CREBBP *)
axiomatization where
  explanation_4: "∀x y z e1 e2. (CBP x ∧ CREBBP y ⟶ AnotherNameFor x y) ⟶ (ClinicalTrial z ∧ Mutation e1 ∧ In e1 x ∧ EligibilityCriterionFor e1 z ⟶ (Targets e2 ∧ Agent e2 z ∧ Patient e2 y))"

theorem hypothesis:
  assumes asm: "NCT03568656 x ∧ CREBBP y"
  (* Hypothesis: NCT03568656 targets CREBBP *)
  shows "∃x y e. NCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y"
proof -
  (* From the known information, we have NCT03568656 x and CREBBP y. *)
  from asm have "NCT03568656 x ∧ CREBBP y" by simp
  (* Explanation 1 provides that Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm. *)
  (* This is equivalent to a clinical trial having a mutation in a gene as an eligibility criterion (C). *)
  from explanation_1 have "∃x y z e. ClinicalTrial x ∧ NCT03568656 x ∧ Mutation y ∧ CBP z ∧ In y z ∧ Has e ∧ Agent e x ∧ Patient e y ∧ EligibilityCriteriaFor y MutationArm" by blast
  (* Explanation 2 states that CBP is another name for CREBBP. *)
  from explanation_2 have "∀x y. CBP x ∧ CREBBP y ⟶ AnotherNameFor x y" by blast
  (* Explanation 4 states that if CBP is another name for CREBBP, then a clinical trial with a mutation in CBP as an eligibility criterion targets CREBBP. *)
  from explanation_4 have "∀x y z e1 e2. (CBP x ∧ CREBBP y ⟶ AnotherNameFor x y) ⟶ (ClinicalTrial z ∧ Mutation e1 ∧ In e1 x ∧ EligibilityCriterionFor e1 z ⟶ (Targets e2 ∧ Agent e2 z ∧ Patient e2 y))" by blast
  (* Using the logical relation Implies(B, E), we can infer that a clinical trial with a mutation in CBP as an eligibility criterion targets CREBBP. *)
  then have "∃x y e. NCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y" sledgehammer
  then show ?thesis <ATP>
qed

end
