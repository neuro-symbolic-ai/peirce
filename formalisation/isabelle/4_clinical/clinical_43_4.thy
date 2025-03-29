theory clinical_43_4
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
  Gene :: "entity ⇒ bool"
  Has :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  EligibilityCriterion :: "entity ⇒ bool"
  Targets :: "event ⇒ bool"
  AnotherNameFor :: "entity ⇒ entity ⇒ bool"
  Directly :: "event ⇒ bool"

(* Explanation 1: Clinical Trial NCT03568656 has a mutation in CBP as an eligibility criterion for the mutation arm *)
axiomatization where
  explanation_1: "∃x y z e. ClinicalTrial x ∧ NCT03568656 x ∧ Mutation y ∧ CBP z ∧ Has e ∧ Agent e x ∧ Patient e y ∧ In y z ∧ EligibilityCriterion y"

(* Explanation 2: CBP is another name for CREBBP *)
axiomatization where
  explanation_2: "∀x y. CBP x ∧ CREBBP y ⟶ AnotherNameFor x y"

(* Explanation 3: If a clinical trial has a mutation in a gene as an eligibility criterion, then the trial targets that gene *)
axiomatization where
  explanation_3: "∀x y z e1 e2. ClinicalTrial x ∧ Mutation y ∧ Gene z ∧ Has e1 ∧ Agent e1 x ∧ Patient e1 y ∧ In y z ∧ EligibilityCriterion y ⟶ (Targets e2 ∧ Agent e2 x ∧ Patient e2 z)"

(* Explanation 4: If CBP is another name for CREBBP, then any clinical trial with a mutation in CBP as an eligibility criterion directly targets CREBBP *)
axiomatization where
  explanation_4: "∀x y z e1 e2. (CBP x ∧ CREBBP y ⟶ AnotherNameFor x y) ⟶ (ClinicalTrial z ∧ Mutation e1 ∧ In e1 x ∧ EligibilityCriterion e1 ⟶ (Targets e2 ∧ Agent e2 z ∧ Patient e2 y ∧ Directly e2))"

theorem hypothesis:
  assumes asm: "NCT03568656 x ∧ CREBBP y"
  (* Hypothesis: NCT03568656 targets CREBBP *)
  shows "∃x y e. NCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y"
  using assms explanation_1 explanation_2 explanation_4 by blast
  

end
