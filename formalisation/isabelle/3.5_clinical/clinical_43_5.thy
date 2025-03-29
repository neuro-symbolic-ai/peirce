theory clinical_43_5
imports Main


begin

typedecl entity
typedecl event

consts
  ClinicalTrialNCT03568656 :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  CBP :: "entity ⇒ bool"
  In :: "event ⇒ bool"
  Possession :: "event ⇒ entity ⇒ entity ⇒ bool"
  AsEligibilityCriteriaFor :: "event ⇒ entity ⇒ entity ⇒ bool"
  AnotherNameFor :: "entity ⇒ entity ⇒ bool"
  CREBBP :: "entity"

(* Explanation 1: Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm *)
axiomatization where
  explanation_1: "∃x y z e. ClinicalTrialNCT03568656 x ∧ Mutation y ∧ CBP z ∧ In e ∧ Possession e x y ∧ AsEligibilityCriteriaFor e y z"

(* Explanation 2: CBP is another name for CREBBP *)
axiomatization where
  explanation_2: "∀x. CBP x ⟶ AnotherNameFor x CREBBP"


theorem hypothesis:
 assumes asm: "ClinicalTrialNCT03568656 x ∧ CBP y"
  (* Hypothesis: NCT03568656 targets CREBBP *)
 shows "∃x y e. ClinicalTrialNCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y"
  sledgehammer
  oops

end
