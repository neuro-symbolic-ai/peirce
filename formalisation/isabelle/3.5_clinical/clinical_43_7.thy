theory clinical_43_7
imports Main


begin

typedecl entity
typedecl event

consts
  ClinicalTrial :: "entity ⇒ bool"
  NCT03568656 :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  CBP :: "entity ⇒ bool"
  EligibilityCriteria :: "event ⇒ bool"
  MutationArm :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  AsEligibilityCriteriaFor :: "entity ⇒ event ⇒ bool"
  AnotherNameFor :: "entity ⇒ entity ⇒ bool"
  CREBBP :: "entity ⇒ entity"

(* Explanation 1: Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm *)
axiomatization where
  explanation_1: "∃x y z e. ClinicalTrial x ∧ NCT03568656 x ∧ Mutation y ∧ CBP z ∧ EligibilityCriteria e ∧ MutationArm e ∧ In x y ∧ AsEligibilityCriteriaFor x e"

(* Explanation 2: CBP is another name for CREBBP *)
axiomatization where
  explanation_2: "∀x. CBP x ⟶ AnotherNameFor x (CREBBP x)"


theorem hypothesis:
 assumes asm: "ClinicalTrial x ∧ Mutation y ∧ CBP z"
  (* Hypothesis: NCT03568656 targets CREBBP *)
 shows "∃x y. NCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y"
  sledgehammer
  oops

end
