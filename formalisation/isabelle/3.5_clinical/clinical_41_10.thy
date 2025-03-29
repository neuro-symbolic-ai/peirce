theory clinical_41_10
imports Main


begin

typedecl entity
typedecl event

consts
  NCT03568656 :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  Relevant :: "entity ⇒ entity ⇒ bool"
  Patients :: "entity ⇒ bool"
  AdvancedSolidTumours :: "entity ⇒ bool"
  Available :: "entity ⇒ entity ⇒ bool"
  SoftTissueSarcoma :: "entity ⇒ bool"
  Has :: "entity ⇒ entity ⇒ bool"
  Eligible :: "entity ⇒ bool"
  For :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: NCT03568656 might be relevant for this patient *)
axiomatization where
  explanation_1: "∀x y. NCT03568656 x ∧ Patient y ∧ Relevant x y"

(* Explanation 2: NCT03568656 is available for patients with advanced solid tumours *)
axiomatization where
  explanation_2: "∀x y. NCT03568656 x ∧ Patients y ∧ AdvancedSolidTumours y ⟶ Available x y"

(* Explanation 3: Patient has soft tissue sarcoma *)
axiomatization where
  explanation_3: "∃x y. Patient x ∧ SoftTissueSarcoma y ∧ Has x y"


theorem hypothesis:
 assumes asm: "Patient x"
  (* Hypothesis: Patient may be eligible for NCT03568656 *)
 shows "∃x e. Patient x ∧ Eligible e ∧ For e NCT03568656"
  sledgehammer
  oops

end
