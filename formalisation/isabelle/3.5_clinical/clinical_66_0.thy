theory clinical_66_0
imports Main

begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  PIK3CA :: "entity ⇒ bool"
  Activating :: "entity ⇒ bool"
  HER2Negative :: "entity ⇒ bool"
  HRPositive :: "entity ⇒ bool"
  Patients :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  LessSensitive :: "event ⇒ bool"
  WorseSurvival :: "event ⇒ bool"
  With :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Patient likely has activating PIK3CA mutation, is HER2 negative and HR positive. *)
axiomatization where
  explanation_1: "∃x y. Patient x ∧ PIK3CA y ∧ Activating y ∧ HER2Negative x ∧ HRPositive x"

(* Explanation 2: Patients with HR+/Her2- mBC and PIK3CA mutation were less sensitive to chemotherapy and presented worse overall survival. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. Patients x ∧ HRPositive x ∧ HER2Negative x ∧ PIK3CA y ∧ Mutation y ∧ LessSensitive e1 ∧ WorseSurvival e2 ∧ With x y ∧ With x z"

theorem hypothesis:
  assumes asm: "Patient x ∧ Chemotherapy y"
  (* Hypothesis: Patient is likely less sensitive to chemotherapy. *)
  shows "∃x y. Patient x ∧ Chemotherapy y ∧ LessSensitive x y"
  sledgehammer
  oops

end
