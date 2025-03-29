theory clinical_66_1
imports Main

begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  Likely :: "entity ⇒ bool"
  PIK3CAMutation :: "entity ⇒ bool"
  Has :: "entity ⇒ entity ⇒ bool"
  HER2Negative :: "entity ⇒ bool"
  HRPositive :: "entity ⇒ bool"
  Patients :: "entity ⇒ bool"
  mBC :: "entity ⇒ bool"
  LessSensitiveTo :: "entity ⇒ entity ⇒ bool"
  Chemotherapy :: "entity ⇒ bool"
  OverallSurvival :: "entity ⇒ bool"
  Worse :: "entity ⇒ bool"
  Presented :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  PatientEvent :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Patient likely has activating PIK3CA mutation, is HER2 negative and HR positive. *)
axiomatization where
  explanation_1: "∃x y. Patient x ∧ Likely x ∧ PIK3CAMutation y ∧ Has x y ∧ HER2Negative x ∧ HRPositive x"

(* Explanation 2: Patients with HR+/Her2- mBC and PIK3CA mutation were less sensitive to chemotherapy and presented worse overall survival. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. Patients x ∧ HRPositive x ∧ HER2Negative x ∧ mBC x ∧ PIK3CAMutation y ∧ LessSensitiveTo x y ∧ Chemotherapy y ∧ OverallSurvival z ∧ Worse z ∧ Presented e1 ∧ Agent e1 x ∧ PatientEvent e1 z"

theorem hypothesis:
  assumes asm: "Patient x ∧ Likely x"
  (* Hypothesis: Patient is likely less sensitive to chemotherapy. *)
  shows "∃x. Patient x ∧ Likely x ∧ LessSensitiveTo x Chemotherapy"
  sledgehammer
  oops

end
