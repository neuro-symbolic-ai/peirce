theory clinical_66_1
imports Main


begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  ActivatingPIK3CA :: "event ⇒ bool"
  Mutation :: "event ⇒ bool"
  HER2Negative :: "event ⇒ bool"
  HRPositive :: "event ⇒ bool"
  Patients :: "entity ⇒ bool"
  LessSensitive :: "event ⇒ bool"
  ToChemotherapy :: "event ⇒ bool"
  Worse :: "event ⇒ bool"
  OverallSurvival :: "event ⇒ bool"
  PIK3CA :: "event ⇒ bool"

(* Explanation 1: Patient likely has activating PIK3CA mutation, is HER2 negative and HR positive. *)
axiomatization where
  explanation_1: "∃x e1 e2 e3. Patient x ∧ ActivatingPIK3CA e1 ∧ Mutation e1 ∧ HER2Negative e2 ∧ HRPositive e3"

(* Explanation 2: Patients with HR+/Her2- mBC and PIK3CA mutation were less sensitive to chemotherapy and presented worse overall survival. *)
axiomatization where
  explanation_2: "∃x y e1 e2 e3 e4. Patients x ∧ HRPositive y ∧ HER2Negative y ∧ Mutation e1 ∧ PIK3CA e1 ∧ LessSensitive e2 ∧ ToChemotherapy e2 ∧ Worse e3 ∧ OverallSurvival e4"


theorem hypothesis:
 assumes asm: "Patient x"
  (* Hypothesis: Patient is likely less sensitive to chemotherapy. *)
 shows "∃x e. Patient x ∧ LessSensitive e ∧ ToChemotherapy e"
  using assms explanation_2 by blast
  

end
