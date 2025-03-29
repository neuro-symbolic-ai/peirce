theory clinical_66_3
imports Main

begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  PIK3CA :: "entity ⇒ bool"
  HER2Negative :: "entity ⇒ bool"
  HRPositive :: "entity ⇒ bool"
  Chemotherapy :: "entity ⇒ bool"
  Sensitive :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Cause :: "event ⇒ entity ⇒ bool"
  Likely :: "event ⇒ bool"
  Less :: "event ⇒ bool"
  mBC :: "entity ⇒ bool"
  Survival :: "entity ⇒ bool"
  Worse :: "entity ⇒ bool"
  Present :: "event ⇒ bool"

(* Explanation 1: Patients with an activating PIK3CA mutation, who are HER2 negative and HR positive, are likely less sensitive to chemotherapy. *)
axiomatization where
  explanation_1: "∃x y z e. Patient x ∧ Mutation y ∧ PIK3CA y ∧ HER2Negative x ∧ HRPositive x ∧ Chemotherapy z ∧ Sensitive e ∧ Agent e x ∧ Cause e z ∧ Likely e ∧ Less e"

(* Explanation 2: Patients with HR+/HER2- mBC and PIK3CA mutation were less sensitive to chemotherapy and presented worse overall survival. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. Patient x ∧ Mutation y ∧ PIK3CA y ∧ HRPositive x ∧ HER2Negative x ∧ mBC x ∧ Chemotherapy z ∧ Survival w ∧ Worse w ∧ Sensitive e1 ∧ Agent e1 x ∧ Cause e1 z ∧ Less e1 ∧ Present e2 ∧ Agent e2 x ∧ Cause e2 w"

theorem hypothesis:
  assumes asm: "Patient x ∧ Chemotherapy y"
  (* Hypothesis: Patient is likely less sensitive to chemotherapy. *)
  shows "∃x y e. Patient x ∧ Chemotherapy y ∧ Sensitive e ∧ Agent e x ∧ Cause e y ∧ Likely e ∧ Less e"
  using explanation_1 by blast
  

end
