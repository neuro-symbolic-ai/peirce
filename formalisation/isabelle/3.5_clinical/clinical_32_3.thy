theory clinical_32_3
imports Main

begin

typedecl entity
typedecl event

consts
  NotchInhibitor :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  Effective :: "event ⇒ bool"
  Involving :: "event ⇒ entity ⇒ bool"
  NotAvailable :: "event ⇒ bool"
  For :: "event ⇒ entity ⇒ entity ⇒ bool"
  NoLicensed :: "event ⇒ bool"
  Inhibitors :: "entity ⇒ bool"
  Available :: "event ⇒ bool"
  In :: "event ⇒ entity ⇒ bool"
  ClinicalTrials :: "entity"
  No :: "entity ⇒ bool"
  PediatricPatients :: "entity"
  Treatment :: "entity ⇒ bool"

(* Explanation 1: If a Notch inhibitor may be effective in a patient, then the treatment involving the Notch inhibitor is not available for that patient. *)
axiomatization where
  explanation_1: "∀x y e1 e2. NotchInhibitor x ∧ Patient y ∧ Effective e1 ∧ Involving e1 x ∧ NotAvailable e2 ∧ For e2 x y"

(* Explanation 2: If a Notch inhibitor may be effective in a patient, then there are no licensed Notch inhibitors available. *)
axiomatization where
  explanation_2: "∀x y e1 e2. NotchInhibitor x ∧ Patient y ∧ Effective e1 ∧ NoLicensed e1 ∧ Inhibitors x ∧ Available e2"

(* Explanation 3: If a Notch inhibitor may be effective in a patient, then there are no Notch inhibitors in clinical trials available for pediatric patients. *)
axiomatization where
  explanation_3: "∀x y e1 e2. NotchInhibitor x ∧ Patient y ∧ Effective e1 ∧ In e1 ClinicalTrials ∧ No x ∧ Inhibitors x ∧ Available e2 ∧ For e2 x PediatricPatients"

theorem hypothesis:
  assumes asm: "Treatment x ∧ Patient y"
  (* Hypothesis: This treatment is not available for this patient. *)
  shows "∃x y e. Treatment x ∧ Patient y ∧ NotAvailable e ∧ For e x y"
  using assms explanation_1 by blast
  

end
