theory clinical_32_2
imports Main

begin

typedecl entity
typedecl event

consts
  NotchInhibitor :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  EffectiveIn :: "entity ⇒ entity ⇒ bool"
  LicencedNotchInhibitor :: "entity ⇒ bool"
  Available :: "entity ⇒ bool"
  ClinicalTrial :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  AvailableFor :: "entity ⇒ entity ⇒ bool"
  HepatoblastomaPatients :: "entity ⇒ bool"
  PaediatricPatients :: "entity ⇒ bool"
  Treatment :: "entity ⇒ bool"

(* Explanation 1: A Notch inhibitor may be effective in this patient. *)
axiomatization where
  explanation_1: "∃x y. NotchInhibitor x ∧ Patient y ∧ EffectiveIn x y"

(* Explanation 2: There are no licenced Notch inhibitors available. *)
axiomatization where
  explanation_2: "¬(∃x. LicencedNotchInhibitor x ∧ Available x)"

(* Explanation 3: If there are no licenced Notch inhibitors available, then there are no available Notch inhibitors. *)
axiomatization where
  explanation_3: "(¬(∃x. LicencedNotchInhibitor x ∧ Available x)) ⟶ (¬(∃y. NotchInhibitor y ∧ Available y))"

(* Explanation 4: There are no Notch inhibitors in clinical trials available for hepatoblastoma patients. *)
axiomatization where
  explanation_4: "¬(∃x y z. NotchInhibitor x ∧ ClinicalTrial y ∧ In x y ∧ AvailableFor x z ∧ HepatoblastomaPatients z)"

(* Explanation 5: There are no Notch inhibitors in clinical trials available for paediatric patients. *)
axiomatization where
  explanation_5: "¬(∃x y z. NotchInhibitor x ∧ ClinicalTrial y ∧ In x y ∧ AvailableFor x z ∧ PaediatricPatients z)"

(* Explanation 6: If there are no available Notch inhibitors, then the treatment is not available for the patient. *)
axiomatization where
  explanation_6: "(¬(∃x. NotchInhibitor x ∧ Available x)) ⟶ (∀y z. Treatment y ∧ Patient z ⟶ ¬AvailableFor y z)"

theorem hypothesis:
  assumes asm: "Treatment x ∧ Patient y"
  (* Hypothesis: This treatment is not available for this patient. *)
  shows "∀x y. Treatment x ∧ Patient y ⟶ ¬AvailableFor x y"
  using explanation_2 explanation_3 explanation_6 by blast
  

end
