theory clinical_19_3
imports Main

begin

typedecl entity
typedecl event

consts
  Dasatinib :: "entity ⇒ bool"
  Licensed :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  UseIn :: "event ⇒ entity ⇒ bool"
  ChronicMyeloidLeukaemia :: "entity ⇒ bool"
  RelapsedAcuteLymphoblasticLeukaemia :: "entity ⇒ bool"
  Effective :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Treating :: "event ⇒ entity ⇒ bool"
  Condition :: "entity ⇒ bool"
  Used :: "event ⇒ bool"
  Accessed :: "event ⇒ bool"
  OffLicence :: "event ⇒ bool"

(* Explanation 1: Dasatinib is licensed for use in chronic myeloid leukaemia or relapsed acute lymphoblastic leukaemia. *)
axiomatization where
  explanation_1: "∃x y e. Dasatinib x ∧ Licensed e ∧ Patient e x ∧ (UseIn e y ∧ (ChronicMyeloidLeukaemia y ∨ RelapsedAcuteLymphoblasticLeukaemia y))"

(* Explanation 2: Dasatinib may be effective in treating this patient. *)
axiomatization where
  explanation_2: "∃x y e. Dasatinib x ∧ Patient e y ∧ Effective e ∧ Agent e x ∧ Treating e y"

(* Explanation 3: If Dasatinib is used for conditions other than chronic myeloid leukaemia or relapsed acute lymphoblastic leukaemia, it will need to be accessed off licence. *)
axiomatization where
  explanation_3: "∀x y e1 e2. Dasatinib x ∧ Condition y ∧ Used e1 ∧ Agent e1 x ∧ Patient e1 y ∧ ¬(ChronicMyeloidLeukaemia y ∨ RelapsedAcuteLymphoblasticLeukaemia y) ⟶ (Accessed e2 ∧ Patient e2 x ∧ OffLicence e2)"

(* Explanation 4: There are conditions for which Dasatinib is not licensed, and if used for such conditions, it must be accessed off licence. *)
axiomatization where
  explanation_4: "∃x y e1 e2. Condition y ∧ Dasatinib x ∧ ¬Licensed e1 ∧ Patient e1 x ∧ Used e2 ∧ Agent e2 x ∧ Patient e2 y ⟶ (Accessed e2 ∧ OffLicence e2)"

(* Explanation 5: Dasatinib is being used for a condition that is not chronic myeloid leukaemia or relapsed acute lymphoblastic leukaemia. *)
axiomatization where
  explanation_5: "∃x y e. Dasatinib x ∧ Condition y ∧ Used e ∧ Agent e x ∧ Patient e y ∧ ¬(ChronicMyeloidLeukaemia y ∨ RelapsedAcuteLymphoblasticLeukaemia y)"

theorem hypothesis:
  assumes asm: "Dasatinib x"
  (* Hypothesis: Dasatinib will need to be accessed off licence. *)
  shows "∃x e. Dasatinib x ∧ Accessed e ∧ Patient e x ∧ OffLicence e"
  using explanation_3 explanation_5 by blast
  

end
