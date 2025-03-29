theory clinical_19_8
imports Main


begin

typedecl entity
typedecl event

consts
  Dasatinib :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  Effective :: "event ⇒ bool"
  Treat :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Need :: "event ⇒ bool"
  Will :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  OffLicence :: "event ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"

(* Explanation 1: If Dasatinib is effective in treating a specific patient, then it will need to be accessed off licence for that patient. *)
axiomatization where
  explanation_1: "∀x y e1 e2. Dasatinib x ∧ Patient y ∧ Effective e1 ∧ Treat e1 ∧ Agent e1 x ∧ Patient y ⟶ (Need e2 ∧ Will e2 ∧ Access e2 ∧ OffLicence e2 ∧ For e2 y)"


theorem hypothesis:
 assumes asm: "Dasatinib x ∧ Patient y ∧ Effective e1 ∧ Treat e1 ∧ Agent e1 x ∧ Patient y"
  (* Hypothesis: Dasatinib will need to be accessed off licence. *)
 shows "∃e. Need e ∧ Will e ∧ Access e ∧ OffLicence e ∧ For e Dasatinib"
  sledgehammer
  oops

end
