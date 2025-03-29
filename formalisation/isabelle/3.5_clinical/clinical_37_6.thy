theory clinical_37_6
imports Main


begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  Travel :: "event ⇒ bool"
  Have :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Event :: "entity ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"
  Treatment :: "entity ⇒ bool"
  MayNotSuitable :: "entity ⇒ bool"
  Reason :: "entity ⇒ bool"
  SuitableFor :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: If the patient has to travel for an event, then the treatment for that event may not be suitable *)
axiomatization where
  explanation_1: "∀x y z e1 e2 e3. Patient x ∧ Travel e1 ∧ Have e1 ∧ Agent e1 x ∧ Event y ∧ For e2 y ∧ Treatment z ∧ MayNotSuitable e3 ∧ Reason e3 ⟶ (SuitableFor z y ⟶ ¬SuitableFor z y)"

(* Explanation 2: If the patient has to travel for an event, then the event may not be suitable for the patient *)
axiomatization where
  explanation_2: "∀x y z e1 e2 e3. Patient x ∧ Travel e1 ∧ Have e1 ∧ Agent e1 x ∧ Event y ∧ For e2 y ∧ MayNotSuitable e3 ∧ Reason e3 ⟶ (SuitableFor y x ⟶ ¬SuitableFor y x)"


theorem hypothesis:
 assumes asm: "Patient x ∧ Travel e1 ∧ Have e1 ∧ Agent e1 x ∧ MayNotSuitable e2 ∧ Reason e2"
  (* Hypothesis: Patient will have to travel, may not be suitable *)
 shows "∃x e1 e2. Patient x ∧ Travel e1 ∧ Have e1 ∧ Agent e1 x ∧ MayNotSuitable e2 ∧ Reason e2"
  using assms by blast
  

end
