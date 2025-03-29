theory clinical_8_0
imports Main

begin

typedecl entity
typedecl event

consts
  Inhibit :: "event ⇒ bool"
  PARP :: "entity ⇒ bool"
  Accumulation :: "event ⇒ bool"
  Breaks :: "entity ⇒ bool"
  SingleStrand :: "entity ⇒ bool"
  Result :: "event ⇒ event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  Recognition :: "event ⇒ bool"
  Repair :: "event ⇒ bool"
  Damage :: "entity ⇒ bool"
  DNA :: "entity ⇒ bool"
  Involved :: "event ⇒ bool"
  RepairIn :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Inhibiting PARP results in accumulation of single strand breaks. *)
axiomatization where
  explanation_1: "∀x y e1 e2. Inhibit e1 ∧ PARP x ∧ Agent e1 x ∧ Accumulation e2 ∧ Breaks y ∧ SingleStrand y ∧ Patient e2 y ⟶ Result e1 e2"

(* Explanation 2: PARP1 is involved in the recognition and repair of DNA damage in single strand DNA damage repair. *)
axiomatization where
  explanation_2: "∀x y z e1 e2 e3. PARP1 x ∧ Recognition e1 ∧ Repair e2 ∧ Damage y ∧ DNA y ∧ SingleStrand z ∧ Involved e3 ∧ Agent e3 x ∧ Patient e1 y ∧ Patient e2 y ∧ RepairIn e2 z"

theorem hypothesis:
  assumes asm: "Inhibit e1 ∧ PARP x ∧ Accumulation e2 ∧ Breaks y ∧ SingleStrand y"
  (* Hypothesis: Inhibiting PARP results in accumulation of single strand breaks. *)
  shows "∀x y e1 e2. Inhibit e1 ∧ PARP x ∧ Agent e1 x ∧ Accumulation e2 ∧ Breaks y ∧ SingleStrand y ∧ Patient e2 y ⟶ Result e1 e2"
  using explanation_1 by blast
  

end
