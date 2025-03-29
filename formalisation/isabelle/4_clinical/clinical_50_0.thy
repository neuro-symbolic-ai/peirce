theory clinical_50_0
imports Main

begin

typedecl entity
typedecl event

consts
  Inhibit :: "event ⇒ bool"
  PARP :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Accumulation :: "event ⇒ bool"
  SSBreaks :: "event ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  Involved :: "event ⇒ bool"
  Recognition :: "event ⇒ bool"
  Repair :: "event ⇒ bool"
  DNADamage :: "event ⇒ bool"
  SSRepair :: "event ⇒ bool"
  Patient :: "event ⇒ event ⇒ bool"

(* Explanation 1: Inhibiting PARP results in accumulation of SS breaks *)
axiomatization where
  explanation_1: "∀x e1 e2. Inhibit e1 ∧ PARP x ∧ Agent e1 x ⟶ Accumulation e2 ∧ SSBreaks e2"

(* Explanation 2: PARP1 is involved in the recognition and repair of DNA damage in SS DNA damage repair *)
axiomatization where
  explanation_2: "∀x e1 e2 e3. PARP1 x ∧ Involved e1 ∧ Recognition e2 ∧ Repair e3 ∧ DNADamage e2 ∧ SSRepair e3 ∧ Agent e1 x ∧ Patient e1 e2 ∧ Patient e1 e3"

theorem hypothesis:
  assumes asm: "Inhibit e1 ∧ PARP x ∧ Agent e1 x"
  (* Hypothesis: Inhibiting PARP results in accumulation of SS breaks *)
  shows "∃x e1 e2. Inhibit e1 ∧ PARP x ∧ Agent e1 x ⟶ Accumulation e2 ∧ SSBreaks e2"
  using explanation_1 by blast
  

end
