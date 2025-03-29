theory clinical_12_1
imports Main

begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PAR :: "entity ⇒ bool"
  Synthesis :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  RepairProteins :: "entity ⇒ bool"
  DNA_Damage_Site :: "entity ⇒ bool"
  Recruit :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesis e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DNA_Damage_Site z ∧ Recruit e ∧ Agent e x ∧ Patient e y ∧ To y z"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PAR y ∧ RepairProteins z"
  (* Hypothesis: PARP1 synthesis PAR which recruits repair proteins to sites of DNA damage *)
  shows "∃x y z e1 e2. PARP1 x ∧ PAR y ∧ RepairProteins z ∧ Synthesis e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Recruit e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z DNA_Damage_Site"
  sledgehammer
  oops

end
