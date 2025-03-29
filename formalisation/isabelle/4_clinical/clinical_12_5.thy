theory clinical_12_5
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
  DirectlyCauses :: "event ⇒ event ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesis e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DNA_Damage_Site z ∧ Recruit e ∧ Agent e x ∧ Patient e y ∧ To y z"

(* Explanation 3: The PAR synthesised by PARP1 is the same PAR that recruits repair proteins to the damaged DNA site *)
axiomatization where
  explanation_3: "∀x y z e1 e2. PAR x ∧ PARP1 y ∧ RepairProteins z ∧ Synthesis e1 ∧ Agent e1 y ∧ Patient e1 x ∧ Recruit e2 ∧ Agent e2 x ∧ Patient e2 z ∧ To z z"

(* Explanation 4: The synthesis of PAR by PARP1 directly causes the recruitment of repair proteins to the damaged DNA site *)
axiomatization where
  explanation_4: "∀x y z e1 e2. PAR x ∧ PARP1 y ∧ RepairProteins z ∧ Synthesis e1 ∧ Agent e1 y ∧ Patient e1 x ∧ Recruit e2 ∧ Agent e2 x ∧ Patient e2 z ∧ To z z ⟶ DirectlyCauses e1 e2"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PAR y ∧ RepairProteins z"
  (* Hypothesis: PARP1 synthesis PAR which recruits repair proteins to sites of DNA damage *)
  shows "∃x y z e1 e2. PARP1 x ∧ PAR y ∧ RepairProteins z ∧ Synthesis e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Recruit e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z z"
  by (simp add: explanation_3)
  

end
