theory clinical_90_0
imports Main

begin

typedecl entity
typedecl event

consts
  PARP1_2Inhibitor :: "entity ⇒ bool"
  TumourSpecificDefects :: "entity ⇒ bool"
  DNARepair :: "entity ⇒ bool"
  Target :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Role :: "entity ⇒ bool"
  PARP1_2 :: "entity ⇒ bool"
  RecoverFromDNADamage :: "entity ⇒ bool"
  Olaparib :: "entity ⇒ bool"
  Talazoparib :: "entity ⇒ bool"
  PolyADPRibosePolymerase1_2Inhibitor :: "entity ⇒ bool"
  Licensed :: "entity ⇒ bool"
  PARPInhibitor :: "entity ⇒ bool"

(* Explanation 1: [PARP1/2] inhibitors target tumour-specific defects in DNA repair through the role of PARP1/2 in recover from DNA damage. *)
axiomatization where
  explanation_1: "∀x y z e. PARP1_2Inhibitor x ∧ TumourSpecificDefects y ∧ DNARepair y ∧ Target e ∧ Agent e x ∧ Patient e y ∧ Role z ∧ PARP1_2 z ∧ RecoverFromDNADamage z"

(* Explanation 2: Olaparib and talazoparib are licensed poly [ADP-ribose] polymerase 1/2 inhibitors. *)
axiomatization where
  explanation_2: "∀x y. (Olaparib x ∨ Talazoparib x) ∧ PolyADPRibosePolymerase1_2Inhibitor y ∧ Licensed y"

theorem hypothesis:
  assumes asm: "(Olaparib x ∨ Talazoparib x) ∧ PARPInhibitor y ∧ Licensed y"
  (* Hypothesis: Olaparib and talazoparib are licensed PARP inhibitors, which target tumour specific defects in DNA repair. *)
  shows "∃x y z e. (Olaparib x ∨ Talazoparib x) ∧ PARPInhibitor y ∧ Licensed y ∧ Target e ∧ Agent e y ∧ Patient e z ∧ TumourSpecificDefects z ∧ DNARepair z"
  using assms explanation_1 by blast
  

end
