theory clinical_90_0
imports Main


begin

typedecl entity
typedecl event

consts
  PARPInhibitor :: "entity ⇒ bool"
  Target :: "event ⇒ entity ⇒ bool"
  TumourSpecificDefects :: "event ⇒ bool"
  DNARepair :: "event ⇒ bool"
  RoleOf :: "event ⇒ entity ⇒ bool"
  RecoverFromDamage :: "event ⇒ bool"
  Olaparib :: "entity ⇒ bool"
  Talazoparib :: "entity ⇒ bool"
  Licensed :: "entity ⇒ bool"
  PolyADPInhibitor :: "entity ⇒ bool"
  Polymerase12Inhibitor :: "entity ⇒ bool"

(* Explanation 1: [PARP1/2] inhibitors target tumour-specific defects in DNA repair through the role of PARP1/2 in recover from DNA damage. *)
axiomatization where
  explanation_1: "∀x e. PARPInhibitor x ∧ Target e x ∧ TumourSpecificDefects e ∧ DNARepair e ∧ RoleOf e PARP1 ∧ RecoverFromDamage e"

(* Explanation 2: Olaparib and talazoparib are licensed poly [ADP-ribose] polymerase 1/2 inhibitors. *)
axiomatization where
  explanation_2: "∃x y. Olaparib x ∧ Talazoparib y ∧ Licensed x ∧ Licensed y ∧ PolyADPInhibitor x ∧ PolyADPInhibitor y ∧ Polymerase12Inhibitor x ∧ Polymerase12Inhibitor y"


theorem hypothesis:
 assumes asm: "PARPInhibitor x ∧ PARPInhibitor y ∧ Licensed x ∧ Licensed y"
  (* Hypothesis: Olaparib and talazoparib are licensed PARP inhibitors, which target tumour specific defects in DNA repair. *)
 shows "∃x y e. Olaparib x ∧ Talazoparib y ∧ Licensed x ∧ Licensed y ∧ PARPInhibitor x ∧ PARPInhibitor y ∧ Target e x ∧ Target e y ∧ TumourSpecificDefects e ∧ DNARepair e"
  using explanation_1 explanation_2 by blast
  

end
