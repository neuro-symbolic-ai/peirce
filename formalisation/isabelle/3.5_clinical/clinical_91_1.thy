theory clinical_91_1
imports Main


begin

typedecl entity
typedecl event

consts
  Inhibitors :: "entity ⇒ bool"
  Agent :: "entity ⇒ entity ⇒ bool"
  Purpose :: "entity ⇒ entity ⇒ bool"
  TargetingDefects :: "entity ⇒ entity"
  DNARepair :: "entity ⇒ bool"
  TumorSpecificDefects :: "entity ⇒ bool"
  MannerOf :: "entity ⇒ entity ⇒ bool"
  Recovery :: "entity ⇒ entity"
  Damage :: "entity ⇒ bool"

(* Explanation 1: For any entity e, if e is an agent in a process involving PARP1/2 inhibitors, then the purpose of e is related to targeting tumor-specific defects in DNA repair *)
axiomatization where
  explanation_1: "∀e. Inhibitors e ∧ Agent e x ⟶ (Purpose e (TargetingDefects e) ∧ DNARepair e ∧ TumorSpecificDefects e)"

(* Explanation 2: For any entity e, if e is an agent in a process involving PARP1/2 inhibitors, then the manner in which e acts is related to the recovery from DNA damage *)
axiomatization where
  explanation_2: "∀e. Inhibitors e ∧ Agent e x ⟶ (MannerOf e (Recovery e) ∧ DNARepair e ∧ Damage e)"


theorem hypothesis:
 assumes asm: "Inhibitors e"
  (* Hypothesis: [PARP1/2] inhibitors target tumour-specific defects in DNA repair through the role of PARP1/2 in recover from DNA damage *)
 shows "∃e. Inhibitors e ∧ TargetingDefects e ∧ TumorSpecificDefects e ∧ DNARepair e ∧ RoleOf e PARP1/2 ∧ RecoverFromDamage e"
  sledgehammer
  oops

end
