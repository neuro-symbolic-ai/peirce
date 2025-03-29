theory clinical_92_5
imports Main


begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PARP2 :: "entity ⇒ bool"
  Involved :: "event ⇒ bool"
  In :: "event ⇒ entity ⇒ bool"
  PolyADPribosylation :: "entity ⇒ bool"
  Important :: "entity ⇒ bool"
  CellularProcesses :: "entity ⇒ bool"
  RecoveryFromDNADamage :: "entity ⇒ bool"

(* Explanation 1: PARP1 and PARP2 are both involved in polyADP-ribosylation. *)
axiomatization where
  explanation_1: "∃x y z e. PARP1 x ∧ PARP2 y ∧ Involved e ∧ In e z ∧ PolyADPribosylation z"

(* Explanation 2: PARP1 and PARP2 are both involved in important cellular processes, including recovery from DNA damage. *)
axiomatization where
  explanation_2: "∃x y z e. PARP1 x ∧ PARP2 y ∧ Involved e ∧ In e z ∧ Important z ∧ CellularProcesses z ∧ RecoveryFromDNADamage z"


theorem hypothesis:
 assumes asm: "PARP1 x ∧ PARP2 y ∧ Involved e ∧ In e z ∧ PolyADPribosylation z ∧ Important z ∧ CellularProcesses z ∧ RecoveryFromDNADamage z"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage. *)
 shows "∃x y z e. PARP1 x ∧ PARP2 y ∧ Involved e ∧ In e z ∧ PolyADPribosylation z ∧ Important z ∧ CellularProcesses z ∧ RecoveryFromDNADamage z"
  using assms by blast
  

end
