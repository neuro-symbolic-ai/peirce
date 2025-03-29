theory clinical_87_0
imports Main

begin

typedecl entity
typedecl event

consts
  PD1Inhibitors :: "entity ⇒ bool"
  PDL1Inhibitors :: "entity ⇒ bool"
  CheckpointInhibitorAnticancerDrugs :: "entity ⇒ bool"
  AntiPD1PDL1Drugs :: "entity ⇒ bool"
  Progress :: "entity ⇒ bool"
  TNBC :: "entity ⇒ bool"
  Promising :: "entity ⇒ bool"
  Started :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Make :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  EarlySetting :: "entity ⇒ bool"
  MetastaticSetting :: "entity ⇒ bool"
  ImmuneCheckpointInhibitors :: "entity ⇒ bool"
  Outcomes :: "entity ⇒ bool"
  Had :: "event ⇒ bool"

(* Explanation 1: PD-1 inhibitors and PD-L1 inhibitors are a group of checkpoint inhibitor anticancer drugs. *)
axiomatization where
  explanation_1: "∀x. (PD1Inhibitors x ∨ PDL1Inhibitors x) ⟶ CheckpointInhibitorAnticancerDrugs x"

(* Explanation 2: anti-programmed death 1 (PD-1)/programmed death-ligand 1 (PD-L1) drugs have started to make progress in triple-negative breast cancer (TNBC) with promising outcomes both in the early and the metastatic setting. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. AntiPD1PDL1Drugs x ∧ Progress y ∧ TNBC z ∧ Promising y ∧ Started e1 ∧ Agent e1 x ∧ Make e2 ∧ Agent e2 x ∧ Patient e2 y ∧ In y z ∧ EarlySetting y ∧ MetastaticSetting y"

theorem hypothesis:
  assumes asm: "ImmuneCheckpointInhibitors x ∧ TNBC z"
  (* Hypothesis: Immune checkpoint inhibitors have had promising outcomes in TNBC. *)
  shows "∃x y e. ImmuneCheckpointInhibitors x ∧ Outcomes y ∧ Promising y ∧ Had e ∧ Agent e x ∧ Patient e y ∧ In y TNBC"
  sledgehammer
  oops

end
