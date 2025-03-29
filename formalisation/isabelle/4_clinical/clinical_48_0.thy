theory clinical_48_0
imports Main

begin

typedecl entity
typedecl event

consts
  Inhibiting :: "entity ⇒ bool"
  PARP :: "entity ⇒ bool"
  SSBreaks :: "entity ⇒ bool"
  Accumulation :: "entity ⇒ bool"
  Result :: "event ⇒ bool"
  Accumulate :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  ReplicationForks :: "entity ⇒ bool"
  HRR :: "entity ⇒ bool"
  Collapse :: "event ⇒ bool"
  Trigger :: "event ⇒ bool"
  DSB :: "entity ⇒ bool"
  Inhibition :: "entity ⇒ bool"

(* Explanation 1: Inhibiting PARP results in accumulation of SS breaks. *)
axiomatization where
  explanation_1: "∀x y z e1 e2. Inhibiting x ∧ PARP y ∧ SSBreaks z ∧ Accumulation w ∧ Result e1 ∧ Agent e1 x ⟶ (Accumulate e2 ∧ Patient e2 z)"

(* Explanation 2: SS breaks collapse replication forks and trigger HRR. *)
axiomatization where
  explanation_2: "∀x y z e1 e2. SSBreaks x ∧ ReplicationForks y ∧ HRR z ∧ Collapse e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Trigger e2 ∧ Agent e2 x ∧ Patient e2 z"

theorem hypothesis:
  assumes asm: "Inhibition x ∧ PARP y"
  (* Hypothesis: Inhibition of PARP results in collapsed replication forks and DSB. *)
  shows "∀x y z e1 e2. Inhibition x ∧ PARP y ∧ ReplicationForks z ∧ DSB w ∧ Result e1 ∧ Agent e1 x ⟶ (Collapse e2 ∧ Patient e2 z) ∧ (Collapse e2 ∧ Patient e2 w)"
  by (simp add: explanation_2)
  

end
