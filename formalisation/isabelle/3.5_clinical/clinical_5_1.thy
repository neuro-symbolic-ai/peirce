theory clinical_5_1
imports Main


begin

typedecl entity
typedecl event

consts
  InhibitingPARP :: "entity ⇒ bool"
  ResultsIn :: "event ⇒ bool"
  AccumulationOfSingleStrandBreaks :: "entity ⇒ event ⇒ bool"
  SingleStrandBreaks :: "entity ⇒ bool"
  Collapse :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  ReplicationForks :: "entity ⇒ entity ⇒ bool"
  Trigger :: "event ⇒ bool"
  HomologousRecombinationRepair :: "entity ⇒ entity ⇒ bool"
  CollapsedReplicationForks :: "entity ⇒ event ⇒ bool"
  DoubleStrandBreak :: "entity ⇒ bool"

(* Explanation 1: Inhibiting PARP results in accumulation of single strand breaks *)
axiomatization where
  explanation_1: "∀e x. InhibitingPARP x ∧ ResultsIn e ∧ AccumulationOfSingleStrandBreaks x e"

(* Explanation 2: Single strand breaks collapse replication forks and trigger homologous recombination repair *)
axiomatization where
  explanation_2: "∀e x y. SingleStrandBreaks x ∧ Collapse e ∧ Agent e x ∧ Patient e y ∧ ReplicationForks x y ∧ Trigger e ∧ Agent e x ∧ Patient e y ∧ HomologousRecombinationRepair x y"

theorem hypothesis:
  assumes asm: "InhibitingPARP x"
  (* Hypothesis: Inhibition of PARP results in collapsed replication forks and double strand break *)
  shows "∃e. ResultsIn e ∧ CollapsedReplicationForks x e ∧ DoubleStrandBreak x"
proof -
  (* From the premise, we know that Inhibiting PARP results in accumulation of single strand breaks. *)
  from asm have "InhibitingPARP x" <ATP>
  (* There is a logical relation Implies(A, B), Implies(Inhibiting PARP, accumulation of single strand breaks) *)
  (* We can infer accumulation of single strand breaks. *)
  then have "AccumulationOfSingleStrandBreaks x e" for e <ATP>
  (* There is a logical relation Implies(B, C and D), Implies(accumulation of single strand breaks, trigger homologous recombination repair) *)
  (* We can infer that single strand breaks collapse replication forks and trigger homologous recombination repair. *)
  then have "SingleStrandBreaks x ∧ Collapse e ∧ ReplicationForks x y ∧ Trigger e ∧ HomologousRecombinationRepair x y" for e y <ATP>
  (* Since collapsed replication forks and double strand break are related to single strand breaks, we can infer the hypothesis. *)
  then have "ResultsIn e ∧ CollapsedReplicationForks x e ∧ DoubleStrandBreak x" for e <ATP>
  then show ?thesis <ATP>
qed

end
