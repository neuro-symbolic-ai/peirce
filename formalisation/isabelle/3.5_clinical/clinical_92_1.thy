theory clinical_92_1
imports Main

begin

typedecl entity
typedecl event

consts
  PARP2 :: "entity ⇒ bool"
  PolyADPRibosylTransferaseLike2Protein :: "entity ⇒ bool"
  CatalyticDomain :: "entity ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"
  CapableOf :: "event ⇒ entity ⇒ bool"
  Catalyzing :: "event ⇒ bool"
  PolyADPRibosylationReaction :: "entity ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  PolyADPRibosylTransferse :: "entity ⇒ bool"
  Via :: "event ⇒ entity ⇒ entity ⇒ bool"
  Modifies :: "event ⇒ entity ⇒ entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  InvolvedIn :: "event ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 1: PARP2 encodes poly(ADP-ribosyl)transferase-like 2 protein, which contains a catalytic domain *)
axiomatization where
  explanation_1: "∃x y z. PARP2 x ∧ PolyADPRibosylTransferaseLike2Protein y ∧ CatalyticDomain z ∧ Contains y z"

(* Explanation 2: Capable of catalyzing a poly(ADP-ribosyl)ation reaction *)
axiomatization where
  explanation_2: "∀x. CapableOf e x ∧ Catalyzing e ∧ PolyADPRibosylationReaction x"

(* Explanation 3: PARP1 is a polyADP-ribosyl transferse which, via polyADP-ribosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
axiomatization where
  explanation_3: "∃x y z e. PARP1 x ∧ PolyADPRibosylTransferse y ∧ Via e y x ∧ Modifies e y z ∧ InvolvedIn e z NuclearProteins ∧ InvolvedIn e z ImportantCellularProcessesIncludingRecoveryFromDNADamage"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PARP2 x"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage *)
  shows "InvolvedIn e x ProcessesIncludingRecoveryFromDNADamage ∧ PolyADPribosylation e ∧ ImportantFor e ProcessesIncludingRecoveryFromDNADamage"
proof -
  (* From the premise, we have information about PARP1 and PARP2. *)
  from asm have "PARP1 x" and "PARP2 x" <ATP>
  (* There is a logical relation Implies(D, E), Implies(PARP1 is a polyADP-ribosyl transferase, PARP1 modifies nuclear proteins involved in important cellular processes including recovery from DNA damage) *)
  (* Since we have PARP1 x, we can infer that it modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
  then have "Modifies e x z ∧ InvolvedIn e z NuclearProteins ∧ InvolvedIn e z ImportantCellularProcessesIncludingRecoveryFromDNADamage" for e z <ATP>
  (* There is a logical relation Implies(A, C), Implies([PARP2] encodes polytransferase-like 2 protein, [PARP2] catalyzes a polyation reaction) *)
  (* We can infer that PARP2 x catalyzes a poly(ADP-ribosyl)ation reaction from the explanation 1. *)
  then have "CapableOf e x ∧ Catalyzing e ∧ PolyADPRibosylationReaction x" for e <ATP>
  (* Therefore, we can conclude that PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage. *)
  then show ?thesis <ATP>
qed

end
