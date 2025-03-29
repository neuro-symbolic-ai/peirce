theory clinical_92_4
imports Main


begin

typedecl entity
typedecl event

consts
  PARP2 :: "entity ⇒ bool"
  PolyADPRibosyltransferase :: "entity ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"
  CatalyticDomain :: "entity ⇒ bool"
  CapableOf :: "entity ⇒ entity ⇒ bool"
  Catalyzing :: "entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  PolyADPRibosylTransferse :: "entity ⇒ bool"
  Modifies :: "entity ⇒ entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  ImportantFor :: "entity ⇒ entity ⇒ bool"
  CellularProcesses :: "entity"

(* Explanation 1: [PARP2] encodes poly(ADP-ribosyl)transferase-like 2 protein, which contains a catalytic domain capable of catalyzing a poly(ADP-ribosyl)ation reaction *)
axiomatization where
  explanation_1: "∃x y z e. PARP2 x ∧ PolyADPRibosyltransferase y ∧ Contains z y ∧ CatalyticDomain z ∧ CapableOf e z ∧ Catalyzing e ∧ PolyADPRibosylation e"

(* Explanation 2: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
axiomatization where
  explanation_2: "∃x y z e. PARP1 x ∧ PolyADPRibosylTransferse y ∧ Modifies z y ∧ NuclearProteins z ∧ InvolvedIn e z ∧ ImportantFor e CellularProcesses ∧ ImportantFor e RecoveryFromDNADamage"


theorem hypothesis:
 assumes asm: "PARP1 x ∧ PARP2 x"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage *)
 shows "∃e. InvolvedIn e x ∧ PolyADPRibosylation e ∧ ImportantFor e RecoveryFromDNADamage"
proof -
  (* From the premise, we have the information about PARP1 and PARP2. *)
  from asm have "PARP1 x" and "PARP2 x" apply simp
  (* There is a logical relation Implies(D, E), Implies(PARP1 is a polyADP-ribosyl transferase, PARP1 modifies nuclear proteins involved in important cellular processes including recovery from DNA damage) *)
  (* We can infer that PARP1 modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
  then have "InvolvedIn x NuclearProteins ∧ PolyADPRibosylation x ∧ ImportantFor x RecoveryFromDNADamage" by (simp add: assms)
  then show ?thesis sledgehammer
qed

end
