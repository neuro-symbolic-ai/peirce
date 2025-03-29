theory clinical_92_0
imports Main


begin

typedecl entity
typedecl event

consts
  PARP2 :: "entity ⇒ bool"
  PolyADPRibosyltransferaseLike2Protein :: "entity ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"
  CatalyticDomain :: "entity ⇒ entity"
  CapableOfCatalyzing :: "entity ⇒ entity ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  PolyADPRibosylTransferse :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  InvolvedIn :: "event ⇒ entity ⇒ bool"
  ImportantIn :: "event ⇒ entity ⇒ bool"
  Including :: "event ⇒ entity ⇒ bool"
  RecoveryFromDNADamage :: "event ⇒ bool"
  CellularProcesses :: "event ⇒ entity"

(* Explanation 1: PARP2 encodes poly(ADP-ribosyl)transferase-like 2 protein, which contains a catalytic domain capable of catalyzing a poly(ADP-ribosyl)ation reaction *)
axiomatization where
  explanation_1: "∃x y z e. PARP2 x ∧ PolyADPRibosyltransferaseLike2Protein y ∧ Contains y (CatalyticDomain z) ∧ CapableOfCatalyzing z (PolyADPRibosylTransferse e)"

(* Explanation 2: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
axiomatization where
  explanation_2: "∃x y z e. PARP1 x ∧ PolyADPRibosylTransferse y ∧ Modifies e ∧ NuclearProteins z ∧ InvolvedIn e z ∧ ImportantIn e z ∧ Including e z"

theorem hypothesis:
 assumes asm: "PARP1 x ∧ PARP2 x"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage *)
 shows "∃e. InvolvedIn e x ∧ Modifies e ∧ ImportantIn e (CellularProcesses e) ∧ Including e (RecoveryFromDNADamage e)"
proof -
  (* From the premise, we know that PARP1 and PARP2 are both present. *)
  from asm have "PARP1 x" and "PARP2 x" <ATP>
  (* There is a logical relation Implies(D, E), Implies(PARP1 is a polyADP-ribosyl transferase, PARP1 modifies nuclear proteins involved in important cellular processes including recovery from DNA damage) *)
  (* Since we have PARP1 x, we can infer the involvement in polyADP-ribosylation and important processes including recovery from DNA damage. *)
  then have "∃e. InvolvedIn e x ∧ Modifies e ∧ ImportantIn e (CellularProcesses e) ∧ Including e (RecoveryFromDNADamage e)" <ATP>
  then show ?thesis <ATP>
qed

end
