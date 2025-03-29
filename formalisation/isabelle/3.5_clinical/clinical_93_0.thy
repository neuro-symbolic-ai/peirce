theory clinical_93_0
imports Main


begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PolyADPRibosylTransferse :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  InvolvedIn :: "event ⇒ entity ⇒ bool"
  VariousNuclearProteins :: "entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  Regulation :: "entity ⇒ bool"
  CellularProcesses :: "entity ⇒ bool"
  Differentiation :: "entity ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  TumorTransformation :: "entity ⇒ bool"
  MolecularEvents :: "entity ⇒ bool"
  RecoveryOfCellFromDNADamage :: "entity ⇒ bool"
  DNA :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x. PARP1 x ⟶ (PolyADPRibosylTransferse x ∧ (∃e. Modifies e ∧ Agent e x ∧ InvolvedIn e VariousNuclearProteins))"

(* Explanation 2: Poly(ADP-ribosyl)ation… is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation *)
axiomatization where
  explanation_2: "∀x. PolyADPRibosylation x ⟶ (DependentOn x DNA ∧ InvolvedIn x Regulation ∧ InvolvedIn x CellularProcesses ∧ InvolvedIn x Differentiation ∧ InvolvedIn x Proliferation ∧ InvolvedIn x TumorTransformation)"

(* Explanation 3: Poly(ADP-ribosyl)ation… is involved in… the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x. PolyADPRibosylation x ⟶ (InvolvedIn x Regulation ∧ InvolvedIn x MolecularEvents ∧ InvolvedIn x RecoveryOfCellFromDNADamage)"


theorem hypothesis:
 assumes asm: "PARP1 x"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "PolyADPRibosylTransferse x ∧ ∃e. Modifies e ∧ Agent e x ∧ InvolvedIn e VariousNuclearProteins ∧ InvolvedIn e CellularProcesses ∧ InvolvedIn e RecoveryOfCellFromDNADamage"
proof -
  (* From the premise, we know that PARP1 is related to PolyADPRibosylTransferse and modifies various nuclear proteins. *)
  from asm have "PARP1 x" <ATP>
  (* There is a logical relation Implies(A, D), Implies(PARP1 is a polytransferase, Polyation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage) *)
  (* Since PARP1 is a poly(ADP-ribosyl)transferase, it is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage. *)
  then have "PolyADPRibosylTransferse x ∧ ∃e. Modifies e ∧ Agent e x ∧ InvolvedIn e VariousNuclearProteins ∧ InvolvedIn e CellularProcesses ∧ InvolvedIn e RecoveryOfCellFromDNADamage" <ATP>
  then show ?thesis <ATP>
qed

end
