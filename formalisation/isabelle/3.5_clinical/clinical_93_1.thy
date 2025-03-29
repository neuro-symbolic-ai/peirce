theory clinical_93_1
imports Main


begin

typedecl entity
typedecl event

consts
  PolyADPRibosylTransferase :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  VariousNuclearProteins :: "entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  DNA :: "entity ⇒ bool"
  RegulationOfCellularProcesses :: "entity ⇒ bool"
  Differentiation :: "entity ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  TumorTransformation :: "entity ⇒ bool"
  RegulationOfMolecularEvents :: "entity ⇒ bool"
  RecoveryOfCellFromDNADamage :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x. PolyADPRibosylTransferase x ⟶ (∃e. Modifies e ∧ Agent e x ∧ Patient e x ∧ VariousNuclearProteins x)"

(* Explanation 2: Poly(ADP-ribosyl)ation… is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation *)
axiomatization where
  explanation_2: "∀x. PolyADPRibosylation x ⟶ (DependentOn x DNA ∧ InvolvedIn x RegulationOfCellularProcesses ∧ InvolvedIn x Differentiation ∧ InvolvedIn x Proliferation ∧ InvolvedIn x TumorTransformation)"

(* Explanation 3: Poly(ADP-ribosyl)ation… is involved in… the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x. PolyADPRibosylation x ⟶ (InvolvedIn x RegulationOfMolecularEvents ∧ InvolvedIn x RecoveryOfCellFromDNADamage)"


theorem hypothesis:
 assumes asm: "PARP1 x"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "PolyADPRibosylTransferase x ∧ (∃e. Modifies e ∧ Agent e x ∧ Patient e x ∧ VariousNuclearProteins x ∧ InvolvedIn e RegulationOfCellularProcesses ∧ InvolvedIn e RecoveryOfCellFromDNADamage)"
proof -
  (* From the premise, we know that PARP1 is a poly(ADP-ribosyl)transferase. *)
  from asm have "PolyADPRibosylTransferase x" <ATP>
  (* We have the derived implication Implies(A, D), which states that if PARP1 is a poly(ADP-ribosyl)transferase, then poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage. *)
  (* This implies that PARP1 being a poly(ADP-ribosyl)transferase is related to the recovery of cell from DNA damage. *)
  then have "∃e. Modifies e ∧ Agent e x ∧ Patient e x ∧ VariousNuclearProteins x ∧ InvolvedIn e RegulationOfCellularProcesses ∧ InvolvedIn e RecoveryOfCellFromDNADamage" <ATP>
  (* Therefore, we have shown that PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
  then show ?thesis <ATP>
qed

end
