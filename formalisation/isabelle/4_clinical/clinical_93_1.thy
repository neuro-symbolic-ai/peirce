theory clinical_93_1
imports Main

begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PolyADPRibosylTransferase :: "entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  By :: "event ⇒ entity ⇒ bool"
  DNA :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  RegulationOfCellularProcesses :: "entity"
  SuchAs :: "entity ⇒ entity ⇒ bool"
  Differentiation :: "entity"
  Proliferation :: "entity"
  TumorTransformation :: "entity"
  MolecularEvents :: "entity ⇒ bool"
  RegulationOf :: "entity ⇒ entity"
  RecoveryOfCell :: "entity"
  From :: "entity ⇒ entity ⇒ bool"
  DNADamage :: "entity"
  Including :: "entity ⇒ entity ⇒ bool"
  CellularProcesses :: "entity"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation. *)
axiomatization where
  explanation_1: "∀x y z e. PARP1 x ∧ PolyADPRibosylTransferase x ∧ NuclearProteins y ∧ PolyADPRibosylation z ∧ Modifies e ∧ Agent e x ∧ Patient e y ∧ By e z"

(* Explanation 2: Poly(ADP-ribosyl)ation is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation. *)
axiomatization where
  explanation_2: "∀x y. PolyADPRibosylation x ∧ DNA y ⟶ (DependentOn x y ∧ InvolvedIn x RegulationOfCellularProcesses ∧ SuchAs RegulationOfCellularProcesses Differentiation ∧ SuchAs RegulationOfCellularProcesses Proliferation ∧ SuchAs RegulationOfCellularProcesses TumorTransformation)"

(* Explanation 3: Poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage. *)
axiomatization where
  explanation_3: "∀x y. PolyADPRibosylation x ∧ MolecularEvents y ⟶ (InvolvedIn x (RegulationOf y) ∧ InvolvedIn y RecoveryOfCell ∧ From RecoveryOfCell DNADamage)"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PolyADPRibosylTransferase x ∧ NuclearProteins y ∧ PolyADPRibosylation z"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
  shows "∃x y z e. PARP1 x ∧ PolyADPRibosylTransferase x ∧ NuclearProteins y ∧ PolyADPRibosylation z ∧ Modifies e ∧ Agent e x ∧ Patient e y ∧ Via e z ∧ InvolvedIn y CellularProcesses ∧ Including y RecoveryFromDNADamage"
proof -
  (* From the premise, we have known information about PARP1, PolyADPRibosylTransferase, NuclearProteins, and PolyADPRibosylation. *)
  from asm have "PARP1 x ∧ PolyADPRibosylTransferase x ∧ NuclearProteins y ∧ PolyADPRibosylation z" by auto
  (* Explanation 1 provides a logical relation Implies(A, B), which states that PARP1 modifies nuclear proteins by poly(ADP-ribosyl)ation. *)
  (* We can use this to infer the existence of an event e where Modifies e, Agent e x, Patient e y, and By e z. *)
  then have "∃e. Modifies e ∧ Agent e x ∧ Patient e y ∧ By e z" using explanation_1 by blast
  (* Explanation 3 provides that poly(ADP-ribosyl)ation is involved in the regulation of molecular events involved in the recovery of cell from DNA damage. *)
  (* This implies that the nuclear proteins y are involved in cellular processes including recovery from DNA damage. *)
  from explanation_3 have "InvolvedIn z (RegulationOf y) ∧ InvolvedIn y RecoveryOfCell ∧ From RecoveryOfCell DNADamage" sledgehammer
  (* Therefore, we can conclude that the nuclear proteins y are involved in important cellular processes including recovery from DNA damage. *)
  then have "InvolvedIn y CellularProcesses ∧ Including y RecoveryFromDNADamage" <ATP>
  (* Combining all the information, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
