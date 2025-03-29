theory clinical_93_10
imports Main


begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PolyADPribosylTransferse :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  By :: "entity ⇒ entity ⇒ bool"
  PolyADPribosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  Regulation :: "entity ⇒ entity ⇒ bool"
  ImportantCellularProcesses :: "entity ⇒ bool"
  Differentiation :: "entity ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  TumorTransformation :: "entity ⇒ bool"
  RecoveryOfCell :: "entity ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  Damage :: "entity ⇒ bool"
  MolecularEvents :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x y z e. PARP1 x ∧ PolyADPribosylTransferse y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ By z PolyADPribosylation"

(* Explanation 2: Poly(ADP-ribosyl)ation… is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation *)
axiomatization where
  explanation_2: "∀x y z. PolyADPribosylation x ⟶ DependentOn x DNA ∧ InvolvedIn x Regulation ∧ Regulation x ImportantCellularProcesses ∧ Regulation x Differentiation ∧ Regulation x Proliferation ∧ Regulation x TumorTransformation"

(* Explanation 3: Poly(ADP-ribosyl)ation… is involved in… the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x y z. PolyADPribosylation x ⟶ InvolvedIn x Regulation ∧ Regulation x MolecularEvents ∧ RecoveryOfCell y ∧ From y DNA ∧ Damage y"


theorem hypothesis:
 assumes asm: "PARP1 x ∧ PolyADPribosylTransferse y ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses ∧ RecoveryFromDNA x"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "∃x y z e. PARP1 x ∧ PolyADPribosylTransferse y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses ∧ RecoveryFromDNA x"
proof -
  (* From the premise, we can extract the known information about PARP1, PolyADPribosylTransferse, NuclearProteins, and ImportantCellularProcesses. *)
  from asm have "PARP1 x ∧ PolyADPribosylTransferse y ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses" <ATP>
  (* There is a logical relation Implies(A, D), Implies(PARP1 is a poly(ADP-ribosyl)transferase, Poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage) *)
  (* Both A and D are from explanatory sentence 1 and 3, we can infer Modifies, Agent, Patient, and RecoveryFromDNA. *)
  then have "PARP1 x ∧ PolyADPribosylTransferse y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses ∧ RecoveryFromDNA x" <ATP>
  then show ?thesis <ATP>
qed

end
