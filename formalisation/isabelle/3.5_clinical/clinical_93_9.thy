theory clinical_93_9
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
  By :: "entity ⇒ entity ⇒ entity ⇒ bool"
  PolyADPribosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  ImportantCellularProcesses :: "entity ⇒ bool"
  Includes :: "entity ⇒ entity ⇒ entity ⇒ bool"
  Differentiation :: "entity ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  TumorTransformation :: "entity ⇒ bool"
  MolecularEvents :: "entity ⇒ bool"
  RecoveryOfCell :: "entity ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  Damage :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x y z e. PARP1 x ∧ PolyADPribosylTransferse y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ By z x PolyADPribosylation"

(* Explanation 2: Poly(ADP-ribosyl)ation… is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation… *)
axiomatization where
  explanation_2: "∀x y z. PolyADPribosylation x ⟶ (DependentOn x DNA ∧ InvolvedIn x Regulation ∧ ImportantCellularProcesses z ∧ Includes z x Differentiation ∧ Includes z x Proliferation ∧ Includes z x TumorTransformation)"

(* Explanation 3: Poly(ADP-ribosyl)ation… is involved in… the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x y z. PolyADPribosylation x ⟶ (InvolvedIn x Regulation ∧ MolecularEvents z ∧ RecoveryOfCell z ∧ From z DNA ∧ Damage z)"


theorem hypothesis:
 assumes asm: "PARP1 x"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "∃x y z e. PARP1 x ∧ PolyADPribosylTransferse y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses ∧ RecoveryOfCell z"
proof -
  (* From the premise, we know that PARP1 x. *)
  from asm have "PARP1 x" <ATP>
  (* We have the explanatory sentence 1 stating that PARP1 is a poly(ADP-ribosyl)transferase. *)
  (* There is a logical relation Implies(A, D), Implies(PARP1 is a poly(ADP-ribosyl)transferase, Poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage) *)
  (* Therefore, we can infer that PARP1 is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage. *)
  then have "PolyADPribosylTransferse y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses ∧ RecoveryOfCell z" <ATP>
  then show ?thesis <ATP>
qed

end
