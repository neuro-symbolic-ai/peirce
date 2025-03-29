theory clinical_93_7
imports Main


begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PolyADPRibosylTransferase :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  By :: "entity ⇒ entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  ImportantCellularProcesses :: "entity ⇒ bool"
  SuchAs :: "entity ⇒ entity ⇒ bool"
  MolecularEvents :: "entity ⇒ bool"
  RecoveryOfCell :: "entity ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  Damage :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x y z e. PARP1 x ∧ PolyADPRibosylTransferase y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ By z x ∧ PolyADPRibosylation x"

(* Explanation 2: Poly(ADP-ribosyl)ation… is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation… *)
axiomatization where
  explanation_2: "∀x y z. PolyADPRibosylation x ⟶ DependentOn x DNA ∧ InvolvedIn x Regulation ∧ ImportantCellularProcesses z ∧ SuchAs x Differentiation ∧ SuchAs x Proliferation ∧ SuchAs x TumorTransformation"

(* Explanation 3: Poly(ADP-ribosyl)ation… is involved in… the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x y z. PolyADPRibosylation x ⟶ InvolvedIn x Regulation ∧ MolecularEvents y ∧ RecoveryOfCell y ∧ From y DNA ∧ Damage y"


theorem hypothesis:
 assumes asm: "PARP1 x ∧ PolyADPRibosylTransferase y ∧ NuclearProteins z"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "∃x y z e. PARP1 x ∧ PolyADPRibosylTransferase y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn e ImportantCellularProcesses ∧ RecoveryOfCell e"
proof -
  (* From the premise, we have the information about PARP1, PolyADPRibosylTransferase, and NuclearProteins. *)
  from asm have "PARP1 x ∧ PolyADPRibosylTransferase y ∧ NuclearProteins z" <ATP>
  (* We know from Explanation 1 that PARP1 is a poly(ADP-ribosyl)transferase that modifies nuclear proteins by poly(ADP-ribosyl)ation. *)
  (* There is a logical relation Implies(A, D), Implies(PARP1 is a poly(ADP-ribosyl)transferase, Poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage) *)
  (* Since PARP1 is a poly(ADP-ribosyl)transferase, we can infer that it is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage. *)
  then have "PARP1 x ∧ PolyADPRibosylTransferase y ∧ Modifies e ∧ Agent e y ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn e ImportantCellularProcesses ∧ RecoveryOfCell e" <ATP>
  then show ?thesis <ATP>
qed

end
