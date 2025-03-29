theory clinical_93_2
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
  RecoveryFromDNA :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x y z e. PARP1 x ∧ PolyADPRibosylTransferase y ∧ Modifies e ∧ Agent e x ∧ Patient e z ∧ NuclearProteins z ∧ By z y ∧ PolyADPRibosylation y"

(* Explanation 2: Poly(ADP-ribosyl)ation… is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation… *)
axiomatization where
  explanation_2: "∀x y z. PolyADPRibosylation x ∧ DependentOn x DNA ∧ InvolvedIn x Regulation ∧ ImportantCellularProcesses z ∧ InvolvedIn x Regulation ∧ InvolvedIn x Differentiation ∧ InvolvedIn x Proliferation ∧ InvolvedIn x TumorTransformation"

(* Explanation 3: Poly(ADP-ribosyl)ation… is involved in… the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x y z. PolyADPRibosylation x ∧ InvolvedIn x Regulation ∧ InvolvedIn x MolecularEvents ∧ RecoveryFromDNA y ∧ InvolvedIn y DNADamage"


theorem hypothesis:
 assumes asm: "PARP1 x"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "∃x y z e. PARP1 x ∧ PolyADPRibosylTransferase y ∧ Modifies e ∧ Agent e x ∧ Patient e z ∧ NuclearProteins z ∧ InvolvedIn z ImportantCellularProcesses ∧ RecoveryFromDNA x"
  sledgehammer
  oops

end
