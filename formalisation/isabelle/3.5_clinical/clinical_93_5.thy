theory clinical_93_5
imports Main


begin

typedecl entity
typedecl event

consts
  PolyADPribosylTransferse :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  PolyADPribosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation *)
axiomatization where
  explanation_1: "∀x. PolyADPribosylTransferse x ⟶ (∃e. Modifies e ∧ Agent e x ∧ Patient e x ∧ NuclearProteins x)"

(* Explanation 2: Poly(ADP-ribosyl)ation is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation *)
axiomatization where
  explanation_2: "∀x. PolyADPribosylation x ⟶ (DependentOn x DNA ∧ InvolvedIn x CellularProcesses ∧ InvolvedIn x Differentiation ∧ InvolvedIn x Proliferation ∧ InvolvedIn x TumorTransformation)"

(* Explanation 3: Poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage *)
axiomatization where
  explanation_3: "∀x. PolyADPribosylation x ⟶ (InvolvedIn x Regulation ∧ InvolvedIn x MolecularEvents ∧ InvolvedIn x RecoveryOfCellFromDNADamage)"


theorem hypothesis:
 assumes asm: "PARP1 x"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
 shows "PolyADPribosylTransferse x ∧ ∃e. Modifies e ∧ Agent e x ∧ Patient e x ∧ NuclearProteins x ∧ InvolvedIn e x CellularProcesses ∧ InvolvedIn e x RecoveryOfCellFromDNADamage"
  sledgehammer
  oops

end
