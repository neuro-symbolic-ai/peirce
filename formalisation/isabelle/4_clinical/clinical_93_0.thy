theory clinical_93_0
imports Main

begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PolyADPTransferase :: "entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  By :: "event ⇒ entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  DependentOn :: "entity ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  CellularProcesses :: "entity ⇒ bool"
  Differentiation :: "entity ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  TumorTransformation :: "entity ⇒ bool"
  MolecularEvents :: "entity ⇒ bool"
  RecoveryFrom :: "entity ⇒ entity ⇒ bool"
  DNA :: "entity ⇒ bool"
  Regulation :: "entity ⇒ bool"
  Recovery :: "entity ⇒ bool"
  DNADamage :: "entity ⇒ bool"

(* Explanation 1: PARP1 is a poly(ADP-ribosyl)transferase, which modifies various nuclear proteins by poly(ADP-ribosyl)ation. *)
axiomatization where
  explanation_1: "∃x y z e. PARP1 x ∧ PolyADPTransferase x ∧ NuclearProteins y ∧ Modifies e ∧ Agent e x ∧ Patient e y ∧ By e z ∧ PolyADPRibosylation z"

(* Explanation 2: Poly(ADP-ribosyl)ation is dependent on DNA and is involved in the regulation of various important cellular processes such as differentiation, proliferation, and tumor transformation. *)
axiomatization where
  explanation_2: "∃x y z. PolyADPRibosylation x ∧ DependentOn x y ∧ DNA y ∧ InvolvedIn x z ∧ Regulation z ∧ CellularProcesses z ∧ Differentiation z ∧ Proliferation z ∧ TumorTransformation z"

(* Explanation 3: Poly(ADP-ribosyl)ation is involved in the regulation of the molecular events involved in the recovery of cell from DNA damage. *)
axiomatization where
  explanation_3: "∃x y z w v. PolyADPRibosylation x ∧ InvolvedIn x y ∧ Regulation y ∧ MolecularEvents z ∧ InvolvedIn z w ∧ Recovery w ∧ RecoveryFrom w v ∧ DNADamage v"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PolyADPTransferase x ∧ NuclearProteins y"
  (* Hypothesis: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage *)
  shows "∃x y e z. PARP1 x ∧ PolyADPTransferase x ∧ NuclearProteins y ∧ Modifies e ∧ Agent e x ∧ Patient e y ∧ By e z ∧ PolyADPRibosylation z ∧ InvolvedIn y CellularProcesses ∧ RecoveryFrom y DNADamage"
  sledgehammer
  oops

end
