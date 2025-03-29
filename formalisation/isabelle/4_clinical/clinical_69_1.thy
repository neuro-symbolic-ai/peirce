theory clinical_69_1
imports Main

begin

typedecl entity
typedecl event

consts
  Phosphorylation :: "entity ⇒ bool"
  Akt :: "entity ⇒ bool"
  Motif :: "entity ⇒ bool"
  CarboxyTerminal :: "entity ⇒ bool"
  Hydrophobic :: "entity ⇒ bool"
  mTOR :: "entity ⇒ bool"
  DNA_PK :: "entity ⇒ bool"
  Activity :: "entity ⇒ bool"
  Full :: "entity ⇒ bool"
  Stimulates :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  By :: "entity ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  PIK3 :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Activation :: "entity ⇒ bool"
  Partial :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  LeadsTo :: "event ⇒ event ⇒ bool"
  Bound :: "entity ⇒ entity ⇒ bool"
  Necessary :: "entity ⇒ entity ⇒ bool"
  Stimulation :: "entity ⇒ bool"

(* Explanation 1: Phosphorylation of Akt at S473 in the carboxy-terminal hydrophobic motif, either by mTOR or by DNA-PK, stimulates full Akt activity. *)
axiomatization where
  explanation_1: "∃x y z w e. Phosphorylation x ∧ Akt y ∧ Motif z ∧ CarboxyTerminal z ∧ Hydrophobic z ∧ (mTOR w ∨ DNA_PK w) ∧ Activity v ∧ Full v ∧ Stimulates e ∧ Agent e x ∧ Patient e v ∧ By x w"

(* Explanation 2: PKB/Akt binds to the docking site on PIK3 at the plasma membrane, leading to a partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane w ∧ Activation v ∧ Partial v ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ LeadsTo e1 e2 ∧ Activation v ∧ Agent e2 x ∧ Patient e2 v"

(* Explanation 3: When Akt is bound to a docking site, its phosphorylation at S473 in the carboxy-terminal hydrophobic motif is necessary for full Akt activity stimulation. *)
axiomatization where
  explanation_3: "∀x y z w. (Akt x ∧ DockingSite y ∧ Bound x y) ⟶ (Phosphorylation z ∧ Motif w ∧ CarboxyTerminal w ∧ Hydrophobic w ∧ Necessary z w ∧ Activity v ∧ Full v ∧ Stimulation v)"

theorem hypothesis:
  assumes asm: "Akt y ∧ Bound y z"
  (* Hypothesis: Phosphorylation of bound Akt stimulates full activity of Akt. *)
  shows "∃x z e. Phosphorylation x ∧ Akt y ∧ Bound y z ∧ Activity z ∧ Full z ∧ Stimulates e ∧ Agent e x ∧ Patient e z"
  using assms explanation_1 by blast
  

end
