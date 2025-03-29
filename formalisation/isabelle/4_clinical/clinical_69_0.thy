theory clinical_69_0
imports Main

begin

typedecl entity
typedecl event

consts
  Phosphorylation :: "entity ⇒ bool"
  Akt :: "entity ⇒ bool"
  S473 :: "entity ⇒ bool"
  CarboxyTerminalHydrophobicMotif :: "entity ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  mTOR :: "entity ⇒ bool"
  DNA_PK :: "entity ⇒ bool"
  Stimulates :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  FullActivity :: "entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  PIK3 :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  PartialActivation :: "event ⇒ bool"
  LeadsTo :: "event ⇒ event ⇒ bool"
  Bound :: "entity ⇒ bool"

(* Explanation 1: Phosphorylation of Akt at S473 in the carboxy-terminal hydrophobic motif, either by mTOR or by DNA-PK stimulates full Akt activity. *)
axiomatization where
  explanation_1: "∃x y z w e. Phosphorylation x ∧ Akt y ∧ S473 z ∧ CarboxyTerminalHydrophobicMotif w ∧ At x z ∧ In x w ∧ (mTOR x ∨ DNA_PK x) ∧ Stimulates e ∧ Agent e x ∧ Patient e y ∧ FullActivity y"

(* Explanation 2: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane w ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ PartialActivation e2 ∧ LeadsTo e1 e2"

theorem hypothesis:
  assumes asm: "Phosphorylation x ∧ Akt y ∧ Bound y"
  (* Hypothesis: Phosphorylation of bound Akt stimulates full activity of Akt. *)
  shows "∃x y e. Phosphorylation x ∧ Akt y ∧ Bound y ∧ Stimulates e ∧ Agent e x ∧ Patient e y ∧ FullActivity y"
proof -
  (* From the premise, we have known information about Phosphorylation, Akt, and Bound. *)
  from asm have "Phosphorylation x ∧ Akt y ∧ Bound y" by simp
  (* Explanation 1 provides a logical relation: Implies(A, D), which means Phosphorylation of Akt at S473 in the carboxy-terminal hydrophobic motif implies Full Akt activity is stimulated. *)
  (* Since we have Phosphorylation x and Akt y, we can infer that FullActivity y is stimulated. *)
  from explanation_1 have "∃e. Stimulates e ∧ Agent e x ∧ Patient e y ∧ FullActivity y" sledgehammer
  (* Combine the known information with the inferred result to satisfy the hypothesis. *)
  then have "∃x y e. Phosphorylation x ∧ Akt y ∧ Bound y ∧ Stimulates e ∧ Agent e x ∧ Patient e y ∧ FullActivity y" <ATP>
  then show ?thesis <ATP>
qed

end
