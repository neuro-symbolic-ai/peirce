theory clinical_71_9
imports Main

begin

typedecl entity
typedecl event

consts
  Conversion :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  Mediate :: "event ⇒ bool"
  Recruitment :: "event ⇒ bool"
  Provide :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  On :: "event ⇒ entity ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  Lead :: "event ⇒ bool"
  Directly :: "event ⇒ bool"
  Allow :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  ActivationLoop :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  At :: "event ⇒ entity ⇒ bool"
  PartialActivation :: "entity ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 mediates the recruitment of PI3K to the plasma membrane and provides a docking site on PI3K for PDK1 and AKT. *)
axiomatization where
  explanation_1: "∃x y z w v u t e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane v ∧ PDK1 u ∧ AKT t ∧ Mediate e1 ∧ Agent e1 x ∧ Recruitment e2 ∧ Agent e2 w ∧ Patient e2 v ∧ Provide e3 ∧ Agent e3 x ∧ DockingSite w ∧ On e3 w ∧ For e3 u ∧ For e3 t"

(* Explanation 2: PKB/Akt binds to the docking site on PI3K at the plasma membrane, which directly leads to partial PKB/Akt activation by allowing PDK1 to access and phosphorylate T308 in the “activation loop. *)
axiomatization where
  explanation_2: "∃x y z w u v t e1 e2 e3 e4. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ PDK1 u ∧ T308 v ∧ ActivationLoop t ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On e1 z ∧ At e1 w ∧ Lead e2 ∧ Agent e2 x ∧ Patient e2 x ∧ Directly e2 ∧ Allow e3 ∧ Agent e3 x ∧ Patient e3 u ∧ Access e4 ∧ Phosphorylate e4 ∧ Agent e4 u ∧ Patient e4 v ∧ In v t"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w"
  (* Hypothesis: PKB/Akt binds to the docking site on PI3K at the plasma membrane leading to a partial PKB/Akt activation *)
  shows "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On e1 z ∧ At e1 w ∧ Lead e2 ∧ Agent e2 x ∧ Patient e2 x ∧ PartialActivation x"
proof -
  (* From the premise, we have known information about PKB_Akt, DockingSite, PI3K, and PlasmaMembrane. *)
  from asm have "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w" by blast
  (* Explanation 2 provides a logical relation: Implies(D, And(E, F)), which means PKB/Akt binds to the docking site on PI3K at the plasma membrane implies partial PKB/Akt activation and PDK1 accesses and phosphorylates T308 in the “activation loop”. *)
  (* We need to show that PKB/Akt binds to the docking site on PI3K at the plasma membrane, which is part of the hypothesis. *)
  (* From explanation_2, we can infer the binding event and its consequences. *)
  then have "Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On e1 z ∧ At e1 w ∧ Lead e2 ∧ Agent e2 x ∧ Patient e2 x ∧ PartialActivation x" sledgehammer
  then show ?thesis <ATP>
qed

end
