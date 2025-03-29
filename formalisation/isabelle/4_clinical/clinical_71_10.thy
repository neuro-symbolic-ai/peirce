theory clinical_71_10
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
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Provide :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  For :: "entity ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  Lead :: "event ⇒ bool"
  Directly :: "event ⇒ bool"
  PartialActivation :: "entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Phosphorylation :: "event ⇒ bool"
  NecessaryFor :: "event ⇒ bool ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 mediates the recruitment of PI3K to the plasma membrane and provides a docking site on PI3K for PDK1 and AKT. *)
axiomatization where
  explanation_1: "∃x y z w v u t e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane v ∧ PDK1 u ∧ AKT t ∧ Mediate e1 ∧ Agent e1 x ∧ Patient e1 w ∧ To w v ∧ Provide e2 ∧ Agent e2 x ∧ DockingSite e3 ∧ On e3 w ∧ For e3 u ∧ For e3 t"

(* Explanation 2: PKB/Akt binds to the docking site on PI3K at the plasma membrane, which directly leads to partial PKB/Akt activation by allowing PDK1 to access and phosphorylate T308 in the “activation loop. *)
axiomatization where
  explanation_2: "∃x y z w u v t e1 e2 e3 e4 e5. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ PDK1 u ∧ T308 v ∧ ActivationLoop t ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Lead e2 ∧ Agent e2 x ∧ Patient e2 x ∧ Directly e2 ∧ PartialActivation x ∧ Allow e3 ∧ Agent e3 x ∧ Patient e3 u ∧ Access e4 ∧ Agent e4 u ∧ Patient e4 v ∧ Phosphorylate e5 ∧ Agent e5 u ∧ Patient e5 v ∧ In v t"

(* Explanation 3: The phosphorylation of T308 by PDK1 is necessary for the partial activation of PKB/Akt. *)
axiomatization where
  explanation_3: "∀x y z e. Phosphorylation e ∧ T308 y ∧ PDK1 z ∧ Agent e z ∧ Patient e y ⟶ (NecessaryFor e (PartialActivation x))"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w"
  (* Hypothesis: PKB/Akt binds to the docking site on PI3K at the plasma membrane leading to a partial PKB/Akt activation *)
  shows "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Lead e2 ∧ Agent e2 e1 ∧ Patient e2 x ∧ PartialActivation x"
  sledgehammer
  oops

end
