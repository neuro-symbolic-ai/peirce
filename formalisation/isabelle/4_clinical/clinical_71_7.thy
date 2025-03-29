theory clinical_71_7
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
  Mediates :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Provides :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  For :: "entity ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  In :: "entity ⇒ string ⇒ bool"
  LeadTo :: "event ⇒ event ⇒ bool"
  Activation :: "event ⇒ bool"
  Partial :: "event ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 mediates the recruitment of PI3K to the plasma membrane and provides a docking site on PI3K for PDK1 and AKT. *)
axiomatization where
  explanation_1: "∃x y z w v u t e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane v ∧ PDK1 u ∧ AKT t ∧ Mediates e1 ∧ Agent e1 x ∧ Patient e1 w ∧ To w v ∧ Provides e2 ∧ Agent e2 x ∧ DockingSite e3 ∧ On e3 w ∧ For e3 u ∧ For e3 t"

(* Explanation 2: PKB/Akt binds to the docking site on PI3K at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "(∃x y z w u v e1 e2 e3 e4 e5. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ PDK1 u ∧ T308 v ∧ Activation e5 ∧ Partial e5 ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Allow e2 ∧ Agent e2 e1 ∧ Access e3 ∧ Agent e3 u ∧ Phosphorylate e4 ∧ Agent e4 u ∧ Patient e4 v ∧ In v 'activation loop' ∧ LeadTo e2 e5)"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation. *)
  shows "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Activation e2 ∧ Partial e2 ∧ LeadTo e1 e2"
proof -
  (* From the premise, we have known information about PKB_Akt, DockingSite, PI3K, and PlasmaMembrane. *)
  from asm have "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w" <ATP>
  (* Explanation 2 provides the logical relation Implies(D, F), which states that if PKB/Akt binds to the docking site on PI3K at the plasma membrane, it leads to partial PKB/Akt activation. *)
  (* We need to show that PKB/Akt binds to the docking site on PI3K at the plasma membrane, which is part of the hypothesis. *)
  (* Explanation 2 also provides the necessary conditions for binding and activation. *)
  from explanation_2 have "∃e1 e2. Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Activation e2 ∧ Partial e2 ∧ LeadTo e1 e2" <ATP>
  then show ?thesis <ATP>
qed

end
