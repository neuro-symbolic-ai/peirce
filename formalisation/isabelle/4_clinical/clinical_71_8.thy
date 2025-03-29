theory clinical_71_8
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
  Recruitment :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Provide :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  For :: "entity ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  LeadTo :: "event ⇒ event ⇒ bool"
  Activation :: "event ⇒ bool"
  Partial :: "event ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 mediates the recruitment of PI3K to the plasma membrane and provides a docking site on PI3K for PDK1 and AKT. *)
axiomatization where
  explanation_1: "∃x y z w v u t e1 e2 e3 s. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane v ∧ PDK1 u ∧ AKT t ∧ Mediate e1 ∧ Agent e1 x ∧ Recruitment e2 ∧ Patient e2 w ∧ To w v ∧ Provide e3 ∧ Agent e3 x ∧ DockingSite s ∧ On s w ∧ For s u ∧ For s t"

(* Explanation 2: PKB/Akt binds to the docking site on PI3K at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃x y z w u v l e1 e2 e3 e4 e5. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ PDK1 u ∧ T308 v ∧ Activation e5 ∧ Partial e5 ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Allow e2 ∧ Agent e2 u ∧ Access e3 ∧ Agent e3 u ∧ Phosphorylate e4 ∧ Agent e4 u ∧ Patient e4 v ∧ In v l ∧ LeadTo e2 e5"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation. *)
  shows "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Activation e2 ∧ Partial e2 ∧ LeadTo e1 e2"
proof -
  (* From the premise, we have known information about PKB_Akt, DockingSite, PI3K, and PlasmaMembrane. *)
  from asm have "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w" by meson
  (* Explanation 2 provides a logical relation: Implies(D, F), which means PKB/Akt binds to the docking site on PI3K at the plasma membrane leads to partial PKB/Akt activation. *)
  (* We need to show that PKB/Akt binds to the docking site on PI3K at the plasma membrane. *)
  (* From explanation_2, we have the existence of such a binding event and its consequences. *)
  from explanation_2 obtain e1 e2 where
    "Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Activation e2 ∧ Partial e2 ∧ LeadTo e1 e2" sledgehammer
  (* Combine the known information and the obtained binding event to conclude the hypothesis. *)
  then have "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Activation e2 ∧ Partial e2 ∧ LeadTo e1 e2" <ATP>
  then show ?thesis <ATP>
qed

end
