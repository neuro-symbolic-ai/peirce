theory clinical_71_3
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
  Provide :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Recruitment :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  DockingSite :: "event ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  T308 :: "entity ⇒ bool"
  ActivationLoop :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Activation :: "event ⇒ bool"
  Partial :: "event ⇒ bool"
  LeadTo :: "event ⇒ event ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT. *)
axiomatization where
  explanation_1: "∃x y z w v u t e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane v ∧ PDK1 u ∧ AKT t ∧ Provide e1 ∧ Agent e1 x ∧ Recruitment e2 ∧ Patient e2 w ∧ To w v ∧ Provide e3 ∧ DockingSite e3 ∧ For e3 u ∧ For e3 t"

(* Explanation 2: PKB/Akt binds to PIP3 at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃x y z w u v e1 e2 e3 e4 e5. PKB_Akt x ∧ PIP3 y ∧ PlasmaMembrane z ∧ PDK1 w ∧ T308 u ∧ ActivationLoop v ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ At y z ∧ Allow e2 ∧ Access e3 ∧ Agent e3 w ∧ Phosphorylate e4 ∧ Agent e4 w ∧ Patient e4 u ∧ In u v ∧ Activation e5 ∧ Partial e5 ∧ LeadTo e1 e5"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane w"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation. *)
  shows "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ At y w ∧ Activation e2 ∧ Partial e2 ∧ LeadTo e1 e2"
  sledgehammer
  oops

end
