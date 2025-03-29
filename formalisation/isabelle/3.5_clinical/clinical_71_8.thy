theory clinical_71_8
imports Main


begin

typedecl entity
typedecl event

consts
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  Provides :: "event ⇒ bool"
  Mediates :: "event ⇒ bool"
  Recruitment :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Location :: "entity ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  T308 :: "entity ⇒ bool"
  ActivationLoop :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Allows :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  LeadingTo :: "event ⇒ entity ⇒ bool"
  PartialActivation :: "entity ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT *)
axiomatization where
  explanation_1: "∀x y z w v e1 e2 e3. PIP2 x ∧ PIP3 y ∧ PI3K z ∧ PlasmaMembrane w ∧ DockingSite v ∧ PDK1 e1 ∧ AKT e2 ∧ Conversion e3 ∧ Provides e3 ∧ Mediates e3 ∧ Recruitment e3 ∧ Agent e3 x ∧ Patient e3 y ∧ Location y w ∧ Location v z ∧ Location v e1 ∧ Location v e2"

(* Explanation 2: PKB/Akt binds to PIP3 at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation *)
axiomatization where
  explanation_2: "∃x y z w v e1 e2 e3 e4. PKB_Akt x ∧ PIP3 y ∧ PlasmaMembrane z ∧ PDK1 w ∧ T308 v ∧ ActivationLoop e1 ∧ Binds e2 ∧ Allows e2 ∧ Access e2 ∧ Phosphorylate e2 ∧ LeadingTo e2 z ∧ Agent e2 x ∧ Patient e2 y ∧ Location y z ∧ Location w v"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane e"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation *)
  shows "∃x y z e. PKB_Akt x ∧ DockingSite y ∧ PI3K z ∧ PlasmaMembrane e ∧ Binds e ∧ Agent e x ∧ Patient e y ∧ Location y z ∧ LeadingTo e (PartialActivation x)"
  sledgehammer
  oops

end
