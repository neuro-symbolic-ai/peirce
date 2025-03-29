theory clinical_71_5
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
  Mediate :: "event ⇒ bool"
  Recruitment :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  For :: "entity ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  T308 :: "entity ⇒ bool"
  ActivationLoop :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  LeadTo :: "event ⇒ bool"
  PartialActivation :: "event ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane w ∧ PDK1 y ∧ AKT z ∧ Provide e1 ∧ Mediate e2 ∧ Recruitment e3 ∧ Agent e1 x ∧ Patient e1 y ∧ Agent e2 x ∧ Patient e2 z ∧ Agent e3 w ∧ Patient e3 w ∧ DockingSite y ∧ For y z"

(* Explanation 2: PKB/Akt binds to PIP3 at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2 e3 e4. PKB_Akt x ∧ PIP3 y ∧ PlasmaMembrane z ∧ PDK1 w ∧ T308 y ∧ ActivationLoop z ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ At y z ∧ Allow e2 ∧ Access e3 ∧ Phosphorylate e4 ∧ Agent e2 x ∧ Patient e2 w ∧ Agent e3 w ∧ Patient e3 y ∧ Agent e4 w ∧ Patient e4 y ∧ In y z ∧ LeadTo e4 ∧ PartialActivation e4 ∧ Agent e4 x"

theorem hypothesis:
  assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation *)
  shows "∃x y z e1 e2. PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z ∧ Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ LeadTo e2 ∧ PartialActivation e2 ∧ Agent e2 x"
proof -
  (* From the premise, we have known information about PKB_Akt, DockingSite, PIK3, and PlasmaMembrane. *)
  from asm have "PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z" by blast
  (* Explanation 2 provides that PKB/Akt binds to PIP3 at the plasma membrane, leading to partial PKB/Akt activation. *)
  (* We have a derived implication: Implies(D, F), which states that if PKB/Akt binds to PIP3 at the plasma membrane, it leads to partial PKB/Akt activation. *)
  (* Since we have PKB_Akt x and PlasmaMembrane z, we can infer that PKB/Akt binds to the docking site on PIK3 at the plasma membrane, leading to partial activation. *)
  then have "Bind e1 ∧ Agent e1 x ∧ Patient e1 y ∧ On y z ∧ LeadTo e2 ∧ PartialActivation e2 ∧ Agent e2 x" sledgehammer
  then show ?thesis <ATP>
qed

end
