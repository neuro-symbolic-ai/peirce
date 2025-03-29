theory clinical_71_6
imports Main


begin

typedecl entity
typedecl event

consts
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  T308 :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Provides :: "event ⇒ bool"
  MediatesRecruitment :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  For :: "event ⇒ entity ⇒ entity ⇒ bool"
  Binds :: "event ⇒ bool"
  At :: "event ⇒ entity ⇒ entity ⇒ bool"
  Allowing :: "event ⇒ entity ⇒ bool"
  Access :: "event ⇒ entity ⇒ bool"
  Phosphorylate :: "event ⇒ entity ⇒ entity ⇒ bool"
  In :: "event ⇒ entity ⇒ bool"
  LeadingTo :: "event ⇒ entity ⇒ bool"
  PartialActivation :: "entity ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT *)
axiomatization where
  explanation_1: "∃x y z w v e1 e2. PIP2 x ∧ PIP3 y ∧ Conversion e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Provides e1 ∧ MediatesRecruitment e1 ∧ Agent e2 PI3K z ∧ Patient e2 PlasmaMembrane w ∧ Provides e1 ∧ DockingSite v ∧ For e1 PDK1 AKT"

(* Explanation 2: PKB/Akt binds to PIP3 at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation *)
axiomatization where
  explanation_2: "∃x y z w v e. PKB_Akt x ∧ PIP3 y ∧ PlasmaMembrane z ∧ Binds e ∧ Agent e x ∧ Patient e y ∧ At e y z ∧ Allowing e PDK1 ∧ Access e PDK1 ∧ Phosphorylate e PDK1 T308 ∧ In e ''activation loop'' ∧ LeadingTo e PartialActivation x"


theorem hypothesis:
 assumes asm: "PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation *)
 shows "∃x y z e. PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z ∧ Binds e ∧ Agent e x ∧ Patient e y ∧ At e y z ∧ LeadingTo e PartialActivation x"
proof -
  (* From the premise, we know that PKB/Akt binds to the docking site on PIK3 at the plasma membrane. *)
  have "PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z" <ATP>
  (* There is a logical relation Implies(D, F), Implies(PKB/Akt binds to PIP3 at the plasma membrane, partial PKB/Akt activation) *)
  (* We can infer that PKB/Akt activation is partial. *)
  then have "PartialActivation x" <ATP>
  (* We also have PKB/Akt x and DockingSite y. *)
  then have "PKB_Akt x ∧ DockingSite y" by auto
  (* Since PKB/Akt activation is partial, we can conclude that PKB/Akt binds to the docking site on PIK3 at the plasma membrane. *)
  then have "PKB_Akt x ∧ DockingSite y ∧ PIK3 z ∧ PlasmaMembrane z ∧ Binds e ∧ Agent e x ∧ Patient e y ∧ At e y z ∧ LeadingTo e PartialActivation x" by auto
  then show ?thesis by auto
qed

end
