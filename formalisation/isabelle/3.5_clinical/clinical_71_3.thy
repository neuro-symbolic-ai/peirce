theory clinical_71_3
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
  Convert :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Recruitment :: "event ⇒ bool"
  At :: "event ⇒ entity ⇒ bool"
  PKB_Akt :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  Phosphorylate :: "event ⇒ bool"
  In :: "event ⇒ string ⇒ bool"
  PartialActivation :: "entity ⇒ bool"

(* Explanation 1: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT *)
axiomatization where
  explanation_1: "∀x y z w v e1 e2. PIP2 x ∧ PIP3 y ∧ PI3K z ∧ PlasmaMembrane w ∧ DockingSite v ∧ PDK1 e1 ∧ AKT e2 ⟶ (Convert e1 ∧ Agent e1 x ∧ Patient e1 y) ∧ (Recruitment e2 ∧ Agent e2 z ∧ Patient e2 w ∧ At e2 v)"

(* Explanation 2: PKB/Akt binds to PIP3 at the plasma membrane, allowing PDK1 to access and phosphorylate T308 in the “activation loop,” leading to partial PKB/Akt activation *)
axiomatization where
  explanation_2: "∃x y z w v e1 e2 e3. PKB_Akt x ∧ PIP3 y ∧ PlasmaMembrane z ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ At e1 z ∧ PDK1 w ∧ Access e2 ∧ Agent e2 w ∧ Patient e2 y ∧ Phosphorylate e3 ∧ Agent e3 w ∧ Patient e3 T308 ∧ In e3 ''activation loop'' ∧ PartialActivation x"


theorem hypothesis:
 assumes asm: "PKB_Akt x ∧ PIK3 y ∧ PlasmaMembrane z"
  (* Hypothesis: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation *)
 shows "∃x y z e. PKB_Akt x ∧ PIK3 y ∧ PlasmaMembrane z ∧ Binds e ∧ Agent e x ∧ Patient e y ∧ At e z ∧ DockingSite y ∧ PartialActivation x"
proof -
  (* From the premise, we have the information about PKB/Akt, PIK3, and the plasma membrane. *)
  from asm have "PKB_Akt x ∧ PIK3 y ∧ PlasmaMembrane z" <ATP>
  (* There is a logical relation Implies(D, F), Implies(PKB/Akt binds to PIP3 at the plasma membrane, partial PKB/Akt activation) *)
  (* We can infer that if PKB/Akt binds to PIK3 at the plasma membrane, there is a partial PKB/Akt activation. *)
  then have "PartialActivation x" <ATP>
  (* We also know that PKB/Akt binds to PIP3 at the plasma membrane. *)
  then have "Binds e ∧ Agent e x ∧ Patient e y ∧ At e z ∧ DockingSite y" <ATP>
  (* Combining all the information, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
