theory clinical_76_3
imports Main

begin

typedecl entity
typedecl event

consts
  Binding :: "entity ⇒ bool"
  Subunit :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Relieve :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Inhibition :: "entity ⇒ bool"
  Mediate :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Activation :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyse :: "event ⇒ bool"
  ConvertTo :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃x y z w v e1 e2. Binding x ∧ Subunit y ∧ P85 y ∧ P110 z ∧ PI3K w ∧ PlasmaMembrane v ∧ Relieve e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Inhibition z ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 w ∧ To w v"

(* Explanation 2: The activation of the p110 subunit is necessary for it to catalyze the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3) and to mediate the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_2: "∀x y z w v u e1 e2. Activation x ∧ Subunit y ∧ P110 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ⟶ (Catalyse e1 ∧ Agent e1 y ∧ Patient e1 z ∧ ConvertTo z w ∧ Mediate e2 ∧ Agent e2 y ∧ Patient e2 v ∧ To v u)"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
  shows "∃x y z e1 e2. Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ ConvertTo z w ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 v ∧ To v u"
proof -
  (* From the known information, we have Subunit x, PIK3 y, PIP2 z, PIP3 w, PI3K v, and PlasmaMembrane u. *)
  from asm have "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u" by auto
  
  (* Explanation 2 provides a logical relation: Implies(D, And(E, C)), which means activation of the p110 subunit implies catalyze the conversion of PIP2 to PIP3 and recruitment of PI3K to the plasma membrane. *)
  (* We need to show that the p110 subunit catalyzes the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to the plasma membrane. *)
  
  (* From explanation_2, we have: 
     Activation x ∧ Subunit y ∧ P110 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ⟶ 
     (Catalyse e1 ∧ Agent e1 y ∧ Patient e1 z ∧ ConvertTo z w ∧ Mediate e2 ∧ Agent e2 y ∧ Patient e2 v ∧ To v u) *)
  
  (* Since we have Subunit x and the other conditions from the premise, we can infer the activation of the p110 subunit. *)
  (* Therefore, we can apply the implication from explanation_2 to conclude the catalysis and mediation. *)
  
  then have "Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ ConvertTo z w ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 v ∧ To v u" sledgehammer
  
  (* Combining with the known information, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
