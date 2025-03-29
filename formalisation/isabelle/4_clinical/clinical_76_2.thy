theory clinical_76_2
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
  Relieves :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Inhibition :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Recruitment :: "event ⇒ entity ⇒ entity ⇒ bool"
  Activated :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Conversion :: "event ⇒ entity ⇒ entity ⇒ bool"
  ActOn :: "event ⇒ entity ⇒ bool"
  Convert :: "event ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z v u e1 e2. Binding x ∧ Subunit y ∧ P85 y ∧ P110 z ∧ PI3K v ∧ PlasmaMembrane u ∧ Relieves e1 ∧ Agent e1 x ∧ Inhibition e1 z ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v u"

(* Explanation 2: The activated p110 subunit catalyses the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3) by acting on PIP2 and converting it to PIP, also mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z w v u e1 e2. Subunit x ∧ P110 x ∧ Activated x ∧ PIP2 y ∧ PIP3 z ∧ PI3K w ∧ PlasmaMembrane v ∧ Catalyse e1 ∧ Agent e1 x ∧ Conversion e1 y z ∧ ActOn e1 y ∧ Convert e1 y z ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 w v"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Conversion e1 z w ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v u"
proof -
  (* From the known information, we have Subunit x, PIK3 y, PIP2 z, PIP3 w, PI3K v, and PlasmaMembrane u. *)
  from asm have "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u" by auto
  
  (* Explanation 2 provides that an activated p110 subunit catalyses the conversion of PIP2 to PIP3 and mediates the recruitment of PI3K to the plasma membrane. *)
  (* We have logical relations Implies(D, E) and Implies(D, C) from explanation 2. *)
  (* Since we have Subunit x and PIK3 y, we can infer that x is the activated p110 subunit. *)
  (* Therefore, we can infer the conversion of PIP2 to PIP3 and the recruitment of PI3K to the plasma membrane. *)
  then have "Catalyse e1 ∧ Agent e1 x ∧ Conversion e1 z w ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v u" sledgehammer
  
  (* Combining all the information, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
