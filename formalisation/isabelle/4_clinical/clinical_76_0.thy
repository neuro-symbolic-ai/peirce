theory clinical_76_0
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
  Catalyses :: "event ⇒ bool"
  Conversion :: "event ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z w v e1 e2. Binding x ∧ Subunit y ∧ P85 y ∧ P110 z ∧ PI3K w ∧ PlasmaMembrane v ∧ Relieves e1 ∧ Agent e1 x ∧ Inhibition e1 z ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 w v"

(* Explanation 2: The activated p110 subunit catalyses the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3). *)
axiomatization where
  explanation_2: "∃x y z e. Subunit x ∧ P110 x ∧ Activated x ∧ PIP2 y ∧ PIP3 z ∧ Catalyses e ∧ Agent e x ∧ Conversion e y z"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyses e1 ∧ Agent e1 x ∧ Conversion e1 z w ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v u"
proof -
  (* From the known information, we have Subunit x, PIK3 y, PIP2 z, PIP3 w, PI3K v, and PlasmaMembrane u. *)
  from asm have "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u" by simp
  
  (* Explanation 1 provides that binding of the p85 subunit and p110 mediates the recruitment of PI3K to the plasma membrane. *)
  (* This implies that there exists an event e2 where Mediates e2, Agent e2 x, and Recruitment e2 v u. *)
  from explanation_1 have "∃e2. Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v u" sledgehammer
  
  (* Explanation 2 provides that the activated p110 subunit catalyses the conversion of PIP2 to PIP3. *)
  (* This implies that there exists an event e1 where Catalyses e1, Agent e1 x, and Conversion e1 z w. *)
  from explanation_2 have "∃e1. Catalyses e1 ∧ Agent e1 x ∧ Conversion e1 z w" <ATP>
  
  (* Combining the results from explanation_1 and explanation_2, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
