theory clinical_76_1
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
  Recruitment :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Activated :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Conversion :: "event ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃x y z w v e1 e2. Binding x ∧ Subunit y ∧ P85 y ∧ P110 z ∧ PI3K w ∧ PlasmaMembrane v ∧ Relieves e1 ∧ Agent e1 x ∧ Inhibition e1 z ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 w ∧ To w v"

(* Explanation 2: The activated p110 subunit catalyses the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3) *)
axiomatization where
  explanation_2: "∃x y z e. Subunit x ∧ P110 x ∧ Activated x ∧ PIP2 y ∧ PIP3 z ∧ Catalyse e ∧ Agent e x ∧ Conversion e y z"

(* Explanation 3: The activated p110 subunit also mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_3: "∃x y z e. Subunit x ∧ P110 x ∧ Activated x ∧ PI3K y ∧ PlasmaMembrane z ∧ Mediates e ∧ Agent e x ∧ Recruitment e y ∧ To y z"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
  shows "∃x y z e1 e2. Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Conversion e1 z w ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v ∧ To v u"
proof -
  (* From the known information, we have Subunit x, PIK3 y, PIP2 z, PIP3 w, PI3K v, and PlasmaMembrane u. *)
  from asm have "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u" by blast
  (* Explanation 2 states that the activated p110 subunit catalyses the conversion of PIP2 to PIP3. *)
  (* This corresponds to logical proposition D and E, with the relation Implies(D, E). *)
  (* Since we have Subunit x and PIP2 z, PIP3 w, we can infer the conversion. *)
  then have "Catalyse e1 ∧ Agent e1 x ∧ Conversion e1 z w" sledgehammer
  (* Explanation 3 states that the activated p110 subunit mediates the recruitment of PI3K to the plasma membrane. *)
  (* This corresponds to logical proposition D and C, with the relation Implies(D, C). *)
  (* Since we have Subunit x, PI3K v, and PlasmaMembrane u, we can infer the recruitment. *)
  then have "Mediates e2 ∧ Agent e2 x ∧ Recruitment e2 v ∧ To v u" <ATP>
  (* Combining both inferences, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
