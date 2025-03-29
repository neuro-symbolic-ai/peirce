theory clinical_76_1
imports Main


begin

typedecl entity
typedecl event

consts
  P85Subunit :: "entity ⇒ bool"
  P110Subunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  RelievesInhibition :: "event ⇒ bool"
  MediatesRecruitment :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  ActivatedP110Subunit :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e x y z. P85Subunit x ∧ P110Subunit y ∧ PI3K z ∧ RelievesInhibition e ∧ Agent e x ∧ Patient e y ∧ MediatesRecruitment e ∧ Agent e y ∧ Patient e z ∧ To z PlasmaMembrane"

(* Explanation 2: The activated p110 subunit catalyses the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3) *)
axiomatization where
  explanation_2: "∃e x y z. ActivatedP110Subunit x ∧ PIP2 y ∧ PIP3 z ∧ Conversion e ∧ Agent e x ∧ Patient e y ∧ Patient e z"


theorem hypothesis:
 assumes asm: "P110Subunit x ∧ PI3K y ∧ PIP2 z"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
 shows "∃e x y z. P110Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 z ∧ Conversion e ∧ Agent e x ∧ Patient e z ∧ MediatesRecruitment e ∧ Agent e x ∧ Patient e y ∧ To z PlasmaMembrane"
proof -
  (* From the premise, we have the information about the p110 subunit, PI3K, and PIP2. *)
  from asm have "P110Subunit x ∧ PI3K y ∧ PIP2 z" <ATP>
  (* There is a logical relation Implies(D, E), Implies(The activated p110 subunit, Catalyses the conversion of PIP2 to PIP3) *)
  (* We need to connect the premise with the hypothesis. *)
  (* We know that the activated p110 subunit catalyses the conversion of PIP2 to PIP3. *)
  (* Therefore, we can infer the conversion of PIP2 to PIP3. *)
  then obtain e where "Conversion e ∧ Agent e x ∧ Patient e z ∧ Patient e y" <ATP>
  (* Now, we have the conversion of PIP2 to PIP3. *)
  (* We also know that the binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  (* This implies that the p110 subunit mediates the recruitment of PI3K to the plasma membrane. *)
  then obtain e' where "MediatesRecruitment e' ∧ Agent e' x ∧ Patient e' y ∧ To y PlasmaMembrane" <ATP>
  (* Combining the information about the conversion and recruitment, we can derive the hypothesis. *)
  then show ?thesis <ATP>
qed

end
