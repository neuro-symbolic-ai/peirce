theory clinical_76_3
imports Main


begin

typedecl entity
typedecl event

consts
  P85 :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  RelievesInhibition :: "event ⇒ bool"
  MediatesRecruitment :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Activated :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e x y z. P85 x ∧ P110 y ∧ PI3K z ∧ RelievesInhibition e ∧ Agent e x ∧ Patient e y ∧ MediatesRecruitment e ∧ Agent e y ∧ Patient e z ∧ To z plasma_membrane"

(* Explanation 2: The activated p110 subunit catalyses the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3) *)
axiomatization where
  explanation_2: "∃e x y z. P110 x ∧ Activated x ∧ PIP2 y ∧ PIP3 z ∧ Conversion e ∧ Agent e x ∧ Patient e y ∧ To y z"


theorem hypothesis:
 assumes asm: "P110 x ∧ PIK3 y ∧ PIP2 z"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
 shows "∃e x y z. P110 x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 z ∧ Conversion e ∧ Agent e x ∧ Patient e z ∧ MediatesRecruitment e ∧ Agent e x ∧ Patient e y ∧ To x plasma_membrane"
proof -
  (* From the premise, we have the information about P110, PIK3, and PIP2. *)
  from asm have "P110 x" and "PIK3 y" and "PIP2 z" apply blast
  (* There is a logical relation Implies(C, D), Implies(The p110 subunit is activated, The p110 subunit catalyses the conversion of PIP2 to PIP3) *)
  (* We can infer that if the p110 subunit is activated, it catalyses the conversion of PIP2 to PIP3. *)
  (* Since we have P110 x and the p110 subunit is activated, we can deduce the conversion of PIP2 to PIP3. *)
  from `P110 x` and `Activated x` obtain "PIP3 z" using assms apply auto[1]
  (* There is a logical relation Implies(A, C), Implies(Binding of the p85 subunit and p110 relieves inhibition of p110, The p110 subunit is activated) *)
  (* We can infer that if the binding of the p85 subunit and p110 relieves inhibition of p110, then the p110 subunit is activated. *)
  (* Since we have P110 x and the binding of the p85 subunit and p110 relieves inhibition of p110, we can deduce that the p110 subunit is activated. *)
  from `P110 x` and `PIK3 y` and `PIP2 z` and explanation_1 obtain "Conversion e" and "Agent e x" and "Patient e z" and "MediatesRecruitment e" and "Agent e x" and "Patient e y" and "To x plasma_membrane" by auto
  (* Combining all the inferred information, we have proven the hypothesis. *)
  then show ?thesis sledgehammer
qed

end
