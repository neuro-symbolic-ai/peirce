theory clinical_76_10
imports Main

begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  Activation :: "event ⇒ bool"
  Catalysis :: "event ⇒ bool"
  Mediation :: "event ⇒ bool"
  Necessary :: "event ⇒ event ⇒ bool"
  LeadsTo :: "event ⇒ event ⇒ bool"
  Ensures :: "event ⇒ event ⇒ bool"
  RelieveInhibition :: "event ⇒ bool"
  Conversion :: "entity ⇒ entity ⇒ bool"
  Recruitment :: "entity ⇒ entity ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  P110Subunit :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The binding of the p85 subunit to the p110 subunit is necessary to relieve the inhibition of p110, which allows the activation of the p110 subunit. *)
axiomatization where
  explanation_1: "∀e1 e2 e3 x y. Binding e1 ∧ P85Subunit x ∧ P110Subunit y ∧ To x y ∧ Necessary e1 e2 ∧ RelieveInhibition e2 ∧ LeadsTo e2 e3 ∧ Activation e3 ∧ P110Subunit y"

(* Explanation 2: The activation of the p110 subunit directly leads to the catalysis of the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3). *)
axiomatization where
  explanation_2: "∀e1 e2 x y. Activation e1 ∧ P110Subunit x ∧ LeadsTo e1 e2 ∧ Catalysis e2 ∧ Conversion y z ∧ PIP2 y ∧ PIP3 z"

(* Explanation 3: The activation of the p110 subunit directly leads to the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_3: "∀e1 e2 x y z. Activation e1 ∧ P110Subunit x ∧ LeadsTo e1 e2 ∧ Mediation e2 ∧ Recruitment y z ∧ PI3K y ∧ PlasmaMembrane z"

(* Explanation 4: The binding of the p85 subunit to the p110 subunit is necessary for the activation of the p110 subunit, which directly leads to both the catalysis of the conversion of PIP2 to PIP3 and the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_4: "∀e1 e2 e3 e4 x y z. Binding e1 ∧ P85Subunit x ∧ P110Subunit y ∧ To x y ∧ Necessary e1 e2 ∧ Activation e2 ∧ P110Subunit y ∧ LeadsTo e2 e3 ∧ Catalysis e3 ∧ Conversion z w ∧ PIP2 z ∧ PIP3 w ∧ LeadsTo e2 e4 ∧ Mediation e4 ∧ Recruitment v u ∧ PI3K v ∧ PlasmaMembrane u"

(* Explanation 5: Additionally, the activation of the p110 subunit ensures that both processes occur simultaneously. *)
axiomatization where
  explanation_5: "∀e1 e2 e3 x. Activation e1 ∧ P110Subunit x ∧ Ensures e1 e2 ∧ Ensures e1 e3 ∧ Catalysis e2 ∧ Mediation e3"

theorem hypothesis:
  assumes asm: "P110Subunit x"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃e1 e2 e3 y z. P110Subunit x ∧ Catalysis e1 ∧ Conversion y z ∧ PIP2 y ∧ PIP3 z ∧ Mediation e2 ∧ Recruitment x e3 ∧ PI3K x ∧ PlasmaMembrane e3"
  by (simp add: explanation_2 explanation_3)
  

end
