theory clinical_76_8
imports Main

begin

typedecl entity
typedecl event

consts
  P85Subunit :: "entity ⇒ bool"
  P110Subunit :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Necessary :: "event ⇒ bool"
  Inhibition :: "entity ⇒ entity ⇒ bool"
  Relieve :: "event ⇒ bool"
  Allows :: "event ⇒ bool"
  Activation :: "event ⇒ entity ⇒ bool"
  Leads :: "event ⇒ event ⇒ bool"
  Directly :: "event ⇒ bool"
  Catalysis :: "event ⇒ bool"
  Conversion :: "event ⇒ entity ⇒ entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Mediation :: "event ⇒ bool"
  Recruitment :: "event ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 1: The binding of the p85 subunit to the p110 subunit is necessary to relieve the inhibition of p110, which allows the activation of the p110 subunit. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. P85Subunit x ∧ P110Subunit y ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Necessary e1 ∧ Inhibition z y ∧ Relieve e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Allows e2 ∧ Activation e2 y"

(* Explanation 2: The activation of the p110 subunit directly leads to the catalysis of the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3). *)
axiomatization where
  explanation_2: "∃x y z e1 e2. P110Subunit x ∧ Activation e1 x ∧ PIP2 y ∧ PIP3 z ∧ Leads e1 e2 ∧ Directly e1 ∧ Catalysis e2 ∧ Conversion e2 y z"

(* Explanation 3: The activation of the p110 subunit directly leads to the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. P110Subunit x ∧ Activation e1 x ∧ PI3K y ∧ PlasmaMembrane z ∧ Leads e1 e2 ∧ Directly e1 ∧ Mediation e2 ∧ Recruitment e2 y z"

(* Explanation 4: The binding of the p85 subunit to the p110 subunit is necessary for the activation of the p110 subunit, which directly leads to both the catalysis of the conversion of PIP2 to PIP3 and the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_4: "∃x y z w v u e1 e2 e3. P85Subunit x ∧ P110Subunit y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Necessary e1 ∧ Activation e2 y ∧ Leads e2 e3 ∧ Directly e2 ∧ (Catalysis e3 ∧ Conversion e3 z w) ∧ (Mediation e3 ∧ Recruitment e3 v u)"

theorem hypothesis:
  assumes asm: "P110Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PI3K catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. P110Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalysis e1 ∧ Agent e1 x ∧ Conversion e1 z w ∧ Mediation e2 ∧ Agent e2 x ∧ Recruitment e2 v u"
proof -
  (* From the known information, we have P110Subunit x, PI3K y, PIP2 z, PIP3 w, PI3K v, and PlasmaMembrane u. *)
  from asm have "P110Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u" by auto
  (* Explanation 4 states that the binding of the p85 subunit to the p110 subunit is necessary for the activation of the p110 subunit, which directly leads to both the catalysis of the conversion of PIP2 to PIP3 and the mediation of the recruitment of PI3K to the plasma membrane. *)
  (* We can use the logical relation Implies(A, And(D, E)) from Explanation 4. *)
  (* Since we have P110Subunit x, we can infer the activation of the p110 subunit, which leads to both catalysis and mediation. *)
  then have "Catalysis e1 ∧ Conversion e1 z w ∧ Mediation e2 ∧ Recruitment e2 v u" sledgehammer
  (* Therefore, we can conclude that the p110 subunit of PI3K catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to the plasma membrane. *)
  then show ?thesis <ATP>
qed

end
