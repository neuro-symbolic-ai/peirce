theory clinical_76_7
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
  Relieve :: "event ⇒ bool"
  Inhibition :: "entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Activation :: "event ⇒ bool"
  Lead :: "event ⇒ event ⇒ bool"
  Directly :: "event ⇒ bool"
  Catalysis :: "event ⇒ bool"
  Convert :: "entity ⇒ entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  PIP :: "entity ⇒ bool"
  Recruitment :: "entity ⇒ entity ⇒ bool"
  Mediation :: "event ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Mediate :: "event ⇒ bool"

(* Explanation 1: The binding of the p85 subunit to the p110 subunit is necessary to relieve the inhibition of p110, which allows the activation of the p110 subunit. *)
axiomatization where
  explanation_1: "∃x y z e1 e2 e3. P85Subunit x ∧ P110Subunit y ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Necessary e1 ∧ Relieve e2 ∧ Inhibition z ∧ Patient e2 z ∧ Allow e3 ∧ Activation e3 ∧ Agent e3 y"

(* Explanation 2: The activation of the p110 subunit directly leads to the catalysis of the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3). *)
axiomatization where
  explanation_2: "∃x y z e1 e2. P110Subunit x ∧ PIP2 y ∧ PIP3 z ∧ Activation e1 ∧ Agent e1 x ∧ Lead e1 e2 ∧ Directly e1 ∧ Catalysis e2 ∧ Convert y z"

(* Explanation 3: The activation of the p110 subunit directly leads to the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. P110Subunit x ∧ PI3K y ∧ PlasmaMembrane z ∧ Activation e1 ∧ Agent e1 x ∧ Lead e1 e2 ∧ Directly e1 ∧ Mediation e2 ∧ Recruitment y z"

(* Explanation 4: The binding of the p85 subunit to the p110 subunit is necessary for the activation of the p110 subunit, which directly leads to the catalysis of the conversion of PIP2 to PIP. *)
axiomatization where
  explanation_4: "∃x y z w e1 e2 e3. P85Subunit x ∧ P110Subunit y ∧ PIP2 z ∧ PIP w ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Necessary e1 ∧ Activation e2 ∧ Agent e2 y ∧ Lead e2 e3 ∧ Directly e2 ∧ Catalysis e3 ∧ Convert z w"

theorem hypothesis:
  assumes asm: "P110Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. P110Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Convert z w ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 v ∧ Recruitment v u"
proof -
  (* From the known information, we have P110Subunit x, PIK3 y, PIP2 z, PIP3 w, PI3K v, and PlasmaMembrane u. *)
  from asm have "P110Subunit x ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u" by auto
  (* Explanation 2 states that the activation of the p110 subunit directly leads to the catalysis of the conversion of PIP2 to PIP3. *)
  (* This implies that if the p110 subunit is activated, it catalyses the conversion of PIP2 to PIP3. *)
  (* Explanation 3 states that the activation of the p110 subunit directly leads to the mediation of the recruitment of PI3K to the plasma membrane. *)
  (* This implies that if the p110 subunit is activated, it mediates the recruitment of PI3K to the plasma membrane. *)
  (* Using the logical relations, we can infer that the activation of the p110 subunit leads to both the catalysis and mediation. *)
  then have "Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Convert z w ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 v ∧ Recruitment v u" sledgehammer
  then show ?thesis <ATP>
qed

end
