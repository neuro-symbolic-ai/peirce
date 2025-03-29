theory clinical_76_5
imports Main

begin

typedecl entity
typedecl event

consts
  Subunit :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Necessary :: "event ⇒ bool"
  Relieve :: "event ⇒ bool"
  Inhibition :: "entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Activation :: "event ⇒ bool"
  Essential :: "event ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Conversion :: "entity ⇒ entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Mediate :: "event ⇒ bool"
  Recruitment :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The binding of the p85 subunit to the p110 subunit is necessary to relieve the inhibition of p110, which allows the activation of the p110 subunit. *)
axiomatization where
  explanation_1: "∃x y z e1 e2 e3. Subunit x ∧ P85 y ∧ P110 z ∧ Binding e1 ∧ Agent e1 y ∧ Patient e1 z ∧ Necessary e1 ∧ Relieve e2 ∧ Inhibition z ∧ Allow e3 ∧ Activation e3"

(* Explanation 2: This activation is essential for the p110 subunit to catalyze the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3). *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. Activation e1 ∧ Essential e1 ∧ Subunit x ∧ P110 y ∧ PIP2 z ∧ PIP3 w ∧ Catalyse e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Conversion z w"

(* Explanation 3: The activation of the p110 subunit is necessary for it to mediate the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_3: "∃x y z w e1 e2. Activation e1 ∧ Necessary e1 ∧ Subunit x ∧ P110 y ∧ PI3K z ∧ PlasmaMembrane w ∧ Mediate e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Recruitment z w"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u"
  (* Hypothesis: The p110 subunit of PI3K catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Conversion z w ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 v ∧ Recruitment v u"
proof -
  (* From the explanation sentences, we know the logical relations and derived implications. *)
  (* Explanation 1 and 2 provide the necessary conditions for the activation of the p110 subunit. *)
  from explanation_1 have "∃x y z e1 e2 e3. Subunit x ∧ P85 y ∧ P110 z ∧ Binding e1 ∧ Agent e1 y ∧ Patient e1 z ∧ Necessary e1 ∧ Relieve e2 ∧ Inhibition z ∧ Allow e3 ∧ Activation e3" by blast
  (* Explanation 2 states that activation is essential for catalysis. *)
  from explanation_2 have "∃x y z w e1 e2. Activation e1 ∧ Essential e1 ∧ Subunit x ∧ P110 y ∧ PIP2 z ∧ PIP3 w ∧ Catalyse e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Conversion z w" by blast
  (* Explanation 3 states that activation is necessary for mediation. *)
  from explanation_3 have "∃x y z w e1 e2. Activation e1 ∧ Necessary e1 ∧ Subunit x ∧ P110 y ∧ PI3K z ∧ PlasmaMembrane w ∧ Mediate e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Recruitment z w" by blast
  (* Using the logical relations, we can infer the hypothesis. *)
  (* Activation leads to both catalysis and mediation. *)
  then have "∃x y z e1 e2. Subunit x ∧ PI3K y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Conversion z w ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 v ∧ Recruitment v u" sledgehammer
  then show ?thesis <ATP>
qed

end
