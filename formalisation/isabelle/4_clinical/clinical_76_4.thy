theory clinical_76_4
imports Main

begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  Subunit :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Of :: "entity ⇒ entity ⇒ bool"
  Necessary :: "event ⇒ bool"
  Relieve :: "event ⇒ bool"
  Inhibition :: "event ⇒ entity ⇒ bool"
  Allow :: "event ⇒ bool"
  Activation :: "event ⇒ bool"
  Mediate :: "event ⇒ bool"
  Recruitment :: "event ⇒ entity ⇒ entity ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Conversion :: "event ⇒ entity ⇒ entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit and p110 is necessary to relieve inhibition of p110, which allows the activation of the p110 subunit and mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z w v e1 e2 e3. Binding e1 ∧ Subunit x ∧ P85 y ∧ P110 z ∧ PI3K w ∧ PlasmaMembrane v ∧ Of x y ∧ Of x z ∧ Necessary e1 ∧ Relieve e2 ∧ Inhibition e2 z ∧ Allow e3 ∧ Activation e3 ∧ Mediate e3 ∧ Recruitment e3 w v"

(* Explanation 2: The activation of the p110 subunit is necessary for it to catalyze the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3) and to mediate the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z w v u e1 e2 e3. Activation e1 ∧ Subunit x ∧ P110 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Of x y ∧ Necessary e1 ∧ Catalyse e2 ∧ Agent e2 x ∧ Conversion e2 z w ∧ Mediate e3 ∧ Agent e3 x ∧ Recruitment e3 v u"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Of x y"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Catalyse e1 ∧ Agent e1 x ∧ Conversion e1 z w ∧ Mediate e2 ∧ Agent e2 x ∧ Recruitment e2 v u ∧ Of x y"
proof -
  (* From the explanation sentences, we know that the activation of the p110 subunit is necessary for catalyzing the conversion of PIP2 to PIP3 and mediating the recruitment of PI3K to the plasma membrane. *)
  (* We have logical relations: Implies(C, And(E, D)), which means activation of the p110 subunit implies both catalyzing the conversion of PIP2 to PIP3 and recruitment of PI3K to the plasma membrane. *)
  (* We also have Implies(C, E) and Implies(C, D) as derived implications. *)
  (* From explanation_2, we have the existence of such activation, catalysis, and mediation events. *)
  from explanation_2 obtain e1 e2 e3 where
    "Activation e1 ∧ Subunit x ∧ P110 y ∧ PIP2 z ∧ PIP3 w ∧ PI3K v ∧ PlasmaMembrane u ∧ Of x y ∧ Necessary e1 ∧ Catalyse e2 ∧ Agent e2 x ∧ Conversion e2 z w ∧ Mediate e3 ∧ Agent e3 x ∧ Recruitment e3 v u" sledgehammer
  (* From this, we can directly infer the hypothesis. *)
  then show ?thesis <ATP>
qed

end
