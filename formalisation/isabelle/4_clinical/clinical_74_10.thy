theory clinical_74_10
imports Main

begin

typedecl entity
typedecl event

consts
  P110Subunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Mediate :: "event ⇒ bool"
  Recruitment :: "event ⇒ bool"
  ResultIn :: "event ⇒ bool"
  NecessaryStep :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  SignalingPathway :: "entity ⇒ bool"
  PleckstrinHomologyDomain :: "entity ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "event ⇒ entity ⇒ bool"
  Provides :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The p110 subunit of PI3K catalyses the conversion of PIP2 to PIP3, which directly mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∀x y z. P110Subunit x ∧ PI3K y ∧ PIP2 z ⟶ (∃e1 e2 e3. Catalyse e1 ∧ Conversion e2 ∧ Mediate e3 ∧ Agent e1 x ∧ Patient e1 z ∧ Agent e2 y ∧ Patient e2 z ∧ To e2 z ∧ Recruitment e3 ∧ Agent e3 y ∧ To e3 z ∧ PlasmaMembrane z)"

(* Explanation 2: The conversion of PIP2 to PIP3 directly results in the recruitment of PI3K to the plasma membrane, which is a necessary step in the signaling pathway and provides a docking site for pleckstrin homology domain-containing proteins PDK1 and AKT. *)
axiomatization where
  explanation_2: "∀x y z. Conversion x ∧ PIP2 y ∧ PIP3 z ⟶ (∃e1 e2 e3. ResultIn e1 ∧ Recruitment e2 ∧ NecessaryStep e3 ∧ Agent e1 x ∧ Patient e1 y ∧ Agent e2 y ∧ To e2 z ∧ PlasmaMembrane z ∧ SignalingPathway z ∧ Provides e3 z ∧ DockingSite z ∧ (∃a b. PleckstrinHomologyDomain a ∧ PleckstrinHomologyDomain b ∧ PDK1 a ∧ AKT b))"

(* Explanation 3: The recruitment of PI3K to the plasma membrane provides a docking site for the pleckstrin homology domain-containing proteins PDK1 and AKT. *)
axiomatization where
  explanation_3: "∀x y z. Recruitment x ∧ PI3K y ∧ PlasmaMembrane z ⟶ (∃e a b. Provides e z ∧ DockingSite z ∧ PleckstrinHomologyDomain a ∧ PleckstrinHomologyDomain b ∧ PDK1 a ∧ AKT b ∧ Agent e x ∧ To e z)"

theorem hypothesis:
  assumes asm: "Conversion e1 ∧ PIP2 x ∧ PIP3 y"
  (* Hypothesis: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT. *)
  shows "∃e1 e2 e3. Conversion e1 ∧ PIP2 x ∧ PIP3 y ∧ Mediate e2 ∧ Recruitment e2 ∧ Agent e2 y ∧ To e2 z ∧ PlasmaMembrane z ∧ Provides e3 z ∧ DockingSite z ∧ (∃a b. PleckstrinHomologyDomain a ∧ PleckstrinHomologyDomain b ∧ PDK1 a ∧ AKT b))"
proof -
  (* From the premise, we have the known information about the conversion of PIP2 to PIP3. *)
  from asm have "Conversion e1 ∧ PIP2 x ∧ PIP3 y" <ATP>
  (* There is a logical relation Implies(C, B), Implies(conversion of PIP2 to PIP3, recruitment of PI3K to the plasma membrane) *)
  (* C is from explanatory sentence 2, B is from explanatory sentence 1 and 2. *)
  (* We already have Conversion e1, so we can infer Recruitment e2. *)
  then have "Recruitment e2 ∧ Agent e2 y ∧ To e2 z ∧ PlasmaMembrane z" <ATP>
  (* There is a logical relation Implies(B, D), Implies(recruitment of PI3K to the plasma membrane, docking site for pleckstrin homology domain-containing proteins PDK1 and AKT is provided) *)
  (* B is from explanatory sentence 1 and 2, D is from explanatory sentence 2 and 3. *)
  (* We already have Recruitment e2, so we can infer Provides e3 z and DockingSite z. *)
  then have "Provides e3 z ∧ DockingSite z ∧ (∃a b. PleckstrinHomologyDomain a ∧ PleckstrinHomologyDomain b ∧ PDK1 a ∧ AKT b)" <ATP>
  (* Combine all the inferred information to satisfy the hypothesis. *)
  then show ?thesis <ATP>
qed

end
