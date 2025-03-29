theory clinical_74_9
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
  Result :: "event ⇒ bool"
  NecessaryStep :: "event ⇒ bool"
  DockingSite :: "event ⇒ bool"
  SignalingPathway :: "entity ⇒ bool"
  PleckstrinHomologyDomain :: "entity ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "event ⇒ entity ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The p110 subunit of PI3K catalyses the conversion of PIP2 to PIP3, which directly mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∀x y z. P110Subunit x ∧ PI3K y ∧ PIP2 z ⟶ (∃e1 e2 e3. Catalyse e1 ∧ Conversion e2 ∧ Mediate e3 ∧ Agent e1 x ∧ Patient e1 z ∧ Agent e2 y ∧ To e2 z ∧ Recruitment e3 ∧ Agent e3 y ∧ To e3 PlasmaMembrane)"

(* Explanation 2: The conversion of PIP2 to PIP3 directly results in the recruitment of PI3K to the plasma membrane, which is a necessary step in the signaling pathway and provides a docking site for pleckstrin homology domain-containing proteins PDK1 and AKT. *)
axiomatization where
  explanation_2: "∀x y z e1 e2 e3. Conversion e1 ∧ PIP2 y ∧ PIP3 z ⟶ (Result e1 ∧ Recruitment e2 ∧ NecessaryStep e3 ∧ Agent e1 x ∧ Patient e1 y ∧ Agent e2 y ∧ To e2 PlasmaMembrane ∧ For e3 SignalingPathway ∧ DockingSite e3 ∧ For e3 PleckstrinHomologyDomain ∧ For e3 PDK1 ∧ For e3 AKT)"

(* Explanation 3: The recruitment of PI3K to the plasma membrane provides a docking site for the pleckstrin homology domain-containing proteins PDK1 and AKT. *)
axiomatization where
  explanation_3: "∀x e. Recruitment x ∧ PI3K y ∧ PlasmaMembrane z ⟶ (DockingSite e ∧ For e PleckstrinHomologyDomain ∧ For e PDK1 ∧ For e AKT)"

theorem hypothesis:
  assumes asm: "Conversion e ∧ PIP2 x ∧ PIP3 y"
  (* Hypothesis: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT. *)
  shows "∃e1 e2 e3. Conversion e1 ∧ PIP2 x ∧ PIP3 y ∧ Mediate e2 ∧ Recruitment e2 ∧ Agent e2 y ∧ To e2 PlasmaMembrane ∧ DockingSite e3 ∧ For e3 PDK1 ∧ For e3 AKT"
proof -
  (* From the premise, we have the known information about the conversion of PIP2 to PIP3. *)
  from asm have "Conversion e ∧ PIP2 x ∧ PIP3 y" <ATP>
  (* There is a logical relation Implies(C, B), Implies(conversion of PIP2 to PIP3, recruitment of PI3K to the plasma membrane) *)
  (* C is from explanatory sentence 2, B is from explanatory sentence 1 and 2. *)
  (* We already have Conversion e, so we can infer Recruitment e2. *)
  then have "Recruitment e2 ∧ Agent e2 y ∧ To e2 PlasmaMembrane" <ATP>
  (* There is a logical relation Implies(B, D), Implies(recruitment of PI3K to the plasma membrane, docking site for pleckstrin homology domain-containing proteins PDK1 and AKT is provided) *)
  (* B is from explanatory sentence 1 and 2, D is from explanatory sentence 2 and 3. *)
  (* We already have Recruitment e2, so we can infer DockingSite e3. *)
  then have "DockingSite e3 ∧ For e3 PDK1 ∧ For e3 AKT" <ATP>
  (* Combine all the inferred information to satisfy the hypothesis. *)
  then show ?thesis <ATP>
qed

end
