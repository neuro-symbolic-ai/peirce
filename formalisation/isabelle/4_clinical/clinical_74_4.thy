theory clinical_74_4
imports Main

begin

typedecl entity
typedecl event

consts
  Subunit :: "entity ⇒ bool"
  PIK3 :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyse :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Result :: "event ⇒ entity ⇒ bool"
  Recruitment :: "event ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Essential :: "event ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"
  Location :: "event ⇒ entity ⇒ bool"
  Conversion :: "entity ⇒ bool"
  Convert :: "event ⇒ bool"
  Mediate :: "event ⇒ bool"
  Recruit :: "event ⇒ bool"
  DockingSite :: "event ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  Provide :: "event ⇒ bool"
  PI3K :: "entity ⇒ bool"

(* Explanation 1: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3, which is essential for the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2. Subunit x ∧ PIK3 y ∧ PIP2 z ∧ PIP3 w ∧ Catalyse e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Result e1 w ∧ Recruitment e2 ∧ PI3K y ∧ PlasmaMembrane z ∧ Essential e2 ∧ For e2 y ∧ Location e2 z"

(* Explanation 2: The conversion of PIP2 to PIP3 mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ Convert e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Result e1 z ∧ Recruitment e2 ∧ PI3K y ∧ PlasmaMembrane z ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Location e2 z"

(* Explanation 3: The recruitment of PI3K to the plasma membrane provides a docking site for the pleckstrin homology domain-containing proteins PDK1 and AKT. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. Recruitment e1 ∧ PI3K y ∧ PlasmaMembrane z ∧ Recruit e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Location e1 z ∧ DockingSite e2 ∧ PDK1 y ∧ AKT z ∧ Provide e2 ∧ Agent e2 x ∧ Patient e2 y ∧ For e2 z"

theorem hypothesis:
  assumes asm: "Conversion x ∧ PIP2 y ∧ PIP3 z"
  (* Hypothesis: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT. *)
  shows "∃x y z e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ Convert e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Result e1 z ∧ Recruitment e2 ∧ PI3K y ∧ PlasmaMembrane z ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Location e2 z ∧ DockingSite e3 ∧ PDK1 y ∧ AKT z ∧ Provide e3 ∧ Agent e3 x ∧ Patient e3 y ∧ For e3 z"
proof -
  (* From the premise, we have known information about the conversion of PIP2 to PIP3. *)
  from asm have "Conversion x ∧ PIP2 y ∧ PIP3 z" by fastforce
  (* There is a logical relation Implies(B, C), Implies(conversion of PIP2 to PIP3, recruitment of PI3K to the plasma membrane) *)
  (* B is from explanatory sentence 2, C is from explanatory sentence 1 and 2. *)
  (* We can infer the recruitment of PI3K to the plasma membrane. *)
  then obtain e1 e2 where "Convert e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Result e1 z ∧ Recruitment e2 ∧ PI3K y ∧ PlasmaMembrane z ∧ Mediate e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Location e2 z" sledgehammer
  (* There is a logical relation Implies(C, D), Implies(recruitment of PI3K to the plasma membrane, provides a docking site for the pleckstrin homology domain-containing proteins PDK1 and AKT) *)
  (* C is from explanatory sentence 1 and 2, D is from explanatory sentence 3. *)
  (* We can infer that it provides a docking site for PDK1 and AKT. *)
  then obtain e3 where "DockingSite e3 ∧ PDK1 y ∧ AKT z ∧ Provide e3 ∧ Agent e3 x ∧ Patient e3 y ∧ For e3 z" <ATP>
  then show ?thesis <ATP>
qed

end
