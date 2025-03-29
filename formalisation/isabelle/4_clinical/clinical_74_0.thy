theory clinical_74_0
imports Main

begin

typedecl entity
typedecl event

consts
  Subunit :: "entity ⇒ bool"
  PIK3 :: "entity ⇒ bool"
  Conversion :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyses :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Convert :: "event ⇒ bool"
  Result :: "event ⇒ entity ⇒ bool"
  Recruitment :: "event ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  DockingSite :: "entity ⇒ bool"
  Proteins :: "entity ⇒ bool"
  PDK1 :: "entity ⇒ bool"
  AKT :: "entity ⇒ bool"
  Provides :: "event ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z w v e1 e2. Subunit x ∧ PIK3 y ∧ Conversion z ∧ PIP2 w ∧ PIP3 v ∧ Catalyses e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Convert e1 ∧ Agent e1 z ∧ Patient e1 w ∧ Result e1 v ∧ Recruitment e2 ∧ PI3K x ∧ PlasmaMembrane y ∧ Mediates e2 ∧ Agent e2 x ∧ Patient e2 y"

(* Explanation 2: PIP2 to PIP3… subsequently provides a docking site for the pleckstrin homology domain-containing proteins PDK1 and AKT. *)
axiomatization where
  explanation_2: "∃x y z w v u e. PIP2 x ∧ PIP3 y ∧ DockingSite z ∧ Proteins w ∧ PDK1 v ∧ AKT u ∧ Provides e ∧ Agent e x ∧ Patient e z ∧ Contains w v ∧ Contains w u"

theorem hypothesis:
  assumes asm: "Conversion x ∧ PIP2 y ∧ PIP3 z"
  (* Hypothesis: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT. *)
  shows "∃x y z e1 e2 e3. Conversion x ∧ PIP2 y ∧ PIP3 z ∧ Convert e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Result e1 z ∧ Recruitment e2 ∧ PI3K x ∧ PlasmaMembrane y ∧ Mediates e2 ∧ Agent e2 x ∧ Patient e2 y ∧ DockingSite e3 ∧ PDK1 x ∧ AKT y ∧ Provides e3 ∧ Agent e3 x ∧ Patient e3 y"
  sledgehammer
  oops

end
