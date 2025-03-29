theory clinical_76_9
imports Main

begin

typedecl entity
typedecl event

consts
  Binding :: "entity ⇒ bool"
  Subunit :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  Necessary :: "entity ⇒ bool"
  Relieve :: "event ⇒ bool"
  Inhibition :: "entity ⇒ bool"
  Allows :: "event ⇒ bool"
  Activation :: "entity ⇒ bool"
  Catalysis :: "event ⇒ bool"
  Conversion :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Leads :: "event ⇒ bool"
  To :: "event ⇒ event ⇒ bool"
  Mediation :: "event ⇒ bool"
  Recruitment :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Ensures :: "event ⇒ bool"
  Occur :: "event ⇒ bool"
  Simultaneously :: "event ⇒ bool"
  Catalyses :: "event ⇒ bool"
  Mediates :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The binding of the p85 subunit to the p110 subunit is necessary to relieve the inhibition of p110, which allows the activation of the p110 subunit. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. Binding x ∧ Subunit y ∧ P85 y ∧ P110 z ∧ Necessary x ∧ Relieve e1 ∧ Inhibition z ∧ Allows e2 ∧ Activation z"

(* Explanation 2: The activation of the p110 subunit directly leads to the catalysis of the conversion of phosphatidylinositol-4,5-bisphosphate (PIP2) to phosphatidylinositol-4,5-trisphosphate (PIP3). *)
axiomatization where
  explanation_2: "∃x y z e1 e2. Activation x ∧ Subunit y ∧ P110 y ∧ Catalysis e1 ∧ Conversion z ∧ PIP2 z ∧ PIP3 z ∧ Leads e2 ∧ To e2 e1"

(* Explanation 3: The activation of the p110 subunit directly leads to the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. Activation x ∧ Subunit y ∧ P110 y ∧ Mediation e1 ∧ Recruitment z ∧ PI3K z ∧ PlasmaMembrane z ∧ Leads e2 ∧ To e2 e1"

(* Explanation 4: The binding of the p85 subunit to the p110 subunit is necessary for the activation of the p110 subunit, which directly leads to both the catalysis of the conversion of PIP2 to PIP3 and the mediation of the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_4: "∃x y z w e1 e2 e3. Binding x ∧ Subunit y ∧ P85 y ∧ P110 z ∧ Activation w ∧ Necessary x ∧ Catalysis e1 ∧ Conversion z ∧ PIP2 z ∧ PIP3 z ∧ Mediation e3 ∧ Recruitment w ∧ PI3K w ∧ PlasmaMembrane w ∧ Leads e3 ∧ To e3 e1 ∧ To e3 e2"

(* Explanation 5: Additionally, the activation of the p110 subunit ensures that both processes occur simultaneously. *)
axiomatization where
  explanation_5: "∃x y e1 e2. Activation x ∧ Subunit y ∧ P110 y ∧ Ensures e1 ∧ Occur e2 ∧ Simultaneously e2"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PI3K y ∧ Conversion z ∧ PIP2 z ∧ PIP3 z ∧ PI3K y ∧ PlasmaMembrane y"
  (* Hypothesis: The p110 subunit of PI3K catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane. *)
  shows "∃x y z e1 e2. Subunit x ∧ PI3K y ∧ Conversion z ∧ PIP2 z ∧ PIP3 z ∧ PI3K y ∧ PlasmaMembrane y ∧ Catalyses e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Mediates e2 ∧ Agent e2 x ∧ Recruitment y ∧ To y PlasmaMembrane"
  sledgehammer
  oops

end
