theory clinical_77_0
imports Main

begin

typedecl entity
typedecl event

consts
  GrowthFactorStimulation :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Upon :: "event ⇒ entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Relieves :: "event ⇒ bool"
  InhibitoryEffect :: "event ⇒ bool"
  On :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation p85 binds… and mediating the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2. GrowthFactorStimulation x ∧ P85 y ∧ PI3K z ∧ PlasmaMembrane w ∧ Bind e1 ∧ Agent e1 y ∧ Mediates e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z w ∧ Upon e1 x"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ P85 z ∧ P110 x ∧ Binding e1 ∧ Agent e1 z ∧ Patient e1 x ∧ Relieves e2 ∧ Agent e2 z ∧ InhibitoryEffect e2 ∧ On e2 x"

theorem hypothesis:
  assumes asm: "P85Subunit x ∧ P110 y ∧ PI3K z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  shows "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Mediates e2 ∧ Patient e2 z ∧ To z PlasmaMembrane"
  sledgehammer
  oops

end
