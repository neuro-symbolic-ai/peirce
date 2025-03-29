theory clinical_77_4
imports Main

begin

typedecl entity
typedecl event

consts
  GrowthFactorStimulation :: "event ⇒ bool"
  P85 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Recruitment :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Upon :: "event ⇒ event ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Relieves :: "event ⇒ bool"
  InhibitoryEffect :: "event ⇒ entity ⇒ bool"
  Facilitates :: "event ⇒ bool"
  Subunit :: "entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation, p85 binds and mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. GrowthFactorStimulation e1 ∧ P85 x ∧ PI3K y ∧ PlasmaMembrane z ∧ Binds e2 ∧ Agent e2 x ∧ Mediates e2 ∧ Recruitment e2 y ∧ To y z ∧ Upon e2 e1"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 and facilitates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. CatalyticSubunit x ∧ P110 x ∧ PI3K y ∧ RegulatorySubunit z ∧ P85 z ∧ PlasmaMembrane w ∧ Binding e1 ∧ Agent e1 z ∧ Patient e1 x ∧ Relieves e2 ∧ Agent e2 z ∧ InhibitoryEffect e2 x ∧ Facilitates e2 ∧ Recruitment e2 y ∧ To y w"

theorem hypothesis:
  assumes asm: "Subunit x ∧ P85 x ∧ P110 y ∧ PI3K z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  shows "∃x y z e1 e2. Subunit x ∧ P85 x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ Agent e2 e1 ∧ Patient e2 y ∧ Mediates e2 ∧ Recruitment e2 z ∧ To z PlasmaMembrane"
  sledgehammer
  oops

end
