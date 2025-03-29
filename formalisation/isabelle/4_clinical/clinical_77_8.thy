theory clinical_77_8
imports Main

begin

typedecl entity
typedecl event

consts
  GrowthFactorStimulation :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Upon :: "event ⇒ entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Relieves :: "event ⇒ bool"
  Facilitates :: "event ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  P110Subunit :: "entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation, p85 binds and mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. GrowthFactorStimulation x ∧ P85 y ∧ PI3K z ∧ Binds e1 ∧ Agent e1 y ∧ Mediates e2 ∧ Patient e2 z ∧ To z PlasmaMembrane ∧ Upon e1 x"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 and facilitates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. CatalyticSubunit x ∧ P110 y ∧ PI3K z ∧ RegulatorySubunit w ∧ Binding e1 ∧ Agent e1 w ∧ Patient e1 x ∧ Relieves e2 ∧ Patient e2 y ∧ Facilitates e2 ∧ Patient e2 z ∧ To z PlasmaMembrane"

(* Explanation 3: The binding of both the p85 subunit and the p110 subunit together mediates the recruitment of PI3K to the plasma membrane and relieves the inhibitory effect on p. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. P85Subunit x ∧ P110Subunit y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Mediates e2 ∧ Patient e2 z ∧ Relieves e2 ∧ Patient e2 y ∧ To z PlasmaMembrane"

theorem hypothesis:
  assumes asm: "P85Subunit x ∧ P110 y ∧ PI3K z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  shows "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ Patient e2 y ∧ Mediates e2 ∧ Patient e2 z ∧ To z PlasmaMembrane"
proof -
  (* From the assumption, we have known information about P85Subunit, P110, and PI3K. *)
  from asm have "P85Subunit x ∧ P110 y ∧ PI3K z" <ATP>
  (* Explanation 3 states that the binding of both the p85 subunit and the p110 subunit together mediates the recruitment of PI3K to the plasma membrane and relieves the inhibitory effect on p. *)
  (* This directly corresponds to the hypothesis we want to prove. *)
  (* We can use the logical relation Implies(F, And(C, G)) from explanation 3. *)
  (* Since we have P85Subunit x and P110 y, we can infer the binding event and the effects. *)
  then have "Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Mediates e2 ∧ Patient e2 z ∧ Relieves e2 ∧ Patient e2 y ∧ To z PlasmaMembrane" <ATP>
  then show ?thesis <ATP>
qed

end
