theory clinical_77_9
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
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Upon :: "event ⇒ event ⇒ bool"
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
  explanation_1: "∃x y z e1 e2. GrowthFactorStimulation e1 ∧ P85 x ∧ PI3K y ∧ PlasmaMembrane z ∧ Binds e2 ∧ Agent e2 x ∧ Mediates e2 ∧ Patient e2 y ∧ To y z ∧ Upon e2 e1"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 and facilitates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. CatalyticSubunit x ∧ P110 y ∧ PI3K z ∧ RegulatorySubunit w ∧ Binding e1 ∧ Agent e1 w ∧ Patient e1 x ∧ Relieves e2 ∧ Agent e2 w ∧ Patient e2 y ∧ Facilitates e2 ∧ Patient e2 z ∧ To z PlasmaMembrane"

(* Explanation 3: The binding of both the p85 subunit and the p110 subunit together mediates the recruitment of PI3K to the plasma membrane and relieves the inhibitory effect on p. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. P85Subunit x ∧ P110Subunit y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Mediates e2 ∧ Agent e2 x ∧ Patient e2 z ∧ To z PlasmaMembrane ∧ Relieves e2 ∧ Patient e2 y"

theorem hypothesis:
  assumes asm: "P85Subunit x ∧ P110 y ∧ PI3K z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  shows "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Mediates e2 ∧ Patient e2 z ∧ To z PlasmaMembrane"
proof -
  (* From the known information, we have P85Subunit x, P110 y, and PI3K z. *)
  from asm have "P85Subunit x ∧ P110 y ∧ PI3K z" <ATP>
  
  (* Explanation 3 states that the binding of both the p85 subunit and the p110 subunit together mediates the recruitment of PI3K to the plasma membrane and relieves the inhibitory effect on p. *)
  (* This directly corresponds to the hypothesis we want to prove. *)
  (* We can use explanation_3 to infer the hypothesis. *)
  from explanation_3 have "∃e1 e2. Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Mediates e2 ∧ Agent e2 x ∧ Patient e2 z ∧ To z PlasmaMembrane ∧ Relieves e2 ∧ Patient e2 y" <ATP>
  
  (* Combine the known information with the result from explanation_3 to conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
