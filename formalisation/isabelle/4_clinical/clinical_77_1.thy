theory clinical_77_1
imports Main

begin

typedecl entity
typedecl event

consts
  GrowthFactorStimulation :: "entity ⇒ bool"
  P85 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Recruitment :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Upon :: "event ⇒ entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  InhibitoryEffect :: "event ⇒ bool"
  Relieves :: "event ⇒ event ⇒ bool"
  Subunit :: "entity ⇒ bool"
  Inhibition :: "event ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation p85 binds… and mediating the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2. GrowthFactorStimulation x ∧ P85 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 y ∧ Recruitment e2 ∧ Patient e2 z ∧ Mediates e1 e2 ∧ To z w ∧ PlasmaMembrane w ∧ Upon e1 x"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. CatalyticSubunit x ∧ P110 x ∧ PI3K y ∧ RegulatorySubunit z ∧ P85 z ∧ Binding e1 ∧ Agent e1 z ∧ Patient e1 x ∧ InhibitoryEffect e2 ∧ Patient e2 x ∧ Relieves e1 e2"

theorem hypothesis:
  assumes asm: "Subunit x ∧ P85 x ∧ P110 y ∧ PI3K z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  shows "∃x y z e1 e2 w. Subunit x ∧ P85 x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Inhibition e2 ∧ Patient e2 y ∧ Relieves e1 e2 ∧ Recruitment e2 ∧ Patient e2 z ∧ Mediates e1 e2 ∧ To z w ∧ PlasmaMembrane w"
proof -
  (* From the premise, we have known information about the subunit, P85, P110, and PI3K. *)
  from asm have "Subunit x ∧ P85 x ∧ P110 y ∧ PI3K z" by meson
  (* Explanation 1 provides a scenario where p85 binds and mediates the recruitment of PI3K to the plasma membrane. *)
  (* Explanation 2 provides a scenario where the binding of p85 to p110 relieves the inhibitory effect on p110. *)
  (* We need to show that these two scenarios can be combined to satisfy the hypothesis. *)
  (* From Explanation 2, we can infer that binding of p85 to p110 relieves inhibition on p110. *)
  from explanation_2 obtain e1 e2 where "Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ InhibitoryEffect e2 ∧ Patient e2 y ∧ Relieves e1 e2" sledgehammer
  (* From Explanation 1, we can infer that p85 binding mediates the recruitment of PI3K to the plasma membrane. *)
  from explanation_1 obtain e3 w where "Recruitment e3 ∧ Patient e3 z ∧ Mediates e1 e3 ∧ To z w ∧ PlasmaMembrane w" <ATP>
  (* Combine the results from both explanations to satisfy the hypothesis. *)
  then have "∃x y z e1 e2 w. Subunit x ∧ P85 x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Inhibition e2 ∧ Patient e2 y ∧ Relieves e1 e2 ∧ Recruitment e3 ∧ Patient e3 z ∧ Mediates e1 e3 ∧ To z w ∧ PlasmaMembrane w" <ATP>
  then show ?thesis <ATP>
qed

end
