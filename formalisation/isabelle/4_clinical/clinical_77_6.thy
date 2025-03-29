theory clinical_77_6
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
  Recruitment :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Upon :: "event ⇒ entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Relieves :: "event ⇒ bool"
  InhibitoryEffect :: "event ⇒ entity ⇒ bool"
  Facilitates :: "event ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  Inhibition :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation, p85 binds and mediates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. GrowthFactorStimulation x ∧ P85 y ∧ PI3K z ∧ Binds e1 ∧ Agent e1 y ∧ Mediates e2 ∧ Recruitment e2 z ∧ (∃w. To z w ∧ PlasmaMembrane w) ∧ Upon e1 x"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 and facilitates the recruitment of PI3K to the plasma membrane. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. CatalyticSubunit x ∧ P110 y ∧ PI3K z ∧ RegulatorySubunit w ∧ Binding e1 ∧ Agent e1 w ∧ Patient e1 x ∧ Relieves e2 ∧ InhibitoryEffect e2 y ∧ Facilitates e2 ∧ Recruitment e2 z ∧ (∃v. To z v ∧ PlasmaMembrane v)"

theorem hypothesis:
  assumes asm: "P85Subunit x ∧ P110 y ∧ PI3K z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  shows "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ Inhibition e2 y ∧ Mediates e2 ∧ Recruitment e2 z ∧ (∃w. To z w ∧ PlasmaMembrane w)"
proof -
  (* From the known information, we have P85Subunit x, P110 y, and PI3K z. *)
  from asm have "P85Subunit x ∧ P110 y ∧ PI3K z" by blast
  
  (* Explanation 2 provides a scenario where the binding of the catalytic subunit (p110) by the regulatory subunit (p85) relieves the inhibitory effect on p110 and facilitates the recruitment of PI3K to the plasma membrane. *)
  (* We can use the logical relation Implies(D, And(E, C)) which states that if p110 is bound by p85, then the inhibitory effect on p110 is relieved and PI3K is recruited to the plasma membrane. *)
  (* Since we have P110 y and PI3K z, we can infer the binding event and the subsequent effects. *)
  then have "∃e1 e2. Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ InhibitoryEffect e2 y ∧ Facilitates e2 ∧ Recruitment e2 z ∧ (∃w. To z w ∧ PlasmaMembrane w)" sledgehammer
  
  (* The hypothesis requires us to show that the binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  (* We have already established the binding and recruitment from the explanation and logical relations. *)
  then have "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Relieves e2 ∧ Inhibition e2 y ∧ Mediates e2 ∧ Recruitment e2 z ∧ (∃w. To z w ∧ PlasmaMembrane w)" <ATP>
  
  then show ?thesis <ATP>
qed

end
