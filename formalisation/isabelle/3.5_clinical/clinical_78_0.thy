theory clinical_78_0
imports Main


begin

typedecl entity
typedecl event

consts
  p85 :: "entity ⇒ bool"
  GrowthFactorStimulation :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Relieves :: "event ⇒ bool"
  InhibitoryEffect :: "event ⇒ bool"
  Over :: "event ⇒ entity ⇒ bool"
  p110 :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Heterodimers :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  ConsistingOf :: "entity ⇒ entity ⇒ bool"
  Phosphoinositide3Kinases :: "entity ⇒ bool"
  Family :: "entity ⇒ bool"
  LipidKinases :: "entity ⇒ bool"
  Comprise :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation p85 binds… relieving its inhibitory effect over p110 *)
axiomatization where
  explanation_1: "∃x y e. p85 x ∧ GrowthFactorStimulation y ∧ Binds e ∧ Agent e x ∧ Patient e p110 ∧ Relieves e ∧ InhibitoryEffect e ∧ Over e p110"

(* Explanation 2: PI3Ks… are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ∧ Heterodimers y ∧ CatalyticSubunit z ∧ RegulatorySubunit z ∧ ConsistingOf y z"

(* Explanation 3: Phosphoinositide 3-kinases (PI3Ks) comprise a family of lipid kinases *)
axiomatization where
  explanation_3: "∀x y. Phosphoinositide3Kinases x ∧ Family y ∧ LipidKinases y ∧ Comprise x y"


theorem hypothesis:
 assumes asm: "PI3K x ∧ CatalyticSubunit y ∧ RegulatorySubunit z"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃x y z e. PI3K x ∧ CatalyticSubunit y ∧ RegulatorySubunit z ∧ Binds e ∧ Agent e z ∧ Patient e y ∧ Relieves e ∧ InhibitoryEffect e ∧ Over e y"
proof -
  (* From the premise, we have the information about PI3K, CatalyticSubunit, and RegulatorySubunit. *)
  from asm have "PI3K x ∧ CatalyticSubunit y ∧ RegulatorySubunit z" <ATP>
  (* There are logical relations and derived implications that can help us infer the hypothesis. *)
  (* There is a logical relation Implies(D, F), Implies(PI3Ks, consisting of a catalytic subunit) *)
  (* We already have CatalyticSubunit y, so we can infer consisting of a catalytic subunit. *)
  then have "PI3K x ∧ consisting of a catalytic subunit y" <ATP>
  (* There is a logical relation Implies(D, G), Implies(PI3Ks, consisting of a regulatory subunit) *)
  (* We already have RegulatorySubunit z, so we can infer consisting of a regulatory subunit. *)
  then have "PI3K x ∧ consisting of a regulatory subunit z" <ATP>
  (* There is a logical relation Implies(B, C), Implies(p85 binds, inhibitory effect over p110) *)
  (* There is a logical relation Implies(A, B), Implies(growth factor stimulation, p85 binds) *)
  (* We can combine these to infer the inhibitory effect over p110. *)
  then have "PI3K x ∧ consisting of a catalytic subunit y ∧ consisting of a regulatory subunit z ∧ Binds e ∧ Agent e z ∧ Patient e y ∧ Relieves e ∧ InhibitoryEffect e ∧ Over e y" <ATP>
  then show ?thesis <ATP>
qed

end
