theory clinical_78_3
imports Main


begin

typedecl entity
typedecl event

consts
  p85 :: "entity ⇒ bool"
  GrowthFactorStimulation :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Cause :: "entity ⇒ event ⇒ bool"
  PI3Ks :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Heterodimers :: "entity ⇒ bool"
  ConsistingOf :: "entity ⇒ entity ⇒ entity ⇒ bool"
  Family :: "entity ⇒ bool"
  LipidKinases :: "entity ⇒ bool"
  Comprise :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation p85 binds… relieving its inhibitory effect over p110 *)
axiomatization where
  explanation_1: "∃e x y. p85 x ∧ GrowthFactorStimulation y ∧ Binds e ∧ Agent e x ∧ Cause y e"

(* Explanation 2: PI3Ks… are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y z. PI3Ks x ∧ CatalyticSubunit y ∧ RegulatorySubunit z ∧ Heterodimers x ∧ ConsistingOf x y z"

(* Explanation 3: Phosphoinositide 3-kinases (PI3Ks) comprise a family of lipid kinases *)
axiomatization where
  explanation_3: "∀x y. PI3Ks x ∧ Family y ∧ LipidKinases y ∧ Comprise x y"


theorem hypothesis:
 assumes asm: "CatalyticSubunit x ∧ RegulatorySubunit y ∧ PI3K z"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ PI3K z ∧ Agent e y ∧ Patient e x ∧ Relieves e z"
proof -
  (* From the premise, we know that the catalytic subunit, regulatory subunit, and PI3K are involved. *)
  from asm have "CatalyticSubunit x" and "RegulatorySubunit y" and "PI3K z" apply simp
  (* There is a logical relation Implies(D, F), Implies(PI3Ks, consisting of a catalytic subunit) *)
  (* We can infer that PI3K z consists of a catalytic subunit. *)
  then have "ConsistingOf z x y" apply (simp add: assms)
  (* There is a logical relation Implies(D, G), Implies(PI3Ks, consisting of a regulatory subunit) *)
  (* We can infer that PI3K z consists of a regulatory subunit. *)
  then have "ConsistingOf z y x" by (simp add: assms)
  (* From the explanatory sentence 1, we know that p85 binds upon growth factor stimulation, relieving its inhibitory effect over p110. *)
  (* This implies that the binding event relieves the inhibitory effect on p110. *)
  then have "Relieves e z" sledgehammer
  (* We have the necessary components for the hypothesis. *)
  then show ?thesis <ATP>
qed

end
