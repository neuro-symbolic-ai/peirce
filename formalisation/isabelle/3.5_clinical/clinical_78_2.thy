theory clinical_78_2
imports Main


begin

typedecl entity
typedecl event

consts
  GrowthFactorStimulation :: "entity ⇒ bool"
  p85 :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Target :: "event ⇒ entity ⇒ bool"
  Over :: "entity ⇒ entity ⇒ bool"
  p110 :: "entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation p85 binds… relieving its inhibitory effect over p110 *)
axiomatization where
  explanation_1: "∃e x y z. GrowthFactorStimulation x ∧ p85 y ∧ Binds e ∧ InhibitoryEffect z ∧ Agent e y ∧ Target e z ∧ Over z p110"

consts
  PI3Ks :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Heterodimers :: "entity ⇒ bool"
  ConsistingOf :: "entity ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 2: PI3Ks… are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y z. PI3Ks x ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ Heterodimers z ∧ ConsistingOf z p110 p85"

consts
  Family :: "entity ⇒ bool"
  LipidKinases :: "entity ⇒ bool"
  Comprise :: "entity ⇒ entity ⇒ bool"

(* Explanation 3: Phosphoinositide 3-kinases (PI3Ks) comprise a family of lipid kinases *)
axiomatization where
  explanation_3: "∀x y. PI3Ks x ∧ Family y ∧ LipidKinases y ∧ Comprise x y"


theorem hypothesis:
 assumes asm: "GrowthFactorStimulation x ∧ p85 y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binds e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Agent e y ∧ Target e z"
proof -
  (* From the premise, we know about growth factor stimulation and p85 binding. *)
  from asm have "GrowthFactorStimulation x ∧ p85 y" <ATP>
  (* There is a logical relation Implies(A, B), Implies(growth factor stimulation, p85 binds) *)
  (* A is from explanatory sentence 1, B is from explanatory sentence 1. *)
  (* We can infer p85 binds. *)
  then have "p85 y" <ATP>
  (* There is a logical relation Implies(B, C), Implies(p85 binds, inhibitory effect over p110) *)
  (* We can infer inhibitory effect over p110. *)
  then have "InhibitoryEffect p110" <ATP>
  (* There is a logical relation Implies(B, G), Implies(p85 binds, consisting of a regulatory subunit) *)
  (* We can infer consisting of a regulatory subunit. *)
  then obtain z where "RegulatorySubunit y ∧ Heterodimers z ∧ ConsistingOf z p110 p85" <ATP>
  then have "RegulatorySubunit y" and "Heterodimers z" and "ConsistingOf z p110 p85" <ATP>
  (* There is a logical relation Implies(E, F), Implies(heterodimers, consisting of a catalytic subunit) *)
  (* We can infer consisting of a catalytic subunit. *)
  then obtain e where "CatalyticSubunit e ∧ ConsistingOf z p110 e" <ATP>
  then have "CatalyticSubunit e" and "ConsistingOf z p110 e" <ATP>
  (* We have obtained the necessary information to prove the hypothesis. *)
  then show ?thesis <ATP>
qed

end
