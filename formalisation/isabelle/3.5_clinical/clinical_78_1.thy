theory clinical_78_1
imports Main


begin

typedecl entity
typedecl event

consts
  p85 :: "entity ⇒ bool"
  GrowthFactorStimulation :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Cause :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  Over :: "entity ⇒ entity ⇒ bool"
  Relieves :: "entity ⇒ event ⇒ bool"
  PI3Ks :: "entity ⇒ bool"
  Heterodimers :: "entity ⇒ bool"
  ConsistingOf :: "entity ⇒ entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ entity"
  RegulatorySubunit :: "entity ⇒ entity"
  FamilyOf :: "entity ⇒ entity"

(* Explanation 1: Upon growth factor stimulation p85 binds… relieving its inhibitory effect over p110 *)
axiomatization where
  explanation_1: "∃x y z e. p85 x ∧ GrowthFactorStimulation y ∧ Binds e ∧ Cause e y ∧ Patient e x ∧ InhibitoryEffect z ∧ Over z p110 ∧ Relieves z e"

(* Explanation 2: PI3Ks… are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y. PI3Ks x ⟶ Heterodimers y ∧ ConsistingOf y (CatalyticSubunit x) ∧ ConsistingOf y (RegulatorySubunit x)"

(* Explanation 3: Phosphoinositide 3-kinases (PI3Ks) comprise a family of lipid kinases *)
axiomatization where
  explanation_3: "∀x y. PI3Ks x ⟶ FamilyOf x y"


theorem hypothesis:
 assumes asm: "Binds e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Over z p110"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binds e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Over z p110 ∧ Agent e x ∧ Patient e y ∧ Relieves z e"
proof -
  (* From the premise, we know that p85 binds p110, which implies the inhibitory effect over p110. *)
  from asm have "Binds e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Over z p110" <ATP>
  (* There is a logical relation Implies(B, C), Implies(p85 binds p110, inhibitory effect over p110) *)
  (* We can infer the inhibitory effect over p110 from p85 binding p110. *)
  then have "Binds e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Over z p110" <ATP>
  (* The hypothesis requires the existence of an agent and a patient in the event. *)
  (* We can introduce an agent x and a patient y to satisfy the hypothesis. *)
  then have "∃e x y z. Binds e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Over z p110 ∧ Agent e x ∧ Patient e y ∧ Relieves z e" <ATP>
  then show ?thesis <ATP>
qed

end
