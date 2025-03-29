theory clinical_105_5
imports Main


begin

typedecl entity
typedecl event

consts
  Trastuzumab :: "entity ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  Have :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Bind :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  ActivatingMutation :: "entity ⇒ bool"
  HER2ExtracellularDomain :: "entity ⇒ entity"
  IntracellularKinaseDomain :: "entity ⇒ entity"
  HER2V777L :: "entity ⇒ bool"
  TyrosineKinaseDomain :: "entity ⇒ bool"
  LocatedIn :: "entity ⇒ entity ⇒ bool"
  ResistanceToAntibodyTherapy :: "entity ⇒ bool"
  Cause :: "event ⇒ bool"

(* Explanation 1: Because trastuzumab binds to the HER2 extracellular domain, it may have no inhibitory effect on the HER2-activating mutation in the intracellular kinase domain *)
axiomatization where
  explanation_1: "∃e1 e2 x y z. Trastuzumab x ∧ InhibitoryEffect y ∧ Have e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Bind e2 ∧ Agent e2 x ∧ Patient e2 (HER2ExtracellularDomain z) ∧ In x z ∧ ActivatingMutation y ∧ In y (IntracellularKinaseDomain z)"

(* Explanation 2: The HER2 V777L mutation is located in the tyrosine kinase domain *)
axiomatization where
  explanation_2: "∃x y. HER2V777L x ∧ TyrosineKinaseDomain y ∧ LocatedIn x y"

(* Explanation 3: HER2 V777L may cause resistance to antibody therapy *)
axiomatization where
  explanation_3: "∃e x y. HER2V777L x ∧ ResistanceToAntibodyTherapy y ∧ Cause e ∧ Agent e x ∧ Patient e y"


theorem hypothesis:
 assumes asm: "HER2V777L x"
  (* Hypothesis: HER2 V777L may cause resistance to trastuzumab, as trastuzumab binds to the extracellular kinase domain, whereas the mutation is in the intracellular kinase domain *)
 shows "∃e1 e2 x y z. HER2V777L(x) ∧ ResistanceToTrastuzumab(y) ∧ Cause(e1) ∧ Agent(e1, x) ∧ Patient(e1, y) ∧ Bind(e2) ∧ Agent(e2, y) ∧ Patient(e2, ExtracellularKinaseDomain(z)) ∧ In(x, z) ∧ In(y, IntracellularKinaseDomain(z))"
  sledgehammer
  oops

end
