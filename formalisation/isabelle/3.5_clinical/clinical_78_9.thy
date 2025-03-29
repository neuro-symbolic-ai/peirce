theory clinical_78_9
imports Main


begin

typedecl entity
typedecl event

consts
  Relief :: "entity ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  CausedBy :: "event ⇒ bool"
  Directly :: "event ⇒ bool"
  Binding :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Implies :: "event ⇒ bool"
  LeadsTo :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The relief of the inhibitory effect on p is directly caused by the binding event of the catalytic subunit by the regulatory subunit *)
axiomatization where
  explanation_1: "∃x y z e. Relief x ∧ InhibitoryEffect y ∧ On y p ∧ CausedBy e ∧ Directly e ∧ Binding z ∧ CatalyticSubunit z ∧ RegulatorySubunit x ∧ Agent e z ∧ Patient e x"

(* Explanation 2: The relief of the inhibitory effect on p is directly caused by the binding event of the catalytic subunit by the regulatory subunit implies that the binding event leads to the relief of the inhibitory effect on p *)
axiomatization where
  explanation_2: "∃x y z e1 e2. Relief x ∧ InhibitoryEffect y ∧ On y p ∧ CausedBy e1 ∧ Directly e1 ∧ Binding z ∧ CatalyticSubunit z ∧ RegulatorySubunit x ∧ Agent e1 z ∧ Patient e1 x ∧ Implies e2 ∧ LeadsTo e2 ∧ Agent e2 z ∧ Patient e2 x"


theorem hypothesis:
 assumes asm: "Binding x ∧ CatalyticSubunit y ∧ PI3K y ∧ RegulatorySubunit z ∧ InhibitoryEffect e ∧ On e y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃x y z e. Binding x ∧ CatalyticSubunit y ∧ PI3K y ∧ RegulatorySubunit z ∧ InhibitoryEffect e ∧ On e y ∧ Relief x ∧ Agent x z ∧ Patient x e"
  sledgehammer
  oops

end
