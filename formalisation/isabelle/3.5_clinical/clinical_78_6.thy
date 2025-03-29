theory clinical_78_6
imports Main


begin

typedecl entity
typedecl event

consts
  Relief :: "event ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  Directly :: "event ⇒ bool"
  Cause :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  By :: "event ⇒ entity ⇒ bool"
  Binding :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"

(* Explanation 1: The relief of the inhibitory effect on p is directly caused by the binding of the catalytic subunit by the regulatory subunit *)
axiomatization where
  explanation_1: "∃e1 e2 x y z. Relief e1 ∧ InhibitoryEffect x ∧ Directly e2 ∧ Cause e2 ∧ Agent e2 y ∧ Patient e2 z ∧ By e1 Binding ∧ By e1 x ∧ By x y"


theorem hypothesis:
 assumes asm: "CatalyticSubunit x ∧ RegulatorySubunit y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Relieves e ∧ Agent e x ∧ Patient e z ∧ By e z p110 ∧ By x y"
proof -
  (* Given the known information about the catalytic subunit and regulatory subunit. *)
  from asm have "CatalyticSubunit x" ∧ "RegulatorySubunit y" <ATP>
  (* From the explanatory sentence, we know that the relief of the inhibitory effect on p is directly caused by the binding of the catalytic subunit by the regulatory subunit. *)
  (* This implies that the binding of the catalytic subunit by the regulatory subunit relieves the inhibitory effect on p. *)
  (* We can infer the existence of an event e, entities x, y, z such that the binding occurs, and the other conditions hold. *)
  then have "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Relief e ∧ Agent e x ∧ Patient e z ∧ By e z p110 ∧ By x y" <ATP>
  then show ?thesis <ATP>
qed

end
