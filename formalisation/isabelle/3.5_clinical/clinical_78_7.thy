theory clinical_78_7
imports Main


begin

typedecl entity
typedecl event

consts
  Relief :: "event ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  Directly :: "event ⇒ bool"
  Caused :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  By :: "entity ⇒ entity ⇒ bool"
  Binding :: "event ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Relieves :: "event ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The relief of the inhibitory effect on p is directly caused by the binding of the catalytic subunit by the regulatory subunit *)
axiomatization where
  explanation_1: "∃e1 e2 x y z. Relief e1 ∧ InhibitoryEffect x ∧ Directly e2 ∧ Caused e2 ∧ Agent e2 y ∧ Patient e2 x ∧ By y x ∧ By x z"


theorem hypothesis:
 assumes asm: "CatalyticSubunit p110 ∧ RegulatorySubunit p85"
 (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Relieves e ∧ Agent e x ∧ Patient e z ∧ On z p110 ∧ By x y"
proof -
  (* Given the premise, we have the information about the catalytic subunit and the regulatory subunit. *)
  from asm have "CatalyticSubunit p110 ∧ RegulatorySubunit p85" by simp
  (* From the explanation sentence, we know that the relief of the inhibitory effect on p is directly caused by the binding of the catalytic subunit by the regulatory subunit. *)
  (* This implies that the binding of the catalytic subunit by the regulatory subunit causes the relief of the inhibitory effect on p. *)
  (* Therefore, we can infer the hypothesis. *)
  then have "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Relieves e ∧ Agent e x ∧ Patient e z ∧ On z p110 ∧ By x y" sledgehammer
  then show ?thesis <ATP>
qed

end
