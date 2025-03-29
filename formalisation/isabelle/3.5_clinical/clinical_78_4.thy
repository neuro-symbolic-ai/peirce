theory clinical_78_4
imports Main


begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  p :: "entity ⇒ bool"
  Leads :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The binding of the catalytic subunit (p110) by the regulatory subunit (p85) directly leads to the relief of the inhibitory effect on p *)
axiomatization where
  explanation_1: "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ PI3K x ∧ RegulatorySubunit y ∧ p z ∧ Leads e ∧ Agent e y ∧ Patient e z ∧ On z x"


theorem hypothesis:
 assumes asm: "CatalyticSubunit x ∧ RegulatorySubunit y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ PI3K x ∧ RegulatorySubunit y ∧ p z ∧ Relieves e ∧ Agent e y ∧ Patient e z ∧ On z x"
proof -
  (* From the premise, we have the information about the catalytic subunit and the regulatory subunit. *)
  from asm have "CatalyticSubunit x ∧ RegulatorySubunit y" by simp
  (* The explanation sentence states that the binding of the catalytic subunit by the regulatory subunit leads to the relief of the inhibitory effect on p. *)
  (* This implies Implies(A, B), where A is the binding of the catalytic subunit by the regulatory subunit and B is the relief of the inhibitory effect on p. *)
  (* We can use the information about the catalytic subunit and the regulatory subunit to infer the binding event. *)
  obtain e z where "Binding e ∧ CatalyticSubunit x ∧ PI3K x ∧ RegulatorySubunit y ∧ p z ∧ Leads e ∧ Agent e y ∧ Patient e z ∧ On z x" sledgehammer
  then show ?thesis <ATP>
qed

end
