theory clinical_77_1
imports Main


begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Recruitment :: "entity ⇒ entity ⇒ bool"
  PlasmaMembrane :: "entity"

(* Explanation 1: Binding of the p85 subunit to PI3K mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e x y. Binding e ∧ P85Subunit x ∧ PI3K y ∧ Mediates e ∧ Agent e x ∧ Patient e y ∧ Recruitment x PlasmaMembrane"


theorem hypothesis:
 assumes asm: "Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e x y z. Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Relieves e ∧ Agent e x ∧ Patient e y ∧ Mediates e ∧ Agent e x ∧ Patient e z ∧ Recruitment PI3K PlasmaMembrane"
  sledgehammer
  oops

end
