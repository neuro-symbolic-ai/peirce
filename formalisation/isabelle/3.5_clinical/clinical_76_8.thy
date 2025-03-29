theory clinical_76_8
imports Main


begin

typedecl entity
typedecl event

consts
  P110SubunitCatalysis :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Result :: "event ⇒ entity ⇒ bool"
  PI3KRecruitment :: "event ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"

(* Explanation 1: The catalysis of the p110 subunit directly results in the conversion of PIP2 to PIP *)
axiomatization where
  explanation_1: "∃x y z e. P110SubunitCatalysis x ∧ PIP2 y ∧ PIP3 z ∧ Conversion e ∧ Agent e x ∧ Patient e y ∧ Result e z"

theorem hypothesis:
 assumes asm: "P110SubunitCatalysis x ∧ PIP2 y"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
 shows "∃x y z e1 e2. P110SubunitOfPIK3 x ∧ PIP2 y ∧ PIP3 z ∧ Conversion e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Result e1 z ∧ PI3KRecruitment e2 ∧ Agent e2 x ∧ Patient e2 PlasmaMembrane"
  sledgehammer
  oops

end
