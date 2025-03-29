theory clinical_76_5
imports Main


begin

typedecl entity
typedecl event

consts
  CatalysisOfP110Subunit :: "entity ⇒ bool"
  Converts :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  ConvertsTo :: "event ⇒ entity ⇒ entity ⇒ bool"
  Directly :: "event ⇒ bool"
  P110SubunitOfPIK3 :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  PI3K :: "entity"
  PlasmaMembrane :: "entity"

(* Explanation 1: The catalysis of the p110 subunit in converting PIP2 to PIP3 directly leads to the conversion of PIP2 to PIP *)
axiomatization where
  explanation_1: "∃e x y z. CatalysisOfP110Subunit x ∧ Converts e ∧ Agent e x ∧ Patient e y ∧ ConvertsTo e y z ∧ Directly e"


theorem hypothesis:
 assumes asm: "P110SubunitOfPIK3 x ∧ PIP2 y"
  (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
 shows "∃x y z e1 e2. P110SubunitOfPIK3 x ∧ PIP2 y ∧ PIP3 z ∧ Catalyses e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Converts e1 y z ∧ Mediates e2 ∧ Agent e2 x ∧ Recruits e2 PI3K ∧ To x PlasmaMembrane"
  sledgehammer
  oops

end
