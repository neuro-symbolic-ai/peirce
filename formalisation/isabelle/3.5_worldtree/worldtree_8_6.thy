theory worldtree_8_6
imports Main


begin

typedecl entity
typedecl event

consts
  Recording :: "entity ⇒ bool"
  Observations :: "entity ⇒ bool"
  Data :: "entity ⇒ bool"
  Journal :: "entity ⇒ bool"
  CommonPractice :: "event ⇒ bool"
  In :: "entity ⇒ event ⇒ bool"
  Communicating :: "event ⇒ bool"
  ResultsOfInvestigation :: "event ⇒ bool"
  Alan :: "entity ⇒ bool"
  CabbageJuice :: "entity ⇒ bool"
  pH :: "entity ⇒ bool"
  HouseholdSolutions :: "entity ⇒ bool"
  Using :: "event ⇒ bool"
  Determine :: "event ⇒ bool"

(* Explanation 1: Recording observations and data in a journal is a common practice in communicating the results of an investigation. *)
axiomatization where
  explanation_1: "∀x y e. Recording x ∧ Observations y ∧ Data y ∧ Journal y ⟶ CommonPractice e ∧ In x e ∧ Communicating e ∧ ResultsOfInvestigation e"


theorem hypothesis:
  (* Premise 1: Alan is using cabbage juice to determine the relative pH of various household solutions. *)
  assumes asm: "Alan x ∧ CabbageJuice y ∧ pH z ∧ HouseholdSolutions z ∧ Using e ∧ Agent e x ∧ Patient e y ∧ Determine e ∧ In x e"
  (* Hypothesis: Recording observations and data in a journal communicates the results of an investigation. *)
  shows "∃x y e. Recording x ∧ Observations y ∧ Data y ∧ Journal y ∧ Communicating e ∧ Agent e x ∧ Patient e ResultsOfInvestigation"
  sledgehammer
  oops

end
