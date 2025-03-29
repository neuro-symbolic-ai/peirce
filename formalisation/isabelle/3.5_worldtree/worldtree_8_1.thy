theory worldtree_8_1
imports Main


begin

typedecl entity
typedecl event

consts
  Investigation :: "entity ⇒ bool"
  Experimentation :: "entity ⇒ bool"
  Requires :: "entity ⇒ entity ⇒ bool"
  Observations :: "entity ⇒ bool"
  Data :: "entity ⇒ bool"
  Experiment :: "entity ⇒ bool"
  PartOf :: "entity ⇒ entity ⇒ bool"
  ResultsOf :: "entity ⇒ entity"
  Recording :: "entity ⇒ bool"
  Journal :: "entity ⇒ bool"
  Communicates :: "entity ⇒ bool"
  ResultsOfInvestigation :: "entity"
  Alan :: "entity ⇒ bool"
  CabbageJuice :: "entity ⇒ bool"
  HouseholdSolutions :: "entity ⇒ bool"
  Using :: "event ⇒ bool"
  DetermineRelativePH :: "event ⇒ bool"

(* Explanation 1: Investigation sometimes requires experimentation. *)
axiomatization where
  explanation_1: "∃x y. Investigation x ∧ Experimentation y ∧ Requires x y"

(* Explanation 2: Observations; data are a part of the results of an experiment. *)
axiomatization where
  explanation_2: "∀x y z. Observations x ∧ Data y ∧ Experiment z ⟶ (PartOf x (ResultsOf z) ∧ PartOf y (ResultsOf z))"


theorem hypothesis:
  (* Premise: Alan is using cabbage juice to determine the relative pH of various household solutions. *)
  assumes asm: "Alan x ∧ CabbageJuice y ∧ HouseholdSolutions z ∧ Using e ∧ Agent e x ∧ Patient e y ∧ DetermineRelativePH e ∧ Patient e z"
  (* Hypothesis: Recording observations and data in a journal communicates the results of an investigation. *)
  shows "∃x y z e. Recording x ∧ Observations y ∧ Data z ∧ Journal e ∧ Communicates e ∧ Agent e x ∧ Patient e ResultsOfInvestigation"
  sledgehammer
  oops

end
