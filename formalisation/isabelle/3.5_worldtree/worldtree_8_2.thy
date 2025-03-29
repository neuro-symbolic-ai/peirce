theory worldtree_8_2
imports Main


begin

typedecl entity
typedecl event

consts
  Investigation :: "entity ⇒ bool"
  Experimentation :: "event ⇒ bool"
  Requires :: "event ⇒ entity ⇒ bool"
  Observations :: "entity ⇒ bool"
  Data :: "entity ⇒ bool"
  Experiment :: "entity ⇒ bool"
  PartOf :: "entity ⇒ entity ⇒ bool"
  ResultsOf :: "entity ⇒ entity"
  Journal :: "entity ⇒ bool"
  Recording :: "event ⇒ bool"
  Communicates :: "entity ⇒ entity ⇒ bool"
  Alan :: "entity ⇒ bool"
  CabbageJuice :: "entity ⇒ bool"
  HouseholdSolutions :: "entity ⇒ bool"
  Using :: "event ⇒ bool"
  PurposeOf :: "event ⇒ entity ⇒ bool"
  DetermineRelativePH :: "entity ⇒ bool"

(* Explanation 1: Investigation sometimes requires experimentation. *)
axiomatization where
  explanation_1: "∃x e. Investigation x ∧ Experimentation e ∧ Requires e x"

(* Explanation 2: Observations; data are a part of the results of an experiment. *)
axiomatization where
  explanation_2: "∀x y z. Observations x ∧ Data y ∧ Experiment z ⟶ (PartOf x (ResultsOf z) ∧ PartOf y (ResultsOf z))"


theorem hypothesis:
  (* Premise: Alan is using cabbage juice to determine the relative pH of various household solutions. *)
  assumes asm: "Alan x ∧ CabbageJuice y ∧ HouseholdSolutions z ∧ Using e ∧ Agent e x ∧ Patient e y ∧ PurposeOf e z"
  (* Hypothesis: Recording observations and data in a journal communicates the results of an investigation. *)
  shows "∃x y z e. Journal x ∧ Observations y ∧ Data z ∧ Recording e ∧ Agent e x ∧ Patient e y ∧ Patient e z ∧ Communicates (ResultsOf e) (Investigation)"
  sledgehammer
  oops

end
