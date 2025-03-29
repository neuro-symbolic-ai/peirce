theory worldtree_8_3
imports Main

begin

typedecl entity
typedecl event

consts
  Investigation :: "entity ⇒ bool"
  Experimentation :: "entity ⇒ bool"
  Observations :: "entity ⇒ bool"
  Data :: "entity ⇒ bool"
  Requires :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Involves :: "event ⇒ bool"
  Recording :: "event ⇒ bool"
  Results :: "entity ⇒ bool"
  Experiment :: "entity ⇒ bool"
  PartOf :: "entity ⇒ entity ⇒ bool"
  Journal :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Documenting :: "event ⇒ bool"
  Method :: "event ⇒ entity ⇒ bool"
  Communicating :: "event ⇒ bool"
  Alan :: "entity ⇒ bool"
  CabbageJuice :: "entity ⇒ bool"
  HouseholdSolutions :: "entity ⇒ bool"
  Using :: "event ⇒ bool"
  Determine :: "event ⇒ bool"
  RelativePH :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Investigation sometimes requires experimentation, and experimentation often involves recording observations and data. *)
axiomatization where
  explanation_1: "∀x y z e1 e2. Investigation x ∧ Experimentation y ∧ Observations z ∧ Data z ∧ (Requires e1 ∧ Agent e1 x ∧ Patient e1 y) ∧ (Involves e2 ∧ Agent e2 y ∧ Recording e2 ∧ Agent e2 z)"

(* Explanation 2: Observations and data are a part of the results of an investigation and an experiment, and recording them in a journal is a method of documenting these results. *)
axiomatization where
  explanation_2: "∀x y z e1 e2. Observations x ∧ Data x ∧ Results y ∧ Investigation y ∧ Experiment y ∧ (PartOf x y) ∧ Journal z ∧ Recording e1 ∧ Agent e1 x ∧ In x z ∧ Documenting e2 ∧ Method e2 y"

(* Explanation 3: Recording observations and data in a journal inherently serves as a method of communicating the results of an investigation, and this act results in the communication of these results. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. Observations x ∧ Data x ∧ Journal y ∧ Recording e1 ∧ Agent e1 x ∧ In x y ∧ Communicating e2 ∧ Investigation x ∧ Method e1 y ∧ Results x"

theorem hypothesis:
  (* Premise: Alan is using cabbage juice to determine the relative pH of various household solutions. *)
  assumes asm: "Alan x ∧ CabbageJuice y ∧ HouseholdSolutions z ∧ Using e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Determine e2 ∧ Agent e2 x ∧ RelativePH e2 z"
  (* Hypothesis: Recording observations and data in a journal communicates the results of an investigation. *)
  shows "∃x y z e. Observations x ∧ Data y ∧ Journal z ∧ Recording e ∧ Agent e x ∧ Agent e y ∧ In x z ∧ In y z ∧ Communicating e ∧ Results x ∧ Investigation e"
  sledgehammer
  oops

end
