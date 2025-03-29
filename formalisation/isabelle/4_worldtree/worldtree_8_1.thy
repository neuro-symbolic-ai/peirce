theory worldtree_8_1
imports Main

begin

typedecl entity
typedecl event

consts
  Investigation :: "entity ⇒ bool"
  Experimentation :: "entity ⇒ bool"
  Requires :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Observations :: "entity ⇒ bool"
  Data :: "entity ⇒ bool"
  Results :: "entity ⇒ bool"
  Experiment :: "entity ⇒ bool"
  PartOf :: "entity ⇒ entity ⇒ bool"
  Of :: "entity ⇒ entity ⇒ bool"
  Journal :: "entity ⇒ bool"
  Recording :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Communicating :: "event ⇒ bool"
  Alan :: "entity ⇒ bool"
  CabbageJuice :: "entity ⇒ bool"
  HouseholdSolutions :: "entity ⇒ bool"
  Using :: "event ⇒ bool"
  Determine :: "event ⇒ bool"
  RelativePH :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Investigation sometimes requires experimentation. *)
axiomatization where
  explanation_1: "∃x y e. Investigation x ∧ Experimentation y ∧ Requires e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: Observations and data are a part of the results of an experiment. *)
axiomatization where
  explanation_2: "∀x y z w. Observations x ∧ Data y ∧ Results z ∧ Experiment w ⟶ (PartOf x z ∧ PartOf y z ∧ Of z w)"

(* Explanation 3: Recording observations and data in a journal is a method of communicating the results of an investigation. *)
axiomatization where
  explanation_3: "∃x y z w v e. Observations x ∧ Data y ∧ Journal z ∧ Investigation w ∧ Results v ∧ Recording e ∧ Agent e x ∧ Agent e y ∧ In x z ∧ In y z ∧ Communicating e ∧ Patient e v ∧ Of v w"

theorem hypothesis:
  (* Premise: Alan is using cabbage juice to determine the relative pH of various household solutions. *)
  assumes asm: "Alan x ∧ CabbageJuice y ∧ HouseholdSolutions z ∧ Using e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Determine e2 ∧ Agent e2 x ∧ RelativePH e2 z"
  (* Hypothesis: Recording observations and data in a journal communicates the results of an investigation. *)
  shows "∃x y z e. Observations x ∧ Data y ∧ Journal z ∧ Investigation w ∧ Results v ∧ Recording e ∧ Agent e x ∧ Agent e y ∧ In x z ∧ In y z ∧ Communicates e ∧ Patient e v ∧ Of v w"
proof -
  (* From the premise, we have information about Alan using cabbage juice to determine the relative pH of household solutions. *)
  from asm have "Alan x ∧ CabbageJuice y ∧ HouseholdSolutions z ∧ Using e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Determine e2 ∧ Agent e2 x ∧ RelativePH e2 z" by meson
  (* Explanation 3 provides a direct relation between recording observations and data in a journal and communicating the results of an investigation. *)
  (* We can use this explanation to infer the hypothesis directly. *)
  from explanation_3 have "∃x y z w v e. Observations x ∧ Data y ∧ Journal z ∧ Investigation w ∧ Results v ∧ Recording e ∧ Agent e x ∧ Agent e y ∧ In x z ∧ In y z ∧ Communicating e ∧ Patient e v ∧ Of v w" sledgehammer
  then show ?thesis <ATP>
qed

end
