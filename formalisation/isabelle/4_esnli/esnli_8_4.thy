theory esnli_8_4
imports Main

begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Sidewalk :: "entity ⇒ bool"
  Dirty :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  Outdoors :: "entity ⇒ bool"
  Outside :: "entity ⇒ bool"
  OldMan :: "entity ⇒ bool"
  HardwareParts :: "entity ⇒ bool"
  Sells :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The man is on a dirty sidewalk. *)
axiomatization where
  explanation_1: "∀x y. Man x ∧ Sidewalk y ∧ Dirty y ⟶ On x y"

(* Explanation 2: If a specific sidewalk is dirty, it is found outdoors. *)
axiomatization where
  explanation_2: "∀y. Sidewalk y ∧ Dirty y ⟶ Outdoors y"

(* Explanation 3: If a man is on a dirty sidewalk and that sidewalk is outdoors, then the man is outside. *)
axiomatization where
  explanation_3: "∀x y. (Man x ∧ Sidewalk y ∧ Dirty y ∧ On x y ∧ Outdoors y) ⟶ Outside x"

(* Explanation 4: An old man is a man. *)
axiomatization where
  explanation_4: "∀x. OldMan x ⟶ Man x"

theorem hypothesis:
  (* Premise: An old man sells hardware parts on a dirty sidewalk. *)
  assumes asm: "OldMan x ∧ HardwareParts y ∧ Sidewalk z ∧ Dirty z ∧ Sells e ∧ Agent e x ∧ Patient e y ∧ On x z"
  (* Hypothesis: The man is outside. *)
  shows "∀x. Man x ⟶ Outside x"
  using assms explanation_1 explanation_2 explanation_3 by blast
  

end
