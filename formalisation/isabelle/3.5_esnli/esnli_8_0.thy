theory esnli_8_0
imports Main


begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Sidewalk :: "entity ⇒ bool"
  Dirty :: "entity ⇒ bool"
  On :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Outdoors :: "entity ⇒ bool"
  Found :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Outside :: "event ⇒ bool"
  OldMan :: "entity ⇒ bool"
  HardwareParts :: "entity ⇒ bool"
  Sells :: "event ⇒ bool"

(* Explanation 1: The man is on a dirty sidewalk. *)
axiomatization where
  explanation_1: "∃x y e. Man x ∧ Sidewalk y ∧ Dirty y ∧ On e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: Sidewalks are found outdoors, therefore, the man is outside. *)
axiomatization where
  explanation_2: "∀x y e. Sidewalk x ∧ Outdoors y ⟶ Found e ∧ Patient e x ∧ In x y"

(* Explanation 3: The man is outside. *)
axiomatization where
  explanation_3: "∃x e. Man x ∧ Outside e ∧ Agent e x"


theorem hypothesis:
  (* Premise: An old man sells hardware parts on a dirty sidewalk. *)
  assumes asm: "OldMan x ∧ HardwareParts y ∧ Sidewalk z ∧ Dirty z ∧ Sells e ∧ Agent e x ∧ Patient e y ∧ On e"
  (* Hypothesis: The man is outside. *)
  shows "∃x e. Man x ∧ Outside e ∧ Agent e x"
  using explanation_3 by blast
  

end
