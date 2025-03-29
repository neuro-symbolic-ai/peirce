theory esnli_6_1
imports Main

begin

typedecl entity
typedecl event

consts
  Men :: "entity ⇒ bool"
  Seven :: "entity ⇒ bool"
  Door :: "entity ⇒ bool"
  Train :: "entity ⇒ bool"
  Looking :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Inside :: "entity ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Group :: "entity ⇒ bool"
  Vests :: "entity ⇒ bool"
  Bright :: "entity ⇒ bool"
  Orange :: "entity ⇒ bool"
  Reflective :: "entity ⇒ bool"
  Wearing :: "event ⇒ bool"

(* Explanation 1: Seven men are looking inside the door of a train. *)
axiomatization where
  explanation_1: "∃x y z w e. Men x ∧ Seven x ∧ Door y ∧ Train z ∧ Looking e ∧ Agent e x ∧ Inside y z ∧ Inside x y"

(* Explanation 2: If someone is looking inside the door of a train, they are considered to be looking in the train. *)
axiomatization where
  explanation_2: "∀x y z e1 e2. (Looking e1 ∧ Agent e1 x ∧ Door y ∧ Train z ∧ Inside x y ∧ Inside y z) ⟶ (Looking e2 ∧ Agent e2 x ∧ In x z)"

(* Explanation 3: Seven men can be considered a group. *)
axiomatization where
  explanation_3: "∀x. (Men x ∧ Seven x) ⟶ Group x"

theorem hypothesis:
  (* Premise: Seven men wearing bright orange reflective vests are looking inside the door of a red train. *)
  assumes asm: "Men x ∧ Seven x ∧ Vests y ∧ Bright y ∧ Orange y ∧ Reflective y ∧ Door z ∧ Train w ∧ Red w ∧ Wearing e ∧ Agent e x ∧ Patient e y ∧ Looking v ∧ Agent v x ∧ Inside z w ∧ Inside x z"
  (* Hypothesis: A group of men are looking in a train. *)
  shows "∃x y z e. Group x ∧ Men y ∧ Train z ∧ Looking e ∧ Agent e x ∧ In x z"
  using assms explanation_2 explanation_3 by blast
  

end
