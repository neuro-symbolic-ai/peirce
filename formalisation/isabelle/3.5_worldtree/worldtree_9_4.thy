theory worldtree_9_4
imports Main


begin

typedecl entity
typedecl event

consts
  Leaf :: "entity ⇒ bool"
  Object :: "entity ⇒ bool"
  Green :: "entity ⇒ bool"
  Appear :: "event ⇒ bool"
  Reflect :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  GreenLight :: "entity ⇒ bool"

(* Explanation 1: Leaves are objects. *)
axiomatization where
  explanation_1: "∀x. Leaf x ⟶ Object x"


theorem hypothesis:
 assumes asm: "Leaf x ∧ Green y"
  (* Hypothesis: Many leaves appear green because they reflect green light. *)
 shows "∃x y e. Leaf x ∧ Green y ∧ Appear e ∧ Agent e x ∧ Patient e y ∧ Reflect e1 ∧ Agent e1 x ∧ Patient e1 GreenLight"
  sledgehammer
  oops

end
