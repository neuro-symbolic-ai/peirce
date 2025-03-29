theory worldtree_1_0
imports Main

begin

typedecl entity
typedecl event

consts
  Pulley :: "entity ⇒ bool"
  Flag :: "entity ⇒ bool"
  Flagpole :: "entity ⇒ bool"
  Used :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Lift :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  SimpleMachine :: "entity ⇒ bool"
  Move :: "event ⇒ bool"
  Up :: "event ⇒ bool"

(* Explanation 1: A pulley is used to lift a flag on a flagpole. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. Pulley x ∧ Flag y ∧ Flagpole z ∧ Used e1 ∧ Agent e1 x ∧ Lift e2 ∧ Agent e2 x ∧ Patient e2 y ∧ On y z"

(* Explanation 2: A pulley is a kind of simple machine. *)
axiomatization where
  explanation_2: "∀x. Pulley x ⟶ SimpleMachine x"

(* Explanation 3: To lift means to move up. *)
axiomatization where
  explanation_3: "∀e1 e2. Lift e1 ⟷ (Move e2 ∧ Up e2)"

theorem hypothesis:
  assumes asm: "Pulley x ∧ Flag y ∧ Flagpole z"
  (* Hypothesis: A pulley is a simple machine that helps move a flag up a flagpole. *)
  shows "∃x y z e1 e2. Pulley x ∧ SimpleMachine x ∧ Flag y ∧ Flagpole z ∧ Helps e1 ∧ Agent e1 x ∧ Move e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Up y z"
  sledgehammer
  oops

end
