theory worldtree_1_0
imports Main


begin

typedecl entity
typedecl event

consts
  Pulley :: "entity ⇒ bool"
  Flag :: "entity ⇒ bool"
  Flagpole :: "entity ⇒ bool"
  Lift :: "event ⇒ bool"
  UsedFor :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  SimpleMachine :: "entity ⇒ bool"
  KindOf :: "entity ⇒ entity ⇒ bool"
  MoveUp :: "entity ⇒ bool"

(* Explanation 1: A pulley is used to lift a flag on a flagpole. *)
axiomatization where
  explanation_1: "∃x y z e. Pulley x ∧ Flag y ∧ Flagpole z ∧ Lift e ∧ UsedFor e ∧ Agent e x ∧ Patient e y ∧ On y z"

(* Explanation 2: A pulley is a kind of simple machine. *)
axiomatization where
  explanation_2: "∀x y. Pulley x ∧ SimpleMachine y ⟶ KindOf x y"

(* Explanation 3: To lift means to move up. *)
axiomatization where
  explanation_3: "∀x y. Lift x ⟷ MoveUp y"


theorem hypothesis:
 assumes asm: "Pulley x ∧ SimpleMachine y ∧ Flag z ∧ Flagpole e"
  (* Hypothesis: A pulley is a simple machine that helps move a flag up a flagpole. *)
 shows "∃x y z e. Pulley x ∧ SimpleMachine y ∧ Flag z ∧ Flagpole e ∧ MoveUp z e ∧ Help e ∧ Agent e x ∧ Patient e z ∧ Up z e"
  sledgehammer
  oops

end
