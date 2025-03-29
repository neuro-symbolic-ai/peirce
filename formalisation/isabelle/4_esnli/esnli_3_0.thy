theory esnli_3_0
imports Main

begin

typedecl entity
typedecl event

consts
  Men :: "entity ⇒ bool"
  Bed :: "entity ⇒ bool"
  White :: "entity ⇒ bool"
  Sleeping :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Inside :: "entity ⇒ bool"
  Pants :: "entity ⇒ bool"
  AnimalPrint :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Two men sleeping on a white bed implies that they are inside. *)
axiomatization where
  explanation_1: "∀x y z e. Men x ∧ Bed y ∧ White y ∧ Sleeping e ∧ Agent e x ∧ Patient e y ⟶ Inside x"

theorem hypothesis:
  (* Premise: Two men in animal print pants sleep on a white bed. *)
  assumes asm: "Men x ∧ Pants y ∧ AnimalPrint y ∧ Bed z ∧ White z ∧ Sleeping e ∧ Agent e x ∧ Patient e z ∧ In x y"
  (* Hypothesis: Two men are inside. *)
  shows "∃x. Men x ∧ Inside x"
  using assms explanation_1 by auto
  

end
