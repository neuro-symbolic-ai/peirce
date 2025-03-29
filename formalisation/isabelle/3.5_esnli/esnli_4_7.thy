theory esnli_4_7
imports Main


begin

typedecl entity
typedecl event

consts
  People :: "entity ⇒ bool"
  Stand :: "entity ⇒ bool"
  Near :: "entity ⇒ entity ⇒ bool"
  Outside :: "entity ⇒ entity ⇒ bool"
  IceCreamStand :: "entity ⇒ bool"
  Standing :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  Small :: "entity ⇒ bool"

(* Explanation 1: If the people are near the stand they are outside it *)
axiomatization where
  explanation_1: "∀x y z. People x ∧ Stand y ∧ Near x y ⟶ Outside x z"


theorem hypothesis:
  (* Premise 1: A small ice cream stand with two people standing near it *)
  assumes asm: "IceCreamStand x ∧ Small x ∧ People y ∧ Stand z ∧ IceCreamStand z ∧ Near y z ∧ Standing e ∧ Agent e y ∧ At y z"
  (* Hypothesis: Two people standing outside an ice cream stand *)
  shows "∃x y e. People x ∧ Stand y ∧ IceCreamStand y ∧ Standing e ∧ Agent e x ∧ At x y ∧ Outside x y"
  using assms explanation_1 by blast
  

end
