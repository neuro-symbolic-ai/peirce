theory esnli_4_4
imports Main

begin

typedecl entity
typedecl event

consts
  People :: "entity ⇒ bool"
  SmallIceCreamStand :: "entity ⇒ bool"
  IceCreamStand :: "entity ⇒ bool"
  Near :: "entity ⇒ entity ⇒ bool"
  Outside :: "entity ⇒ entity ⇒ bool"
  Standing :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"

(* Explanation 1: If people are near a small ice cream stand, they are outside the ice cream stand. *)
axiomatization where
  explanation_1: "∀x y. People x ∧ SmallIceCreamStand y ∧ Near x y ⟶ Outside x y"

(* Explanation 2: If people are standing near a small ice cream stand, they are outside the ice cream stand. *)
axiomatization where
  explanation_2: "∀x y e. People x ∧ SmallIceCreamStand y ∧ Standing e ∧ Agent e x ∧ Near x y ⟶ Outside x y"

(* Explanation 3: A small ice cream stand is a type of ice cream stand. *)
axiomatization where
  explanation_3: "∀x. SmallIceCreamStand x ⟶ IceCreamStand x"

theorem hypothesis:
  (* Premise: A small ice cream stand with two people standing near it. *)
  assumes asm: "SmallIceCreamStand x ∧ People y ∧ Standing e ∧ Agent e y ∧ Near y x"
  (* Hypothesis: Two people standing outside an ice cream stand. *)
  shows "∃x y z e. People x ∧ IceCreamStand y ∧ Standing e ∧ Agent e x ∧ Outside x y"
  using assms explanation_2 explanation_3 by blast
  

end
