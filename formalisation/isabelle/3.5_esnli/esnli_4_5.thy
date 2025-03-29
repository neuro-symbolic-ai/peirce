theory esnli_4_5
imports Main


begin

typedecl entity
typedecl event

consts
  People :: "entity ⇒ bool"
  Stand :: "entity ⇒ bool"
  Near :: "event ⇒ entity ⇒ bool"
  Outside :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  IceCreamStand :: "entity ⇒ bool"
  Standing :: "event ⇒ bool"
  Small :: "entity ⇒ bool"
  Two :: "entity ⇒ bool"

(* Explanation 1: If the people are near the stand they are outside it *)
axiomatization where
  explanation_1: "∀x y z e. People x ∧ Stand y ∧ Near e x ∧ Agent e x ∧ Patient e y ⟶ Outside z ∧ Agent z x"


theorem hypothesis:
  (* Premise 1: A small ice cream stand with two people standing near it *)
  assumes asm: "IceCreamStand x ∧ Small x ∧ People y ∧ Two y ∧ Standing e ∧ Agent e y ∧ Near e x"
  (* Hypothesis: Two people standing outside an ice cream stand *)
  shows "∃x y e. People x ∧ Stand y ∧ IceCreamStand y ∧ Standing e ∧ Agent e x ∧ Outside e y"
  sledgehammer
  oops

end
