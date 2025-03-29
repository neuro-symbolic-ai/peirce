theory esnli_4_6
imports Main


begin

typedecl entity
typedecl event

consts
  People :: "entity ⇒ bool"
  Stand :: "entity ⇒ bool"
  Near :: "event ⇒ bool"
  Outside :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Two :: "entity ⇒ bool"
  IceCreamStand :: "entity ⇒ bool"
  Standing :: "event ⇒ bool"

(* Explanation 1: If the people are near the stand they are outside it *)
axiomatization where
  explanation_1: "∀x y z e. People x ∧ Stand y ∧ Near e ∧ Agent e x ∧ Patient e y ⟶ Outside z ∧ Agent z x"


theorem hypothesis:
  (* Premise 1: A small ice cream stand with two people standing near it *)
  assumes asm: "Stand x ∧ IceCreamStand x ∧ People y ∧ Two y ∧ Standing e ∧ Agent e y ∧ Near z ∧ Agent z y ∧ Patient z x"
  (* Hypothesis: Two people standing outside an ice cream stand *)
  shows "∃x y e. People x ∧ Stand y ∧ IceCreamStand y ∧ Standing e ∧ Agent e x ∧ Outside e y"
  sledgehammer
  oops

end
