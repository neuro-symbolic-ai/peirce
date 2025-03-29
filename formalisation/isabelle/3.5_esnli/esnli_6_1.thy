theory esnli_6_1
imports Main


begin

typedecl entity
typedecl event

consts
  SevenMen :: "entity ⇒ bool"
  BrightOrange :: "entity ⇒ bool"
  Reflective :: "entity ⇒ bool"
  Vests :: "entity ⇒ bool"
  GroupOfMen :: "entity ⇒ bool"
  MenGroup :: "entity ⇒ bool"
  Looking :: "event ⇒ bool"
  InsideDoor :: "event ⇒ bool"
  RedTrain :: "entity ⇒ bool"
  Of :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Seven men wearing bright orange reflective vests are considered as a group of men. *)
axiomatization where
  explanation_1: "∃x. SevenMen x ∧ BrightOrange x ∧ Reflective x ∧ Vests x ∧ GroupOfMen x"

(* Explanation 2: The group of men looking inside the door of a red train can be represented as a MenGroup. *)
axiomatization where
  explanation_2: "∃x y z e. MenGroup x ∧ Looking e ∧ InsideDoor e ∧ RedTrain y ∧ Of x y"


theorem hypothesis:
  (* Premise: none *)
  assumes asm: "True"
  (* Hypothesis: A group of men are looking in a train. *)
  shows "∃x e. MenGroup x ∧ Looking e ∧ InsideDoor e"
  using explanation_2 by auto
  

end
