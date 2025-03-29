theory esnli_10_6
imports Main


begin

typedecl entity
typedecl event

consts
  Red :: "entity ⇒ bool"
  Makeup :: "entity ⇒ bool"
  TypeOfMakeup :: "entity ⇒ bool"
  Man :: "entity ⇒ bool"
  Dressed :: "event ⇒ bool"
  In :: "entity ⇒ event ⇒ bool"
  Festival :: "entity ⇒ bool"
  OlderMan :: "entity ⇒ bool"
  Cream :: "entity ⇒ bool"
  Displays :: "event ⇒ bool"
  Costume :: "event ⇒ bool"
  CreamFace :: "event ⇒ bool"
  OnFace :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: In red makeup is a type of makeup. *)
axiomatization where
  explanation_1: "∀x. Red x ∧ Makeup x ⟶ TypeOfMakeup x"


theorem hypothesis:
  (* Premise: A festival displays two men dressed in red makeup and costume, while an older man has cream on his face. *)
  assumes asm: "Festival x ∧ Man y ∧ Man z ∧ OlderMan w ∧ Cream v ∧ Displays e1 ∧ Dressed e1 ∧ In y e1 ∧ In z e1 ∧ Red v ∧ Costume e1 ∧ In w e2 ∧ OnFace w v ∧ CreamFace e2"
  (* Hypothesis: Two men are dressed in makeup. *)
  shows "∃x y e. Man x ∧ Man y ∧ Dressed e ∧ In x e ∧ In y e ∧ Makeup e"
  sledgehammer
  oops

end
