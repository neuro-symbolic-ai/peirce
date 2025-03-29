theory esnli_10_0
imports Main

begin

typedecl entity
typedecl event

consts
  RedMakeup :: "entity ⇒ bool"
  Makeup :: "entity ⇒ bool"
  Men :: "entity ⇒ bool"
  DressedIn :: "entity ⇒ entity ⇒ bool"
  Festival :: "entity ⇒ bool"
  Costume :: "entity ⇒ bool"
  Display :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  OlderMan :: "entity ⇒ bool"
  Cream :: "entity ⇒ bool"
  Face :: "entity ⇒ bool"
  Has :: "event ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: In red makeup is a type of makeup. *)
axiomatization where
  explanation_1: "∀x. RedMakeup x ⟶ Makeup x"

theorem hypothesis:
  (* Premise: A festival displays two men dressed in red makeup and costume, while an older man has cream on his face. *)
  assumes asm: "Festival x ∧ Men y ∧ RedMakeup z ∧ Costume w ∧ Display e1 ∧ Agent e1 x ∧ Patient e1 y ∧ DressedIn y z ∧ DressedIn y w ∧ OlderMan y ∧ Cream z ∧ Face w ∧ Has e2 ∧ Agent e2 y ∧ Patient e2 z ∧ On z w"
  (* Hypothesis: Two men are dressed in makeup. *)
  shows "∃x y. Men x ∧ Makeup y ∧ DressedIn x y"
  using assms explanation_1 by blast
  

end
