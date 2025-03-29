theory esnli_1_1
imports Main

begin

typedecl entity
typedecl event

consts
  Infant :: "entity ⇒ bool"
  Crying :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Unhappy :: "entity ⇒ bool"
  Baby :: "entity ⇒ bool"
  Crib :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: If the infant is crying, it can be assumed that they are unhappy. *)
axiomatization where
  explanation_1: "∀x e. (Infant x ∧ Crying e ∧ Agent e x) ⟶ Unhappy x"

(* Explanation 2: An infant is a type of baby. *)
axiomatization where
  explanation_2: "∀x. Infant x ⟶ Baby x"

theorem hypothesis:
  (* Premise: An infant is in a crib and crying. *)
  assumes asm: "Infant x ∧ Crib y ∧ In x y ∧ Crying e ∧ Agent e x"
  (* Hypothesis: A baby is unhappy. *)
  shows "∃x. Baby x ∧ Unhappy x"
  using assms explanation_1 explanation_2 by blast
  

end
