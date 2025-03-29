theory esnli_5_0
imports Main

begin

typedecl entity
typedecl event

consts
  Cute :: "entity ⇒ bool"
  Couple :: "entity ⇒ bool"
  Club :: "entity ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: A cute couple at a club means a couple is at a club. *)
axiomatization where
  explanation_1: "∀x y. (Cute x ∧ Couple x ∧ Club y ∧ At x y) ⟷ (Couple x ∧ Club y ∧ At x y)"

theorem hypothesis:
  (* Premise: A cute couple at a club. *)
  assumes asm: "Cute x ∧ Couple x ∧ Club y ∧ At x y"
  (* Hypothesis: The couple is at a club. *)
  shows "∃x y. Couple x ∧ Club y ∧ At x y"
  using assms by blast
  

end
