theory worldtree_7_8
imports Main


begin

typedecl entity
typedecl event

consts
  Entity :: "entity ⇒ bool"
  AbleToRead :: "entity ⇒ bool"
  LearnedTrait :: "entity ⇒ bool"

(* Explanation 1: If an entity has the ability to read, then it is both able to read and an example of a learned trait. *)
axiomatization where
  explanation_1: "∀x. Entity x ⟶ (AbleToRead x ∧ LearnedTrait x)"


theorem hypothesis:
 assumes asm: "Entity x"
  (* Hypothesis: Being able to read is an example of a learned trait. *)
 shows "AbleToRead x ⟶ LearnedTrait x"
  using assms explanation_1 by auto
  

end
