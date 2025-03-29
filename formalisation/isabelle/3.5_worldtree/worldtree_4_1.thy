theory worldtree_4_1
imports Main


begin

typedecl entity
typedecl event

consts
  Sulfur :: "entity ⇒ bool"
  LikelyYellow :: "entity ⇒ bool"
  Mineral :: "entity ⇒ bool"
  Minerals :: "entity ⇒ bool"
  Given :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Identify :: "event ⇒ bool"
  Sample :: "entity ⇒ bool"
  Her :: "entity ⇒ bool"
  Yellow :: "entity ⇒ bool"
  Janet :: "entity ⇒ bool"

(* Explanation 1: If an entity is sulfur, then it is likely to be yellow *)
axiomatization where
  explanation_1: "∀x. Sulfur x ⟶ LikelyYellow x"

(* Explanation 2: If an entity is sulfur, then it is a mineral *)
axiomatization where
  explanation_2: "∀x. Sulfur x ⟶ Mineral x"


theorem hypothesis:
  (* Premise 1: Janet has been given some minerals to identify *)
  assumes asm: "Janet x ∧ Minerals y ∧ Given e ∧ Agent e x ∧ Patient e y ∧ Identify e"
  (* Premise 2: One of her samples is yellow *)
  assumes asm: "Sample x ∧ Her x ∧ Yellow x"
  (* Hypothesis: Sulfur is a mineral that is likely to be yellow *)
  shows "∀x. Sulfur x ⟶ (Mineral x ∧ LikelyYellow x)"
  by (simp add: explanation_1 explanation_2)
  

end
