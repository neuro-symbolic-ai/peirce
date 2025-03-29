theory worldtree_3_1
imports Main


begin

typedecl entity
typedecl event

consts
  Hurricane :: "entity ⇒ bool"
  Tornado :: "entity ⇒ bool"
  HighWindSpeeds :: "event ⇒ bool"
  PartOf :: "entity ⇒ event ⇒ bool"

(* Explanation 1: For hurricanes, there exists an event "e" such that it has high wind speeds and the hurricane is part of that event. *)
axiomatization where
  explanation_1: "∀x. Hurricane x ⟶ (∃e. HighWindSpeeds e ∧ PartOf x e)"

(* Explanation 2: For tornadoes, there exists an event "e" such that it has high wind speeds and the tornado is part of that event. *)
axiomatization where
  explanation_2: "∀x. Tornado x ⟶ (∃e. HighWindSpeeds e ∧ PartOf x e)"


theorem hypothesis:
 assumes asm: "Hurricane x ∨ Tornado x"
  (* Hypothesis: Both hurricanes and tornadoes always have high winds. *)
 shows "∃e. HighWindSpeeds e ∧ PartOf x e"
  using assms explanation_1 explanation_2 by blast
  

end
