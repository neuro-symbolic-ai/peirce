theory esnli_7_0
imports Main

begin

typedecl entity
typedecl event

consts
  Directing :: "event ⇒ bool"
  Crowd :: "entity ⇒ bool"
  People :: "entity ⇒ bool"
  Herding :: "event ⇒ bool"
  Pedestrians :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Policeman :: "entity ⇒ bool"
  Walking :: "entity ⇒ bool"

(* Explanation 1: Directing a crowd of people is other expression of herding pedestrians. *)
axiomatization where
  explanation_1: "∀e1 e2 x y. Directing e1 ∧ Crowd x ∧ People y ∧ Herding e2 ∧ Pedestrians y ⟷ (Agent e1 x ∧ Agent e2 x ∧ Patient e1 y ∧ Patient e2 y)"

theorem hypothesis:
  (* Premise: A policeman is directing a crowd of people walking. *)
  assumes asm: "Policeman x ∧ Crowd y ∧ People z ∧ Walking z ∧ Directing e ∧ Agent e x ∧ Patient e y ∧ Patient e z"
  (* Hypothesis: A policeman is herding pedestrians. *)
  shows "∃x y e. Policeman x ∧ Pedestrians y ∧ Herding e ∧ Agent e x ∧ Patient e y"
  using assms explanation_1 by blast
  

end
