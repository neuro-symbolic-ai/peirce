theory esnli_7_0
imports Main


begin

typedecl entity
typedecl event

consts
  Directing :: "event ⇒ bool"
  CrowdOfPeople :: "entity ⇒ bool"
  HerdingPedestrians :: "event ⇒ bool"
  Herding :: "entity ⇒ bool"
  Policeman :: "entity ⇒ bool"
  Pedestrians :: "entity ⇒ bool"

(* Explanation 1: Directing a crowd of people is another expression of herding pedestrians. *)
axiomatization where
  explanation_1: "∀e1 e2. Directing e1 ∧ CrowdOfPeople e2 ⟷ HerdingPedestrians e1 ∧ Herding e2"


theorem hypothesis:
  (* Premise 1: A policeman is directing a crowd of people walking. *)
  assumes asm: "Policeman x ∧ CrowdOfPeople y ∧ Walking z ∧ Directing e ∧ Agent e x ∧ Patient e y ∧ Manner e z"
  (* Hypothesis: A policeman is herding pedestrians. *)
  shows "∃x y e. Policeman x ∧ Pedestrians y ∧ Herding e ∧ Agent e x ∧ Patient e y"
  sledgehammer
  oops

end
