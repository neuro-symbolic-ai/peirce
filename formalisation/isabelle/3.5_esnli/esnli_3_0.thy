theory esnli_3_0
imports Main


begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Sleeping :: "event ⇒ bool"
  On :: "event ⇒ entity ⇒ bool"
  Bed :: "entity ⇒ bool"
  White :: "entity ⇒ bool"
  Inside :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  AnimalPrintPants :: "entity ⇒ bool"

(* Explanation 1: Two men sleeping on a white bed implies that they are inside. *)
axiomatization where
  explanation_1: "∃x y e. Man x ∧ Man y ∧ Sleeping e ∧ On e Bed ∧ White Bed ∧ Inside e ∧ Agent e x ∧ Agent e y"


theorem hypothesis:
  (* Premise 1: Two men in animal print pants sleep on a white bed. *)
  assumes asm: "Man x ∧ Man y ∧ AnimalPrintPants x ∧ Sleeping e ∧ Agent e x ∧ On e x Bed ∧ White Bed"
  (* Hypothesis: Two men are inside. *)
  shows "∃x y e. Man x ∧ Man y ∧ Inside e ∧ Agent e x ∧ Agent e y"
proof -
  (* From the premise, we can get known information about the men, sleeping, agent, and the white bed. *)
  from asm have "Man x ∧ Man y ∧ Sleeping e ∧ Agent e x ∧ On e x Bed ∧ White Bed" <ATP>
  (* There is a logical relation Implies(A, B), Implies(Two men sleeping on a white bed, they are inside) *)
  (* A is from explanatory sentence 1, B is from explanatory sentence 1. *)
  (* We already have the men and the white bed, so we can infer that they are inside. *)
  then have "Man x ∧ Man y ∧ Inside e ∧ Agent e x ∧ Agent e y" <ATP>
  then show ?thesis <ATP>
qed

end
