theory esnli_3_1
imports Main


begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Sleeping :: "event ⇒ bool"
  OnBed :: "event ⇒ bool"
  White :: "entity ⇒ bool"
  Bed :: "event ⇒ entity"
  Inside :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  AnimalPrintPants :: "entity ⇒ bool"

(* Explanation: Two men sleeping on a white bed implies that they are inside *)
axiomatization where
  explanation: "∃x y e. Man x ∧ Man y ∧ Sleeping e ∧ OnBed e ∧ White (Bed e) ∧ Inside e ∧ Agent e x ∧ Patient e y"


theorem hypothesis:
  (* Premise: Two men in animal print pants sleep on a white bed *)
  assumes asm: "Man x ∧ Man y ∧ AnimalPrintPants x ∧ Sleep e ∧ OnBed e ∧ White (Bed e) ∧ Agent e x ∧ Patient e y"
  shows "∃x y e. Man x ∧ Man y ∧ Inside e ∧ Agent e x ∧ Patient e y"
  using explanation by blast
  

end
