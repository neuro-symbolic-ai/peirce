theory esnli_2_2
imports Main

begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  SnowyDay :: "entity ⇒ bool"
  Street :: "entity ⇒ bool"
  Walk :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Location :: "event ⇒ entity ⇒ bool"
  Time :: "event ⇒ entity ⇒ bool"
  Winter :: "entity ⇒ bool"
  Occur :: "event ⇒ bool"
  Jacket :: "entity ⇒ bool"
  NorthFace :: "entity ⇒ bool"
  GarbageTruck :: "entity ⇒ bool"
  Past :: "event ⇒ entity ⇒ bool"
  With :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: If a man is walking on a snowy day down a street, it is winter. *)
axiomatization where
  explanation_1: "∀x y z e. (Man x ∧ SnowyDay y ∧ Street z ∧ Walk e ∧ Agent e x ∧ Location e z ∧ Time e y) ⟶ Winter y"

(* Explanation 2: Snowy days occur during winter. *)
axiomatization where
  explanation_2: "∀x y e. SnowyDay x ∧ Winter y ⟶ Occur e ∧ Time e y"

theorem hypothesis:
  (* Premise: On a snowy day a man with a north face jacket walks through the crowded streets past a garbage truck. *)
  assumes asm: "Man x ∧ Jacket y ∧ NorthFace y ∧ SnowyDay z ∧ Street w ∧ GarbageTruck v ∧ Walk e ∧ Agent e x ∧ Location e w ∧ Past e v ∧ Time e z ∧ With x y"
  (* Hypothesis: A man walks down the street in winter. *)
  shows "∃x y z e. Man x ∧ Street y ∧ Winter z ∧ Walk e ∧ Agent e x ∧ Location e y ∧ Time e z"
  using assms explanation_1 by blast
  

end
