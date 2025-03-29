theory esnli_2_0
imports Main


begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Walking :: "event ⇒ bool"
  OnSnowyDay :: "event ⇒ bool"
  DownStreet :: "event ⇒ bool"
  LikelyWinter :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  NorthFaceJacket :: "entity ⇒ bool"
  ThroughStreets :: "event ⇒ bool"
  PastGarbageTruck :: "event ⇒ bool"
  Wearing :: "entity ⇒ entity ⇒ bool"
  CrowdedStreets :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Since the man is walking on a snowy day down a street, it is likely winter. *)
axiomatization where
  explanation_1: "∃x e. Man x ∧ Walking e ∧ OnSnowyDay e ∧ DownStreet e ∧ LikelyWinter e ∧ Agent e x"


theorem hypothesis:
  (* Premise 1: On a snowy day a man with a north face jacket walks through the crowded streets past a garbage truck. *)
  assumes asm: "Man x ∧ NorthFaceJacket y ∧ Walking e ∧ ThroughStreets e ∧ PastGarbageTruck e ∧ Agent e x ∧ Wearing x y ∧ CrowdedStreets z ∧ In x z"
  (* Hypothesis: A man walks down the street in winter. *)
  shows "∃x e. Man x ∧ Walking e ∧ DownStreet e ∧ LikelyWinter e ∧ Agent e x"
  using explanation_1 by blast
  

end
