theory clinical_44_5
imports Main


begin

typedecl entity
typedecl event

consts
  ExplanatorySentence :: "entity ⇒ bool"
  Specifying :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  PotentialRoleOfCREBBPBCORL1 :: "entity ⇒ bool"
  InCancer :: "entity ⇒ bool"
  Would :: "event ⇒ bool"
  Directly :: "event ⇒ bool"
  Link :: "event ⇒ bool"
  ConnectionBetweenCREBBPBCORL1AndCancer :: "entity ⇒ entity ⇒ bool"
  HypothesisThatCREBBPBCORL1HasRoleInCancer :: "entity ⇒ bool"

(* Explanation 1: Including an explanatory sentence specifying the potential role of CREBBP/BCORL1 in cancer would directly link the potential connection between CREBBP/BCORL1 and cancer to the hypothesis that CREBBP/BCORL1 has a role in cancer *)
axiomatization where
  explanation_1: "∃x y z e1 e2. ExplanatorySentence x ∧ Specifying e1 ∧ Agent e1 x ∧ PotentialRoleOfCREBBPBCORL1 y ∧ InCancer z ∧ Would e2 ∧ Directly e2 ∧ Link e2 ∧ Agent e2 x ∧ Patient e2 y ∧ ConnectionBetweenCREBBPBCORL1AndCancer y z ∧ HypothesisThatCREBBPBCORL1HasRoleInCancer z"


theorem hypothesis:
 assumes asm: "ExplanatorySentence x ∧ Specifying e1 ∧ Agent e1 x ∧ PotentialRoleOfCREBBPBCORL1 y ∧ InCancer z"
  (* Hypothesis: Hypothesis that CREBBP/BCORL1 has a role in cancer *)
 shows "∃x y z e1 e2. ExplanatorySentence x ∧ Specifying e1 ∧ Agent e1 x ∧ PotentialRoleOfCREBBPBCORL1 y ∧ InCancer z ∧ Would e2 ∧ Directly e2 ∧ Link e2 ∧ Agent e2 x ∧ Patient e2 y ∧ ConnectionBetweenCREBBPBCORL1AndCancer y z ∧ HypothesisThatCREBBPBCORL1HasRoleInCancer z"
  using explanation_1 by blast
  

end
