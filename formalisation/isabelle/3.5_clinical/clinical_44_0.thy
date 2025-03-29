theory clinical_44_0
imports Main


begin

typedecl entity
typedecl event

consts
  CREBBPBCORL1 :: "entity ⇒ bool"
  OssifyingMyxoidTumour :: "entity ⇒ bool"
  ReportedIn :: "entity ⇒ entity ⇒ bool"
  UnknownRelevance :: "entity ⇒ bool"
  CREBBPBCORL1Fusion :: "entity ⇒ bool"
  Of :: "entity ⇒ entity ⇒ bool"
  Role :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Potential :: "entity ⇒ bool"
  In :: "event ⇒ entity ⇒ bool"
  Cancer :: "entity ⇒ bool"

(* Explanation 1: CREBBP/BCORL1 reported in patients with ossifying myxoid tumour *)
axiomatization where
  explanation_1: "∃x y. CREBBPBCORL1 x ∧ OssifyingMyxoidTumour y ∧ ReportedIn x y"

(* Explanation 2: Unknown relevance of CREBBP/BCORL1 fusion *)
axiomatization where
  explanation_2: "∃x y. UnknownRelevance x ∧ CREBBPBCORL1Fusion y ∧ Of x y"


theorem hypothesis:
 assumes asm: "CREBBPBCORL1 x ∧ Role e ∧ Patient e x ∧ Potential y ∧ In e y"
  (* Hypothesis: CREBBP/BCORL1 potential role in cancer *)
 shows "∃x y z e. CREBBPBCORL1(x) ∧ Role(e) ∧ Patient(e, x) ∧ Potential(y) ∧ In(e, y) ∧ Cancer(z)"
  sledgehammer
  oops

end
