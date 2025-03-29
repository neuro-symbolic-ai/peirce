theory clinical_85_0
imports Main

begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  TripleNegativeBreastCancer :: "entity ⇒ bool"
  With :: "entity ⇒ entity ⇒ bool"
  TNBC :: "entity ⇒ bool"
  HeterogeneousGroup :: "entity ⇒ bool"
  Tumors :: "entity ⇒ bool"
  BreastCancers :: "entity ⇒ bool"
  Comprising :: "entity ⇒ entity ⇒ bool"
  DefinedAsAbsence :: "entity ⇒ entity ⇒ bool"
  ER :: "entity ⇒ bool"
  PR :: "entity ⇒ bool"
  NegativityForHER2 :: "entity ⇒ bool"
  BreastCancer :: "entity ⇒ bool"
  HER2 :: "entity ⇒ bool"
  Has :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  NoExpression :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Patient with Triple Negative Breast Cancer. *)
axiomatization where
  explanation_1: "∃x y. Patient x ∧ TripleNegativeBreastCancer y ∧ With x y"

(* Explanation 2: TNBC is a heterogeneous group of tumors comprising various breast cancers (BCs) defined as the absence of [ER and PR] with corresponding negativity for [HER-2]. *)
axiomatization where
  explanation_2: "∃x y z. TNBC x ∧ HeterogeneousGroup x ∧ Tumors y ∧ BreastCancers z ∧ Comprising x z ∧ DefinedAsAbsence x y ∧ ER y ∧ PR y ∧ NegativityForHER2 y"

theorem hypothesis:
  assumes asm: "Patient x ∧ BreastCancer y"
  (* Hypothesis: Patient has breast cancer that has no expression of ER, PR or HER 2. *)
  shows "∃x y z e1 e2. Patient x ∧ BreastCancer y ∧ ER z ∧ PR z ∧ HER2 z ∧ Has e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Has e2 ∧ Agent e2 y ∧ NoExpression e2 z"
  sledgehammer
  oops

end
