theory clinical_97_0
imports Main

begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  BRAF_V600E_Mutation :: "entity ⇒ bool"
  NewMutations :: "entity ⇒ bool"
  AR_Amplification :: "entity ⇒ bool"
  Has :: "event ⇒ bool"
  Acquired :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  BRAF_V600E :: "entity ⇒ bool"
  BRAF_Mutation :: "entity ⇒ bool"
  Common :: "entity ⇒ bool"
  Hyperactivation :: "entity ⇒ bool"
  OncogenicTransformation :: "entity ⇒ bool"
  Results :: "event ⇒ bool"

(* Explanation 1: Patient has BRAF V600E mutation… acquired new mutations and AR amplification. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2. Patient x ∧ BRAF_V600E_Mutation y ∧ NewMutations z ∧ AR_Amplification w ∧ Has e1 ∧ Agent e1 x ∧ Patient y ∧ Acquired e2 ∧ Agent e2 x ∧ Patient z ∧ Patient w"

(* Explanation 2: BRAF V600E is the most common BRAF mutation and results in constitutive hyperactivation and oncogenic transformation. *)
axiomatization where
  explanation_2: "∀x y z e. BRAF_V600E x ∧ BRAF_Mutation y ∧ Common y ∧ Hyperactivation z ∧ OncogenicTransformation z ∧ Results e ∧ Agent e x ∧ Patient z"

theorem hypothesis:
  assumes asm: "Patient x"
  (* Hypothesis: Patient has common BRAF V600E mutation. *)
  shows "∃x y e. Patient x ∧ BRAF_V600E_Mutation y ∧ Common y ∧ Has e ∧ Agent e x ∧ Patient y"
  using explanation_1 explanation_2 by blast
  

end
