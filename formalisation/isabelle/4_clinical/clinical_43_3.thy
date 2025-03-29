theory clinical_43_3
imports Main

begin

typedecl entity
typedecl event

consts
  ClinicalTrial :: "entity ⇒ bool"
  NCT03568656 :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  CBP :: "entity ⇒ bool"
  CREBBP :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  EligibilityCriteria :: "event ⇒ bool"
  EligibilityCriterion :: "event ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"
  Has :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  MutationArm :: "entity"
  AnotherNameFor :: "entity ⇒ entity ⇒ bool"
  Gene :: "entity ⇒ bool"
  Targets :: "event ⇒ bool"

(* Explanation 1: Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm *)
axiomatization where
  explanation_1: "∃x y z e. ClinicalTrial x ∧ NCT03568656 x ∧ Mutation y ∧ CBP z ∧ In y z ∧ EligibilityCriteria e ∧ For e MutationArm ∧ Has e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: CBP is another name for CREBBP *)
axiomatization where
  explanation_2: "∀x y. CBP x ∧ CREBBP y ⟶ AnotherNameFor x y"

(* Explanation 3: If a clinical trial has a mutation in a gene as an eligibility criterion, then the trial targets that gene *)
axiomatization where
  explanation_3: "∀x y z e1 e2. ClinicalTrial x ∧ Mutation y ∧ Gene z ∧ In y z ∧ EligibilityCriterion e1 ∧ Has e1 ∧ Agent e1 x ∧ Patient e1 y ⟶ (Targets e2 ∧ Agent e2 x ∧ Patient e2 z)"

(* Explanation 4: If CBP is another name for CREBBP, then a clinical trial with a mutation in CBP as an eligibility criterion targets CREBBP *)
axiomatization where
  explanation_4: "∀x y z e1 e2. (CBP x ∧ CREBBP y ⟶ AnotherNameFor x y) ⟶ (ClinicalTrial z ∧ Mutation e1 ∧ In e1 x ∧ EligibilityCriterion e2 ∧ Has e2 ∧ Agent e2 z ∧ Patient e2 e1 ⟶ (Targets e2 ∧ Agent e2 z ∧ Patient e2 y))"

theorem hypothesis:
  assumes asm: "NCT03568656 x ∧ CREBBP y"
  (* Hypothesis: NCT03568656 targets CREBBP *)
  shows "∃x y e. NCT03568656 x ∧ CREBBP y ∧ Targets e ∧ Agent e x ∧ Patient e y"
proof -
  (* From the premise, we have known information about NCT03568656 and CREBBP. *)
  from asm have "NCT03568656 x ∧ CREBBP y" by simp
  (* Explanation 1 provides that Clinical Trial NCT03568656 has mutation in CBP as eligibility criteria for mutation arm. *)
  (* Explanation 2 states that CBP is another name for CREBBP. *)
  (* Explanation 4 states that if CBP is another name for CREBBP, then a clinical trial with a mutation in CBP as an eligibility criterion targets CREBBP. *)
  (* Using the logical relation Implies(B, E), we can infer that NCT03568656 targets CREBBP. *)
  then have "∃e. Targets e ∧ Agent e x ∧ Patient e y" sledgehammer
  then show ?thesis <ATP>
qed

end
