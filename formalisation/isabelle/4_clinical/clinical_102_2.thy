theory clinical_102_2
imports Main

begin

typedecl entity
typedecl event

consts
  Lapatinib :: "entity ⇒ bool"
  Neratinib :: "entity ⇒ bool"
  HER2KinaseDomain :: "entity ⇒ bool"
  Tumors :: "entity ⇒ bool"
  Mutations :: "entity ⇒ bool"
  Patients :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Efficacy :: "event ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Benefit :: "event ⇒ bool"
  Inhibitor :: "entity ⇒ bool"
  Irreversible :: "entity ⇒ bool"
  Targeted :: "event ⇒ bool"
  TreatmentResistance :: "entity ⇒ bool"
  BreastCancerPatients :: "entity ⇒ bool"
  Overcome :: "event ⇒ bool"
  Effective :: "event ⇒ bool"
  ERBB2V777L :: "entity ⇒ bool"
  ClinicalTrials :: "entity ⇒ bool"
  BreastCarcinoma :: "entity ⇒ bool"
  InclusionCriterion :: "entity ⇒ entity ⇒ bool"
  Open :: "entity ⇒ bool"
  Closed :: "entity ⇒ bool"
  Access :: "event ⇒ bool"
  Trials :: "entity ⇒ bool"
  InclusionCriteria :: "entity ⇒ entity ⇒ bool"
  Phase1Phase2 :: "entity ⇒ bool"
  Phase2 :: "entity ⇒ bool"
  Treatment :: "entity ⇒ bool"
  ClinicalTrial :: "entity ⇒ bool"

(* Explanation 1: Lapatinib and neratinib bind to the HER2 kinase domain and are therefore expected to have efficacy against tumors with these mutations in the kinase domain, which directly benefits patients with such mutations. *)
axiomatization where
  explanation_1: "∃x y z w v u e1 e2 e3. Lapatinib x ∧ Neratinib y ∧ HER2KinaseDomain z ∧ Tumors w ∧ Mutations v ∧ Patients u ∧ Bind e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Patient e1 z ∧ Efficacy e2 ∧ Agent e2 x ∧ Agent e2 y ∧ Patient e2 w ∧ In w v ∧ Benefit e3 ∧ Agent e3 u ∧ Patient e3 v"

(* Explanation 2: An irreversible inhibitor that is targeted to the HER2 kinase domain may overcome treatment resistance and be effective in breast cancer patients. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. Inhibitor x ∧ Irreversible x ∧ HER2KinaseDomain y ∧ Targeted e1 ∧ Agent e1 x ∧ Patient e1 y ∧ TreatmentResistance z ∧ BreastCancerPatients w ∧ (Overcome e2 ∧ Agent e2 x ∧ Patient e2 z) ∧ Effective e2 ∧ Patient e2 w"

(* Explanation 3: ERBB2 V777L is an inclusion criterion in 4 clinical trials for breast carcinoma, of which 4 are open and 0 are closed. *)
axiomatization where
  explanation_3: "∃x y z. ERBB2V777L x ∧ ClinicalTrials y ∧ BreastCarcinoma z ∧ InclusionCriterion x y ∧ Open y ∧ Closed y"

(* Explanation 4: Patients with ERBB2 V777L may access these open clinical trials. *)
axiomatization where
  explanation_4: "∃x y z e. Patients x ∧ ERBB2V777L y ∧ ClinicalTrials z ∧ Open z ∧ Access e ∧ Agent e x ∧ Patient e z"

(* Explanation 5: Of the trials that contain ERBB2 V777L and breast carcinoma as inclusion criteria, 1 is phase 1/phase 2 (1 open) and 3 are phase 2 (3 open). *)
axiomatization where
  explanation_5: "∃x y z. Trials x ∧ ERBB2V777L y ∧ BreastCarcinoma z ∧ InclusionCriteria y x ∧ InclusionCriteria z x ∧ Phase1Phase2 x ∧ Open x ∧ Phase2 x ∧ Open x"

theorem hypothesis:
  assumes asm: "Patient e1 x ∧ Treatment y ∧ ClinicalTrial z ∧ ERBB2V777L z ∧ Agent e1 x ∧ Patient e1 y ∧ Agent e2 x ∧ Patient e2 z"
  (* Hypothesis: Patient may benefit from treatment with Neratinib or Lapatinib or may able to access a clinical trial for treatment of ERBB2 V777L *)
  shows "∃x y z e1 e2. (Patient e1 x ∧ Treatment y ∧ (Neratinib y ∨ Lapatinib y) ∧ ClinicalTrial z ∧ ERBB2V777L z ∧ (Benefit e1 ∧ Agent e1 x ∧ Patient e1 y)) ∨ (Access e2 ∧ Agent e2 x ∧ Patient e2 z)"
  using explanation_4 by blast
  

end
