theory clinical_102_0
imports Main

begin

typedecl entity
typedecl event

consts
  Lapatinib :: "entity ⇒ bool"
  Neratinib :: "entity ⇒ bool"
  HER2KinaseDomain :: "entity ⇒ bool"
  Tumours :: "entity ⇒ bool"
  Mutations :: "entity ⇒ bool"
  Bind :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Destination :: "event ⇒ entity ⇒ bool"
  Expected :: "event ⇒ bool"
  Efficacy :: "event ⇒ bool"
  Against :: "event ⇒ entity ⇒ bool"
  Inhibitor :: "entity ⇒ bool"
  Irreversible :: "entity ⇒ bool"
  Targeted :: "entity ⇒ entity ⇒ bool"
  TreatmentResistance :: "entity ⇒ bool"
  BreastCancerPatients :: "entity ⇒ bool"
  Overcome :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Effective :: "event ⇒ bool"
  In :: "event ⇒ entity ⇒ bool"
  ERBB2V777L :: "entity ⇒ bool"
  ClinicalTrials :: "entity ⇒ bool"
  BreastCarcinoma :: "entity ⇒ bool"
  InclusionCriterion :: "entity ⇒ entity ⇒ bool"
  For :: "entity ⇒ entity ⇒ bool"
  Open :: "entity ⇒ bool"
  Closed :: "entity ⇒ bool"
  Trials :: "entity ⇒ bool"
  InclusionCriteria :: "entity ⇒ entity ⇒ bool"
  Phase1or2 :: "entity ⇒ bool"
  Phase2 :: "entity ⇒ bool"
  Treatment :: "entity ⇒ bool"
  ClinicalTrial :: "entity ⇒ bool"
  Benefit :: "event ⇒ bool"
  Source :: "event ⇒ entity ⇒ bool"
  Access :: "event ⇒ bool"

(* Explanation 1: Lapatinib and neratinib bind to the HER2 kinase domain and are therefore expected to have efficacy against tumours with these mutations in the kinase domain. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2. Lapatinib x ∧ Neratinib y ∧ HER2KinaseDomain z ∧ Tumours w ∧ Mutations w ∧ Bind e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Destination e1 z ∧ Expected e2 ∧ Agent e2 x ∧ Agent e2 y ∧ Efficacy e2 ∧ Against e2 w"

(* Explanation 2: An irreversible inhibitor that is targeted to the HER2 kinase domain may overcome treatment resistance and be effective in breast cancer patients. *)
axiomatization where
  explanation_2: "∃x y z w e1 e2. Inhibitor x ∧ Irreversible x ∧ HER2KinaseDomain y ∧ Targeted x y ∧ TreatmentResistance z ∧ BreastCancerPatients w ∧ Overcome e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Effective e2 ∧ Agent e2 x ∧ In e2 w"

(* Explanation 3: ERBB2 V777L is an inclusion criterion in 4 clinical trials for breast carcinoma, of which 4 are open and 0 are closed. *)
axiomatization where
  explanation_3: "∃x y z. ERBB2V777L x ∧ ClinicalTrials y ∧ BreastCarcinoma z ∧ InclusionCriterion x y ∧ For y z ∧ Open y ∧ ¬Closed y"

(* Explanation 4: Of the trials that contain ERBB2 V777L and breast carcinoma as inclusion criteria, 1 is phase 1/phase 2 (1 open) and 3 are phase 2 (3 open). *)
axiomatization where
  explanation_4: "∃x y z. Trials x ∧ ERBB2V777L y ∧ BreastCarcinoma z ∧ InclusionCriteria x y ∧ InclusionCriteria x z ∧ Phase1or2 x ∧ Open x ∧ Phase2 x ∧ Open x"

theorem hypothesis:
  assumes asm: "Patient e x ∧ Treatment y ∧ ClinicalTrial z ∧ ERBB2V777L z"
  (* Hypothesis: Patient may benefit from treatment with Neratinib or Lapatinib or may able to access a clinical trial for treatment of ERBB2 V777L *)
  shows "∃x y z e1 e2. (∃e. Patient e x) ∧ Treatment y ∧ Neratinib y ∧ Lapatinib y ∧ ClinicalTrial z ∧ ERBB2V777L z ∧ (Benefit e1 ∧ Agent e1 x ∧ Source e1 y) ∨ (Access e2 ∧ Agent e2 x ∧ Patient e2 z)"
proof -
  (* From the premise, we have information about the patient, treatment, clinical trial, and ERBB2 V777L. *)
  from asm have "Patient e x ∧ Treatment y ∧ ClinicalTrial z ∧ ERBB2V777L z" by simp
  
  (* Explanation 1 provides that Lapatinib and Neratinib are expected to have efficacy against tumors with mutations in the kinase domain. *)
  (* This implies that they may benefit the patient. *)
  from explanation_1 have "∃x y z w e1 e2. Lapatinib x ∧ Neratinib y ∧ HER2KinaseDomain z ∧ Tumours w ∧ Mutations w ∧ Bind e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Destination e1 z ∧ Expected e2 ∧ Agent e2 x ∧ Agent e2 y ∧ Efficacy e2 ∧ Against e2 w" sledgehammer
  
  (* Explanation 3 and 4 provide that ERBB2 V777L is an inclusion criterion in open clinical trials. *)
  from explanation_3 have "∃x y z. ERBB2V777L x ∧ ClinicalTrials y ∧ BreastCarcinoma z ∧ InclusionCriterion x y ∧ For y z ∧ Open y ∧ ¬Closed y" <ATP>
  from explanation_4 have "∃x y z. Trials x ∧ ERBB2V777L y ∧ BreastCarcinoma z ∧ InclusionCriteria x y ∧ InclusionCriteria x z ∧ Phase1or2 x ∧ Open x ∧ Phase2 x ∧ Open x" <ATP>
  
  (* Using the logical relation Implies(E, F), we know that if ERBB2 V777L is an inclusion criterion, then the clinical trials are open. *)
  then have "ClinicalTrial z ∧ Open z" <ATP>
  
  (* Therefore, the patient may benefit from treatment with Neratinib or Lapatinib or may be able to access a clinical trial for treatment of ERBB2 V777L. *)
  then show "∃x y z e1 e2. (∃e. Patient e x) ∧ Treatment y ∧ Neratinib y ∧ Lapatinib y ∧ ClinicalTrial z ∧ ERBB2V777L z ∧ (Benefit e1 ∧ Agent e1 x ∧ Source e1 y) ∨ (Access e2 ∧ Agent e2 x ∧ Patient e2 z)" <ATP>
qed

end
