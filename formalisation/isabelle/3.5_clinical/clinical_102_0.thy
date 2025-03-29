theory clinical_102_0
imports Main


begin

typedecl entity
typedecl event

consts
  Bind :: "event ⇒ bool"
  Drug :: "event ⇒ entity ⇒ bool"
  To :: "event ⇒ entity ⇒ bool"
  HER2KinaseDomain :: "entity ⇒ entity"
  EfficacyAgainst :: "event ⇒ bool"
  TumorsWithMutation :: "event ⇒ entity ⇒ bool"
  Lapatinib :: "entity"
  Neratinib :: "entity"
  
(* Explanation 1: Lapatinib and neratinib bind to the HER2 kinase domain and are therefore expected to have efficacy against tumors with these mutations in the kinase domain. *)
axiomatization where
  explanation_1: "∀x y e. (Bind e ∧ Drug e Lapatinib ∧ To e (HER2KinaseDomain x)) ∨ (Bind e ∧ Drug e Neratinib ∧ To e (HER2KinaseDomain y)) ∧ EfficacyAgainst e ∧ TumorsWithMutation e x"

consts
  Inhibitor :: "entity ⇒ bool"
  Irreversible :: "entity ⇒ bool"
  TargetedTo :: "entity ⇒ entity ⇒ bool"
  OvercomeResistance :: "event ⇒ bool"
  EffectiveIn :: "event ⇒ entity ⇒ bool"
  BreastCancerPatients :: "entity"
  
(* Explanation 2: An irreversible inhibitor that is targeted to the HER2 kinase domain may overcome treatment resistance and be effective in breast cancer patients. *)
axiomatization where
  explanation_2: "∃x y e. Inhibitor x ∧ Irreversible x ∧ TargetedTo x (HER2KinaseDomain y) ∧ OvercomeResistance e ∧ EffectiveIn e BreastCancerPatients"

consts
  ERBB2V777L :: "entity ⇒ bool"
  ClinicalTrial :: "entity ⇒ entity"
  BreastCarcinoma :: "entity ⇒ bool"
  Open :: "entity ⇒ bool"
  Closed :: "entity ⇒ bool"
  NumberOfTrials :: "entity ⇒ nat"
  
(* Explanation 3: ERBB2 V777L is an inclusion criterion in 4 clinical trials for breast carcinoma, of which 4 are open and 0 are closed. *)
axiomatization where
  explanation_3: "∃x. ERBB2V777L x ∧ InclusionCriterionIn x (ClinicalTrial y) ∧ BreastCarcinoma y ∧ Open y ∧ ¬Closed y ∧ NumberOfTrials x (4::nat)"

consts
  Trial :: "entity ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"
  InclusionCriteria :: "entity ⇒ entity"
  Phase1Phase2 :: "entity ⇒ bool"
  Phase2 :: "entity ⇒ bool"
  
(* Explanation 4: Of the trials that contain ERBB2 V777L and breast carcinoma as inclusion criteria, 1 is phase 1/phase 2 (1 open) and 3 are phase 2 (3 open). *)
axiomatization where
  explanation_4: "∃x y z. Trial x ∧ Contains x ERBB2V777L ∧ Contains x BreastCarcinoma ∧ InclusionCriteria x y ∧ (Phase1Phase2 y ∧ Open y ∧ NumberOfTrials y (1::nat)) ∨ (Phase2 z ∧ Open z ∧ NumberOfTrials z (3::nat))"


theorem hypothesis:
 assumes asm: "Patient x"
  (* Hypothesis: Patients may benefit from treatment with Neratinib or Lapatinib or may be able to access a clinical trial for the treatment of ERBB2 V777L. *)
 shows "∃x e. Patient x ∧ (BenefitFrom e ∧ Treatment e Neratinib) ∨ (BenefitFrom e ∧ Treatment e Lapatinib) ∨ (Access e ∧ ClinicalTrial e ∧ ForTreatmentOf e ERBB2V777L)"
proof -
  (* From the premise, we know the patient x. *)
  from asm have "Patient x" <ATP>
  (* We have the following implications from the explanations and logical relations:
     - Implies(A and B, C): Lapatinib and neratinib bind to the HER2 kinase domain implies an irreversible inhibitor targeted to the HER2 kinase domain.
     - Implies(C, D and E): An irreversible inhibitor targeted to the HER2 kinase domain implies effective in breast cancer patients.
     - Implies(F, J): ERBB2 V777L is an inclusion criterion in clinical trials for breast carcinoma implies trials containing ERBB2 V777L and breast carcinoma as inclusion criteria.
     - Implies(G, N): 4 clinical trials for breast carcinoma implies 3 open phase 2 trials.
     - Implies(J, N): Trials containing ERBB2 V777L and breast carcinoma as inclusion criteria implies 3 open phase 2 trials.
     - Implies(N, M): 3 open phase 2 trials implies 3 phase 2 trials.
  *)
  (* We can use these implications to infer the necessary conditions for the hypothesis. *)
  have "EffectiveIn e BreastCancerPatients" if "An irreversible x ∧ TargetedTo x (HER2KinaseDomain y) ∧ OvercomeResistance e" for x y e <ATP>
  have "BenefitFrom e ∧ Treatment e Neratinib" if "(Bind e ∧ Drug e Neratinib ∧ To e (HER2KinaseDomain y)) ∧ EfficacyAgainst e ∧ TumorsWithMutation e x" for x y e <ATP>
  have "BenefitFrom e ∧ Treatment e Lapatinib" if "(Bind e ∧ Drug e Lapatinib ∧ To e (HER2KinaseDomain y)) ∧ EfficacyAgainst e ∧ TumorsWithMutation e x" for x y e <ATP>
  have "Access e ∧ ClinicalTrial e ∧ ForTreatmentOf e ERBB2V777L" if "ERBB2V777L x ∧ InclusionCriterionIn x (ClinicalTrial y) ∧ BreastCarcinoma y ∧ Open y ∧ ¬Closed y ∧ NumberOfTrials x 4" for x y <ATP>
  then show ?thesis by auto
qed

end
