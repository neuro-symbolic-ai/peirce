theory clinical_19_0
imports Main


begin

typedecl entity
typedecl event

consts
  Medicine :: "entity ⇒ bool"
  License :: "event ⇒ bool"
  ChronicMyeloidLeukaemia :: "event ⇒ bool"
  RelapsedAcuteLymphoblasticLeukaemia :: "event ⇒ bool"
  Effective :: "event ⇒ bool"
  Treat :: "event ⇒ bool"
  Patient :: "entity ⇒ bool"
  ThisPatient :: "entity"
  Access :: "event ⇒ bool"
  OffLicence :: "event ⇒ bool"

(* Explanation 1: Dasatinib is licensed for use in chronic myeloid leukaemia or relapsed acute lymphoblastic leukaemia *)
axiomatization where
  explanation_1: "∀e. Medicine Dasatinib ⟶ License e ∧ (ChronicMyeloidLeukaemia e ∨ RelapsedAcuteLymphoblasticLeukaemia e)"

(* Explanation 2: Dasatinib may be effective in treating this patient *)
axiomatization where
  explanation_2: "∃e. Effective e ∧ Treat e ∧ Medicine Dasatinib ∧ Patient ThisPatient"


theorem hypothesis:
 assumes asm: "Medicine Dasatinib"
 (* Hypothesis: Dasatinib will need to be accessed off licence *)
 shows "∃e. Access e ∧ Medicine Dasatinib ∧ OffLicence e"
proof -
  (* From the premise, we know that Dasatinib is a medicine. *)
  from asm have "Medicine Dasatinib" by simp
  (* There are two explanatory sentences related to Dasatinib. *)
  (* We have Implies(A, C) and Implies(B, C) *)
  (* We can infer that Dasatinib may be effective in treating this patient from both explanations. *)
  (* Since Dasatinib may be effective, it will need to be accessed off licence. *)
  from explanation_1 explanation_2 have "∃e. Access e ∧ Medicine Dasatinib ∧ OffLicence e" sledgehammer
  then show ?thesis <ATP>
qed

end
