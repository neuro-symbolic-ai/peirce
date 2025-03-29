theory clinical_89_0
imports Main

begin

typedecl entity
typedecl event

consts
  USFDA :: "entity ⇒ bool"
  Olaparib :: "entity ⇒ bool"
  Talazoparib :: "entity ⇒ bool"
  Approve :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  TreatmentPurpose :: "entity ⇒ bool"
  LicensedPARPInhibitor :: "entity ⇒ bool"
  TumourDefects :: "entity ⇒ bool"
  Target :: "event ⇒ bool"

(* Explanation 1: US Food and Drug Administration approved olaparib and talazoparib for the treatment of patients with BRCA-mutated, HER-2-negative advanced or metastatic BC. *)
axiomatization where
  explanation_1: "∃x y e. USFDA x ∧ (Olaparib y ∨ Talazoparib y) ∧ Approve e ∧ Agent e x ∧ Patient e y ∧ TreatmentPurpose y"

(* Explanation 2: Olaparib and talazoparib are licensed PARP inhibitors, which target tumour specific defects in DNA repair. *)
axiomatization where
  explanation_2: "∀x y e. (Olaparib x ∨ Talazoparib x) ⟶ (LicensedPARPInhibitor x ∧ TumourDefects y ∧ Target e ∧ Agent e x ∧ Patient e y)"

theorem hypothesis:
  assumes asm: "Olaparib x ∨ Talazoparib x"
  (* Hypothesis: Olaparib and talazoparib are licensed PARP inhibitors for the treatment of patients with BRCA-mutated, HER-2-negative advanced or metastatic BC. *)
  shows "∀x. (Olaparib x ∨ Talazoparib x) ⟶ LicensedPARPInhibitor x"
  using explanation_2 by blast
  

end
