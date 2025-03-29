theory clinical_89_2
imports Main


begin

typedecl entity
typedecl event

consts
  USFDA :: "entity ⇒ bool"
  Approved :: "entity ⇒ bool"
  Olaparib :: "entity ⇒ bool"
  Talazoparib :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  BRCA_mutated :: "entity ⇒ bool"
  HER_2_negative :: "entity ⇒ bool"
  Advanced :: "entity ⇒ bool"
  Metastatic :: "entity ⇒ bool"
  BC :: "entity ⇒ bool"
  PARPInhibitor :: "entity ⇒ bool"
  Licensed :: "entity ⇒ bool"
  Tumour :: "entity ⇒ bool"
  SpecificDefects :: "entity ⇒ bool"
  DNARepair :: "entity ⇒ bool"

(* Explanation 1: US Food and Drug Administration approved olaparib and talazoparib for the treatment of patients with BRCA-mutated, HER-2-negative advanced or metastatic BC *)
axiomatization where
  explanation_1: "∃x y z. USFDA x ∧ Approved y ∧ Olaparib y ∧ Talazoparib y ∧ Patient z ∧ BRCA_mutated z ∧ HER_2_negative z ∧ (Advanced z ∨ Metastatic z) ∧ BC z"

(* Explanation 2: Olaparib and talazoparib are licensed PARP inhibitors, which target tumour specific defects in DNA repair *)
axiomatization where
  explanation_2: "∀x. (Olaparib x ∧ Talazoparib x) ⟶ (PARPInhibitor x ∧ Licensed x ∧ (∃y. Tumour y ∧ SpecificDefects y ∧ DNARepair y))"

theorem hypothesis:
 assumes asm: "Olaparib x ∧ Talazoparib x"
  (* Hypothesis: Olaparib and talazoparib are licensed PARP inhibitors for the treatment of patients with BRCA-mutated, HER-2-negative advanced or metastatic BC *)
 shows "PARPInhibitor x ∧ Licensed x ∧ ∃y. Patient y ∧ BRCA_mutated y ∧ HER_2_negative y ∧ (Advanced y ∨ Metastatic y) ∧ BC y"
  sledgehammer
  oops

end
