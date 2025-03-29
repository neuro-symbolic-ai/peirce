theory clinical_89_4
imports Main


begin

typedecl entity
typedecl event

consts
  USFoodDrugAdministration :: "entity ⇒ bool"
  Approved :: "entity ⇒ bool"
  Olaparib :: "entity ⇒ bool"
  Talazoparib :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  BRCA_mutated :: "entity ⇒ bool"
  HER_2_negative :: "entity ⇒ bool"
  AdvancedBC :: "entity ⇒ bool"
  MetastaticBC :: "entity ⇒ bool"
  Treatment :: "entity ⇒ entity ⇒ bool"
  LicensedPARPInhibitor :: "entity ⇒ bool"
  TargetDefects :: "entity ⇒ entity ⇒ entity ⇒ bool"
  TumourSpecific :: "entity ⇒ entity"
  DNARepair :: "entity ⇒ entity"

(* Explanation 1: US Food and Drug Administration approved olaparib and talazoparib for the treatment of patients with BRCA-mutated, HER-2-negative advanced or metastatic BC *)
axiomatization where
  explanation_1: "∃x y. USFoodDrugAdministration x ∧ Approved y ∧ Olaparib y ∧ Talazoparib y ∧ (∀z. Patient z ∧ BRCA_mutated z ∧ HER_2_negative z ∧ (AdvancedBC z ∨ MetastaticBC z) ⟶ Treatment y z)"

(* Explanation 2: Olaparib and talazoparib are licensed PARP inhibitors, which target tumour specific defects in DNA repair *)
axiomatization where
  explanation_2: "∀x. Olaparib x ∧ Talazoparib x ∧ LicensedPARPInhibitor x ∧ TargetDefects x (TumourSpecific x) (DNARepair x)"


theorem hypothesis:
 assumes asm: "Patient(y) ∧ BRCA_mutated(y) ∧ HER_2_negative(y) ∧ (AdvancedBC(y) ∨ MetastaticBC(y))"
  (* Hypothesis: Olaparib and talazoparib are licensed PARP inhibitors for the treatment of patients with BRCA-mutated, HER-2-negative advanced or metastatic BC *)
  shows "∃x. Olaparib(x) ∧ Talazoparib(x) ∧ LicensedPARPInhibitor(x) ∧ (∀y. Patient(y) ∧ BRCA_mutated(y) ∧ HER_2_negative(y) ∧ (AdvancedBC(y) ∨ MetastaticBC(y)) ⟶ Treatment(x, y)"
  sledgehammer
  oops

end
