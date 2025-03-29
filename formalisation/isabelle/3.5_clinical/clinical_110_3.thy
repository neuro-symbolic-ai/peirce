theory clinical_110_3
imports Main


begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  Known :: "entity ⇒ bool"
  Includes :: "entity ⇒ entity ⇒ bool"
  V777LHER2 :: "entity"
  Has :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: If a patient has a mutation that is known to include the V777L HER 2 mutation, then the patient has the V777L HER 2 mutation *)
axiomatization where
  explanation_1: "∀x y. Patient x ∧ Mutation y ∧ Known y ∧ Includes y V777LHER2 ∧ Has x y ⟶ Has x V777LHER2"


theorem hypothesis:
 assumes asm: "Patient x ∧ Mutation y ∧ Known y ∧ Includes y V777LHER2 ∧ Has x y"
 (* Hypothesis: Patient has a known V777L HER 2 mutation *)
 shows "∃x y. Patient x ∧ Mutation y ∧ Known y ∧ Includes y V777LHER2 ∧ Has x y"

  using assms by blast
  

end
