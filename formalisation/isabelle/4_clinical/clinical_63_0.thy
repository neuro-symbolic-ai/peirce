theory clinical_63_0
imports Main

begin

typedecl entity
typedecl event

consts
  HRR :: "entity ⇒ bool"
  PrimaryProcess :: "entity ⇒ bool"
  Repairing :: "entity ⇒ bool"
  DNADoubleStrandBreaks :: "entity ⇒ bool"
  Damage :: "entity ⇒ bool"
  DNA :: "entity ⇒ bool"
  Repairs :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Information :: "entity ⇒ bool"
  Copied :: "event ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  HomologousUndamagedMolecule :: "entity"
  Molecules :: "entity ⇒ bool"
  Undamaged :: "entity ⇒ bool"
  Homologous :: "entity ⇒ bool"
  Provided :: "event ⇒ bool"
  SisterChromatids :: "entity ⇒ bool"
  PaternalCopies :: "entity ⇒ bool"
  MaternalCopies :: "entity ⇒ bool"
  DSBRepairProcess :: "entity ⇒ bool"
  Replaced :: "event ⇒ bool"

(* Explanation 1: HRR is the primary process for repairing DNA double strand breaks. *)
axiomatization where
  explanation_1: "∀x y. HRR x ∧ PrimaryProcess x ∧ Repairing y ∧ DNADoubleStrandBreaks y"

(* Explanation 2: HRR repairs damage to DNA using information copied from a homologous undamaged molecule. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. HRR x ∧ Damage y ∧ DNA z ∧ Repairs e1 ∧ Agent e1 x ∧ Patient e1 y ∧ To y z ∧ Information w ∧ Copied e2 ∧ Agent e2 w ∧ From w HomologousUndamagedMolecule"

(* Explanation 3: Undamaged homologous molecules are provided by sister chromatids or paternal/maternal copies of chromosomes. *)
axiomatization where
  explanation_3: "∃x y e. Molecules x ∧ Undamaged x ∧ Homologous x ∧ Provided e ∧ Patient e x ∧ Agent e y ∧ (SisterChromatids y ∨ PaternalCopies y ∨ MaternalCopies y)"

theorem hypothesis:
  assumes asm: "HRR x ∧ DSBRepairProcess x ∧ DNA y ∧ Damaged y"
  (* Hypothesis: HRR is a DSB DNA repair process wherein damaged DNA is replaced by undamaged homologous molecules from sister chromatids or paternal/maternal copies of chromosomes. *)
  shows "∀x y z e. HRR x ∧ DSBRepairProcess x ∧ DNA y ∧ Damaged y ∧ Molecules z ∧ Undamaged z ∧ Replaced e ∧ Patient e y ∧ Agent e z ∧ From z SisterChromatids ∨ From z PaternalCopies ∨ From z MaternalCopies"
  sledgehammer
  oops

end
