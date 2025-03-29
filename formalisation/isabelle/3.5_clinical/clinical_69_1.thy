theory clinical_69_1
imports Main


begin

typedecl entity
typedecl event

consts
  PhosphorylationOfAktAtS473 :: "entity ⇒ bool"
  CarboxyTerminalHydrophobicMotif :: "entity ⇒ bool"
  Stimulates :: "event ⇒ bool"
  FullAktActivity :: "entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Cause :: "event ⇒ entity ⇒ bool"
  By :: "entity ⇒ entity ⇒ bool"
  mTOR :: "entity"
  DNA_PK :: "entity"
  PKBAkt :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  DockingSiteOnPIK3 :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  At :: "entity ⇒ entity ⇒ bool"
  LeadTo :: "event ⇒ bool"
  PartialPKBAktActivation :: "entity ⇒ bool"

(* Explanation 1: Phosphorylation of Akt at S473 in the carboxy-terminal hydrophobic motif, either by mTOR or by DNA-PK stimulates full Akt activity. *)
axiomatization where
  explanation_1: "∃e x y z. PhosphorylationOfAktAtS473 x ∧ CarboxyTerminalHydrophobicMotif y ∧ Stimulates e ∧ FullAktActivity z ∧ Patient e z ∧ Cause e x ∧ (By x mTOR ∨ By x DNA_PK)"

(* Explanation 2: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃e x y z. PKBAkt x ∧ Binds e ∧ DockingSiteOnPIK3 y ∧ PlasmaMembrane z ∧ At y z ∧ LeadTo e ∧ PartialPKBAktActivation x"


theorem hypothesis:
 assumes asm: "PhosphorylationOfAktAtS473 x ∧ CarboxyTerminalHydrophobicMotif y ∧ FullAktActivity z"
  (* Hypothesis: Phosphorylation of bound Akt stimulates full activity of Akt. *)
 shows "∃e x y. PhosphorylationOfAktAtS473 x ∧ Stimulates e ∧ FullAktActivity y ∧ Patient e y ∧ Cause e x"
  using explanation_1 by blast
  

end
