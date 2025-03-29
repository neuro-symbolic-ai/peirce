theory clinical_74_3
imports Main


begin

typedecl entity
typedecl event

consts
  Conversion :: "event ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Provides :: "event ⇒ entity ⇒ entity ⇒ bool"
  ProvidesDockingSite :: "event ⇒ entity ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Recruitment :: "event ⇒ entity ⇒ entity ⇒ bool"
  PDK1 :: "entity"
  AKT :: "entity"
  PI3K :: "entity"
  PlasmaMembrane :: "entity"

(* Explanation 1: Specify that the conversion of PIP2 to PIP3 provides a docking site for PDK1 and AKT in addition to mediating the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∀e x y z. Conversion e ∧ PIP2 x ∧ PIP3 y ∧ Provides e x y ∧ ProvidesDockingSite e PDK1 AKT ∧ Mediates e ∧ Recruitment e PI3K PlasmaMembrane"


theorem hypothesis:
 assumes asm: "Conversion e ∧ PIP2 x ∧ PIP3 y ∧ Provides e x y ∧ Mediates e ∧ Recruitment e PI3K PlasmaMembrane"
  (* Hypothesis: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT *)
 shows "∃e x y z. Conversion e ∧ PIP2 x ∧ PIP3 y ∧ Provides e x y ∧ Mediates e ∧ Recruitment e PI3K PlasmaMembrane ∧ ProvidesDockingSite e PDK1 AKT"
  by (simp add: explanation_1)
  

end
