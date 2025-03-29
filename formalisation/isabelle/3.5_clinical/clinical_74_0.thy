theory clinical_74_0
imports Main


begin

typedecl entity
typedecl event

consts
  P110Subunit :: "entity ⇒ bool"
  PIK3 :: "entity ⇒ bool"
  Conversion :: "event ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Catalyses :: "event ⇒ entity ⇒ entity ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ entity ⇒ bool"
  Recruitment :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Provides :: "event ⇒ entity ⇒ entity ⇒ bool"
  Subsequently :: "event ⇒ bool"
  DockingSite :: "event ⇒ entity ⇒ bool"
  PleckstrinHomologyDomainContainingProteins :: "entity ⇒ bool"
  PDK1 :: "entity"
  AKT :: "entity"

(* Explanation 1: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
axiomatization where
  explanation_1: "∃e x y z. P110Subunit x ∧ PIK3 x ∧ Conversion e ∧ PIP2 y ∧ PIP3 z ∧ Catalyses e x y z ∧ Mediates e z ∧ Recruitment z ∧ PI3K z ∧ PlasmaMembrane z"

(* Explanation 2: PIP2 to PIP3… subsequently provides a docking site for the pleckstrin homology domain-containing proteins PDK1 and AKT *)
axiomatization where
  explanation_2: "∃e x y. PIP2 x ∧ PIP3 y ∧ Provides e x y ∧ Subsequently e ∧ DockingSite e PDK1 ∧ DockingSite e AKT ∧ PleckstrinHomologyDomainContainingProteins PDK1 ∧ PleckstrinHomologyDomainContainingProteins AKT"


theorem hypothesis:
 assumes asm: "Conversion e ∧ PIP2 x ∧ PIP3 y"
  (* Hypothesis: The conversion of PIP2 to PIP3 provides mediates recruitment of PI3K to the plasma membrane and provides a docking site for PDK1 and AKT *)
 shows "∃e x y z w. Conversion e ∧ PIP2 x ∧ PIP3 y ∧ Provides e x y ∧ Mediates e z ∧ Recruitment z ∧ PI3K z ∧ PlasmaMembrane w ∧ DockingSite e w ∧ PDK1 w ∧ AKT w"
  sledgehammer
  oops

end
