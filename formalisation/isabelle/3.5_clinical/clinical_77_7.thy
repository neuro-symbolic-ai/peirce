theory clinical_77_7
imports Main


begin

typedecl entity
typedecl event

consts
  Entity :: "entity ⇒ bool"
  Related :: "entity ⇒ entity ⇒ bool"
  PlasmaMembrane :: "entity"
  Binding :: "event ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  InhibitionOf :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  RecruitmentOf :: "event ⇒ entity ⇒ bool"
  To :: "event ⇒ entity ⇒ entity ⇒ bool"
  PI3K :: "entity"

(* Explanation 1: The entity z is related to the plasma membrane *)
axiomatization where
  explanation_1: "∀z. Entity z ⟶ Related z PlasmaMembrane"


theorem hypothesis:
 assumes asm: "Entity z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e x y z. Binding e ∧ P85Subunit x ∧ P110 y ∧ InhibitionOf e y ∧ Mediates e ∧ RecruitmentOf e PI3K ∧ To e PlasmaMembrane"
  sledgehammer
  oops

end
