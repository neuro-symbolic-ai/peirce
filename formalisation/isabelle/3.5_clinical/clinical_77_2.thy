theory clinical_77_2
imports Main


begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  Subunit :: "event ⇒ entity ⇒ bool"
  To :: "event ⇒ entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Recruitment :: "event ⇒ bool"
  PI3K :: "entity"
  p85 :: "entity"
  PlasmaMembrane :: "entity"
  p110 :: "entity"
  Inhibition :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Binding of the p85 subunit to PI3K mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e x y. Binding e ∧ Subunit e p85 ∧ To e PI3K ∧ Mediates e ∧ Recruitment e ∧ To e PlasmaMembrane"


theorem hypothesis:
 assumes asm: "Binding e ∧ Subunit e p85 ∧ Subunit e p110 ∧ Inhibition e p110"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e x y z. Binding e ∧ Subunit e p85 ∧ Subunit e p110 ∧ Inhibition e p110 ∧ Relieves e ∧ Mediates e ∧ Recruitment e ∧ To e PlasmaMembrane"
proof -
  (* From the premise, we have the information about the binding of p85 subunit, p110, and inhibition of p110. *)
  from asm have "Binding e ∧ Subunit e p85 ∧ Subunit e p110 ∧ Inhibition e p110" by meson
  (* We know from the explanation that Binding of the p85 subunit to PI3K mediates the recruitment of PI3K to the plasma membrane. *)
  (* There is a logical relation Implies(A, B), Implies(Binding of the p85 subunit to PI3K, Recruitment of PI3K to the plasma membrane) *)
  (* We have Binding of the p85 subunit, so we can infer Recruitment of PI3K to the plasma membrane. *)
  then have "Binding e ∧ Subunit e p85 ∧ Subunit e p110 ∧ Inhibition e p110 ∧ Mediates e ∧ Recruitment e ∧ To e PlasmaMembrane" sledgehammer
  then show ?thesis <ATP>
qed

end
