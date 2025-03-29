theory clinical_77_4
imports Main


begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Recruitment :: "entity ⇒ entity ⇒ bool"
  PI3K :: "entity"
  PlasmaMembrane :: "entity"

(* Explanation 1: Binding of the p85 subunit and p110 together mediates the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e x y. Binding e ∧ P85Subunit x ∧ P110 y ∧ Mediates e ∧ Agent e x ∧ Patient e y ∧ Recruitment PI3K PlasmaMembrane"


theorem hypothesis:
 assumes asm: "Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e x y z. Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Relieves e ∧ Agent e x ∧ Patient e y ∧ Mediates e ∧ Agent e x ∧ Patient e z ∧ Recruitment PI3K PlasmaMembrane"
proof -
  (* From the premise, we have information about binding, p85 subunit, p110, and inhibition. *)
  from asm have "Binding e ∧ P85Subunit x ∧ P110 y" by blast
  (* There is a logical relation Implies(A, B), Implies(Binding of the p85 subunit and p110 together, Mediates the recruitment of PI3K to the plasma membrane) *)
  (* We can infer that binding mediates the recruitment of PI3K to the plasma membrane. *)
  then have "Mediates e" sledgehammer
  (* Since the hypothesis states that binding relieves inhibition of p110, we can add this information. *)
  then have "Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Relieves e" <ATP>
  (* We can also include the agent and patient information. *)
  then have "Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Relieves e ∧ Agent e x ∧ Patient e y" <ATP>
  (* Additionally, we know that binding mediates and recruits PI3K to the plasma membrane. *)
  then have "Binding e ∧ P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Relieves e ∧ Agent e x ∧ Patient e y ∧ Mediates e ∧ Agent e x ∧ Patient e z ∧ Recruitment PI3K PlasmaMembrane" <ATP>
  then show ?thesis <ATP>
qed

end
