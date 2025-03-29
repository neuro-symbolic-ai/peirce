theory clinical_77_9
imports Main


begin

typedecl entity
typedecl event

consts
  P85Subunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  Binds :: "entity ⇒ entity ⇒ bool"
  Specifically :: "entity ⇒ bool"
  PI3KRecruitment :: "entity ⇒ bool"
  MediatedBy :: "entity ⇒ bool"
  ReliefOfInhibition :: "entity ⇒ bool"
  Cause :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The p85 subunit binds specifically to the p110 entity *)
axiomatization where
  explanation_1: "∃x y. P85Subunit x ∧ P110 y ∧ Binds x y ∧ Specifically x"

(* Explanation 2: The recruitment of PI3K is specifically mediated by the relief of inhibition of p *)
axiomatization where
  explanation_2: "∃x y z. PI3KRecruitment x ∧ MediatedBy y ∧ ReliefOfInhibition z ∧ Specifically y ∧ Cause y z"


theorem hypothesis:
 assumes asm: "P85Subunit x ∧ P110 y ∧ Inhibition z"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Mediates e1 ∧ Relieves e2 ∧ Agent e1 x ∧ Patient e1 z ∧ To e1 PlasmaMembrane ∧ Agent e2 x ∧ Patient e2 y"
proof -
  (* From the premise, we know that the p85 subunit binds specifically to the p110 entity. *)
  from asm and explanation_1 obtain xy where "P85Subunit x ∧ P110 y ∧ Binds x y ∧ Specifically x" sledgehammer
  (* From the explanation 2, we have that the recruitment of PI3K is specifically mediated by the relief of inhibition of p. *)
  from explanation_2 obtain xyz where "PI3KRecruitment x ∧ MediatedBy y ∧ ReliefOfInhibition z ∧ Specifically y ∧ Cause y z" <ATP>
  (* We can infer that the binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane. *)
  then have "∃x y z e1 e2. P85Subunit x ∧ P110 y ∧ Inhibition z ∧ Mediates e1 ∧ Relieves e2 ∧ Agent e1 x ∧ Patient e1 z ∧ To e1 PlasmaMembrane ∧ Agent e2 x ∧ Patient e2 y" <ATP>
  then show ?thesis <ATP>
qed

end
