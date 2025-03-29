theory clinical_77_10
imports Main


begin

typedecl entity
typedecl event

consts
  ReliefOfInhibition :: "event ⇒ bool"
  Causes :: "event ⇒ bool"
  RecruitmentOf :: "entity ⇒ entity ⇒ bool"
  To :: "event ⇒ entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  PlasmaMembrane :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  P85Subunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  Leads :: "event ⇒ bool"
  ReliefOfInhibitionOf :: "entity ⇒ bool"
  MediatedBy :: "event ⇒ entity ⇒ bool"
  SpecificEvent :: "event ⇒ bool"

(* Explanation 1: The relief of inhibition of p110 directly causes the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e x y. ReliefOfInhibition e ∧ Causes e ∧ RecruitmentOf y PI3K ∧ To e PlasmaMembrane"

(* Explanation 2: The binding of the p85 subunit to p110 leads to the relief of inhibition of p110 *)
axiomatization where
  explanation_2: "∃e x y. Binding e ∧ P85Subunit x ∧ P110 y ∧ Leads e ∧ To e (ReliefOfInhibitionOf y)"

(* Explanation 3: The relief of inhibition of p110 is mediated by a specific event *)
axiomatization where
  explanation_3: "∃e. ReliefOfInhibition e ∧ MediatedBy e SpecificEvent"


theorem hypothesis:
 assumes asm: "Binding e1 ∧ P85Subunit x ∧ P110 y"
  (* Hypothesis: The binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e1 e2 x y z. Binding e1 ∧ P85Subunit x ∧ P110 y ∧ ReliefOfInhibition e1 ∧ MediatedBy e2 x ∧ RecruitmentOf x PI3K ∧ To x PlasmaMembrane"
proof -
  (* From the premise, we have the information about the binding of the p85 subunit and p110. *)
  from asm have "Binding e1 ∧ P85Subunit x ∧ P110 y" <ATP>
  (* There is a logical relation Implies(C, A), Implies(binding of the p85 subunit to p110, relief of inhibition of p110) *)
  (* We can use the explanatory sentence 2 to infer the relief of inhibition of p110. *)
  obtain e1' where e1': "Binding e1' ∧ P85Subunit x ∧ P110 y ∧ Leads e1' ∧ To e1' (ReliefOfInhibitionOf y)"
    <ATP>
  then have "ReliefOfInhibition e1'" by auto
  (* There is a logical relation Implies(A, B), Implies(relief of inhibition of p110, recruitment of PI3K to the plasma membrane) *)
  (* We can use the explanatory sentence 1 to infer the recruitment of PI3K to the plasma membrane. *)
  obtain e2 x' y' where e2: "ReliefOfInhibition e1' ∧ Causes e2 ∧ RecruitmentOf y' PI3K ∧ To e2 PlasmaMembrane"
    <ATP>
  then have "RecruitmentOf x' PI3K ∧ To x' PlasmaMembrane" for x'
    <ATP>
  (* There is a logical relation Implies(C, B), Implies(binding of the p85 subunit to p110, recruitment of PI3K to the plasma membrane) *)
  (* We have binding of the p85 subunit to p110, which implies recruitment of PI3K to the plasma membrane. *)
  then have "Binding e1 ∧ P85Subunit x ∧ P110 y ∧ ReliefOfInhibition e1' ∧ RecruitmentOf x' PI3K ∧ To x' PlasmaMembrane"
    <ATP>
  then show ?thesis <ATP>
qed

end
