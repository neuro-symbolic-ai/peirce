theory clinical_77_0
imports Main


begin

typedecl entity
typedecl event

consts
  Bind :: "event ⇒ bool"
  Subunit :: "event ⇒ entity ⇒ bool"
  Upon :: "event ⇒ entity ⇒ bool"
  MediatingRecruitment :: "event ⇒ bool"
  To :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  RelievesInhibitoryEffect :: "event ⇒ bool"
  On :: "event ⇒ entity ⇒ bool"
  GrowthFactorStimulation :: "entity"
  PI3K :: "entity"
  PlasmaMembrane :: "entity"
  p85 :: "entity"
  p110 :: "entity"

(* Explanation 1: Upon growth factor stimulation p85 binds… and mediating the recruitment of PI3K to the plasma membrane *)
axiomatization where
  explanation_1: "∃e. Bind e ∧ Subunit e p85 ∧ Upon e GrowthFactorStimulation ∧ MediatingRecruitment e ∧ To e PlasmaMembrane ∧ Patient e PI3K"

(* Explanation 2: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
axiomatization where
  explanation_2: "∃e. Bind e ∧ Subunit e p110 ∧ Subunit e p85 ∧ RelievesInhibitoryEffect e ∧ On e p110"


theorem hypothesis:
 assumes asm: "Upon e GrowthFactorStimulation"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e. Bind e ∧ Subunit e p85 ∧ Subunit e p110 ∧ RelievesInhibition e ∧ MediatesRecruitment e ∧ To e PlasmaMembrane ∧ Agent e p85 ∧ Agent e p110 ∧ Patient e PI3K"
proof -
  (* From the premise, we know that upon growth factor stimulation, p85 binds and mediates the recruitment of PI3K to the plasma membrane. *)
  from asm obtain e where "Bind e ∧ Subunit e p85 ∧ Upon e GrowthFactorStimulation ∧ MediatingRecruitment e ∧ To e PlasmaMembrane ∧ Patient e PI3K" using explanation_1 by blast
  (* We have the explanatory sentence 1 stating the relationship between p85, PI3K, and the plasma membrane. *)
  (* There is a logical relation Implies(A, B and C), Implies(growth factor stimulation, mediating the recruitment of PI3K to the plasma membrane) *)
  (* We can infer the mediating recruitment of PI3K to the plasma membrane. *)
  then have "MediatesRecruitment e" sledgehammer
  (* We also have the explanatory sentence 2 stating the relationship between p85, p110, and the inhibitory effect. *)
  (* There is a logical relation Implies(D, E), Implies(binding of p110 by p85, relieving the inhibitory effect on p110) *)
  (* We can infer the relieving of the inhibitory effect on p110. *)
  then have "RelievesInhibition e" <ATP>
  (* Combining the above inferences, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
