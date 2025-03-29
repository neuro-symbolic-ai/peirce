theory clinical_76_9
imports Main


begin

typedecl entity
typedecl event

consts
  CatalysisOfP110Subunit :: "entity ⇒ bool"
  Results :: "event ⇒ bool"
  Conversion :: "event ⇒ entity ⇒ entity ⇒ bool"
  P110SubunitOfPIK3 :: "entity ⇒ bool"
  PIP2 :: "entity ⇒ bool"
  PIP3 :: "entity ⇒ bool"
  Mediates :: "event ⇒ bool"
  RecruitmentOfPI3K :: "event ⇒ bool"
  ToPlasmaMembrane :: "entity ⇒ bool"

(* Explanation 1: The catalysis of the p110 subunit directly results in the conversion of PIP2 to PIP *)
axiomatization where
  explanation_1: "∃e x y. CatalysisOfP110Subunit x ∧ Results e ∧ Conversion e PIP2 PIP"


theorem hypothesis:
 assumes asm: "P110SubunitOfPIK3 x"
 (* Hypothesis: The p110 subunit of PIK3 catalyses the conversion of PIP2 to PIP3 and mediates recruitment of PI3K to plasma membrane *)
 shows "∃e x y z. P110SubunitOfPIK3 x ∧ CatalysisOfP110Subunit x ∧ Conversion e y z ∧ PIP2 y ∧ PIP3 z ∧ Mediates e ∧ RecruitmentOfPI3K e ∧ ToPlasmaMembrane z"
proof -
  (* From the premise, we know that the p110 subunit of PIK3 is related to x. *)
  from asm have "P110SubunitOfPIK3 x" <ATP>
  (* There is an explanatory sentence stating the relation between the catalysis of the p110 subunit and the conversion of PIP2 to PIP. *)
  (* We have a logical relation Implies(A, B), Implies(catalysis of the p110 subunit, conversion of PIP2 to PIP) *)
  (* We can infer the conversion of PIP2 to PIP from the catalysis of the p110 subunit. *)
  then have "∃e y z. CatalysisOfP110Subunit x ∧ Results e ∧ Conversion e PIP2 PIP" <ATP>
  (* We can further infer the relation between PIP3, Mediates, RecruitmentOfPI3K, and ToPlasmaMembrane. *)
  then have "∃e x y z. P110SubunitOfPIK3 x ∧ CatalysisOfP110Subunit x ∧ Conversion e y z ∧ PIP2 y ∧ PIP3 z ∧ Mediates e ∧ RecruitmentOfPI3K e ∧ ToPlasmaMembrane z" <ATP>
  then show ?thesis <ATP>
qed

end
