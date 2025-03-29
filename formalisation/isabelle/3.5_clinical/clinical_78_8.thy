theory clinical_78_8
imports Main


begin

typedecl entity
typedecl event

consts
  Relief :: "event ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  CausedDirectly :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  BindingEvent :: "event ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  By :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The relief of the inhibitory effect on p is directly caused by the binding event of the catalytic subunit by the regulatory subunit *)
axiomatization where
  explanation_1: "∃e1 e2 x y z. Relief e1 ∧ InhibitoryEffect z ∧ On z p ∧ CausedDirectly e2 ∧ Agent e2 x ∧ Patient e2 z ∧ BindingEvent e1 ∧ CatalyticSubunit y ∧ RegulatorySubunit x ∧ By y x"


theorem hypothesis:
 assumes asm: "CatalyticSubunit p110 ∧ RegulatorySubunit p85"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. BindingEvent e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Relief e ∧ Agent e x ∧ Patient e z ∧ On z p110 ∧ By x y"
proof -
  (* From the premise, we have the information about the catalytic subunit p110 and the regulatory subunit p85. *)
  from asm have "CatalyticSubunit p110 ∧ RegulatorySubunit p85" by simp
  (* Given the explanatory sentence, we know that the relief of the inhibitory effect on p is directly caused by the binding event of the catalytic subunit by the regulatory subunit. *)
  (* This implies that the binding event is related to the relief of the inhibitory effect. *)
  (* We can infer the necessary components for the hypothesis from this relation. *)
  obtain e x y z where "BindingEvent e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ InhibitoryEffect z ∧ Relief e ∧ Agent e x ∧ Patient e z ∧ On z p110 ∧ By x y"
    sledgehammer
  then show ?thesis <ATP>
qed

end
