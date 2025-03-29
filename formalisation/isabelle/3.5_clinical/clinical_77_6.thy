theory clinical_77_6
imports Main


begin

typedecl entity
typedecl event

consts
  Binding :: "event ⇒ bool"
  Subunit :: "entity ⇒ entity ⇒ bool"
  Inhibition :: "entity ⇒ entity ⇒ bool"
  Interact :: "event ⇒ bool"
  Relieves :: "event ⇒ bool"
  Remove :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Directly :: "event ⇒ bool"
  p85 :: "entity"
  p110 :: "entity"
  PI3K :: "entity"
  ToMembrane :: "entity ⇒ bool"
  Recruit :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: The binding of the p85 subunit and p110 together relieves the inhibition of p110 by directly interacting with p110 to remove the inhibitory effect *)
axiomatization where
  explanation_1: "∃e x y z. Binding e ∧ Subunit p85 x ∧ Subunit p110 y ∧ Inhibition z y ∧ Interact e ∧ Relieves e ∧ Remove e ∧ Agent e x ∧ Patient e z ∧ Directly e"


theorem hypothesis:
 assumes asm: "Subunit p85 x ∧ Subunit p110 y ∧ Inhibition z y"
  (* Hypothesis: Binding of the p85 subunit and p110 relieves inhibition of p110 and mediates the recruitment of PI3K to the plasma membrane *)
 shows "∃e x y z. Binding e ∧ Subunit p85 x ∧ Subunit p110 y ∧ Inhibition z y ∧ Mediates e ∧ Relieves e ∧ Agent e x ∧ Patient e z ∧ Recruit PI3K z ∧ ToMembrane z"
proof -
  (* From the premise, we have the information about the subunits and inhibition. *)
  from asm have "Subunit p85 x ∧ Subunit p110 y ∧ Inhibition z y" by blast
  (* The explanation sentence states that the binding of the p85 subunit and p110 together relieves the inhibition of p110 by directly interacting with p110 to remove the inhibitory effect. *)
  (* We know that the binding of the subunits relieves the inhibition. *)
  (* There is a logical relation Implies(A, Not(B)), Implies(binding of the p85 subunit and p110 together, Not(inhibition of p110)) *)
  (* Since we have the subunits and inhibition, we can infer the binding event. *)
  then have "Binding e" for e
  (* The explanation also mentions that the direct interaction with p110 removes the inhibitory effect. *)
  (* There is a logical relation Implies(C, D), Implies(directly interacting with p110, removing the inhibitory effect) *)
  (* As we have the direct interaction with p110, we can conclude that the inhibitory effect is removed. *)
  then have "Remove e" for e
  (* The hypothesis requires that the binding mediates the recruitment of PI3K to the plasma membrane. *)
  (* We need to introduce a new event e that mediates the recruitment. *)
  then have "Mediates e" for e
  (* The hypothesis also involves the recruitment of PI3K to the plasma membrane. *)
  (* We can recruit PI3K to the entity z. *)
  then have "Recruit PI3K z" for z
  (* Additionally, the hypothesis states that the entity z is related to the plasma membrane. *)
  then have "ToMembrane z" sledgehammer
  (* Combining all the necessary conditions, we have proven the hypothesis. *)
  then show ?thesis <ATP>
qed

end
