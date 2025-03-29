theory clinical_78_10
imports Main


begin

typedecl entity
typedecl event

consts
  Relief :: "event ⇒ bool"
  InhibitoryEffect :: "entity ⇒ bool"
  OnP :: "entity ⇒ bool"
  CausedBy :: "event ⇒ bool"
  Binding :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  LeadsTo :: "event ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"

(* Explanation 1: The relief of the inhibitory effect on p is directly caused by the binding event of the catalytic subunit by the regulatory subunit *)
axiomatization where
  explanation_1: "∃e x y. Relief e ∧ InhibitoryEffect x ∧ OnP y ∧ CausedBy e ∧ Binding e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: The relief of the inhibitory effect on p is directly caused by the binding event of the catalytic subunit by the regulatory subunit implies that the binding event leads to the relief of the inhibitory effect on p *)
axiomatization where
  explanation_2: "∀e x y. Relief e ∧ InhibitoryEffect x ∧ OnP y ∧ CausedBy e ∧ Binding e ∧ Agent e x ∧ Patient e y ⟶ LeadsTo e ∧ Relief e ∧ InhibitoryEffect x ∧ OnP y"

theorem hypothesis:
 assumes asm: "CatalyticSubunit p110 ∧ RegulatorySubunit p85"
  (* Hypothesis: The binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
 shows "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ PI3K z ∧ Agent e x ∧ Patient e y ∧ DirectObject e z ∧ Relieves e x"
proof -
  (* From the premise, we know that the catalytic subunit p110 and the regulatory subunit p85 are involved. *)
  from asm have "CatalyticSubunit p110 ∧ RegulatorySubunit p85" by blast
  (* We have the logical proposition Implies(B, A), which states that the binding event of the catalytic subunit by the regulatory subunit leads to the relief of the inhibitory effect on p. *)
  (* Both A and B are from explanatory sentence 1 and 2. *)
  (* We can infer that the binding event relieves the inhibitory effect on p. *)
  then have "∃e x y. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ Agent e x ∧ Patient e y ∧ LeadsTo e ∧ Relief e ∧ InhibitoryEffect x ∧ OnP y" sledgehammer
  (* Since p110 is the catalytic subunit, we can infer that it is the direct object in the event. *)
  then have "∃e x y z. Binding e ∧ CatalyticSubunit x ∧ RegulatorySubunit y ∧ PI3K z ∧ Agent e x ∧ Patient e y ∧ LeadsTo e ∧ Relief e ∧ InhibitoryEffect x ∧ OnP y ∧ DirectObject e z ∧ Relieves e x" <ATP>
  then show ?thesis <ATP>
qed

end
