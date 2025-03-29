theory clinical_78_4
imports Main

begin

typedecl entity
typedecl event

consts
  RegulatorySubunit :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Within :: "event ⇒ entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Relieves :: "event ⇒ bool"
  Effect :: "entity ⇒ bool"
  Inhibitory :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  Heterodimer :: "entity ⇒ bool"
  ConsistingOf :: "entity ⇒ entity ⇒ entity ⇒ bool"

(* Explanation 1: The regulatory subunit (p85) binds to the catalytic subunit (p110) within the PI3K complex, and this binding directly relieves the inhibitory effect on the catalytic subunit (p110). *)
axiomatization where
  explanation_1: "∃x y z e1 e2 w. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Binding e2 ∧ Relieves e2 ∧ Effect w ∧ Inhibitory w ∧ On w y"

(* Explanation 2: PI3Ks are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit. *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ⟶ (Heterodimer x ∧ ConsistingOf x y z ∧ CatalyticSubunit y ∧ RegulatorySubunit z)"

theorem hypothesis:
  assumes asm: "RegulatorySubunit z ∧ CatalyticSubunit x ∧ PI3K y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110. *)
  shows "∃x y z e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x"
proof -
  (* From the premise, we have known information about the regulatory subunit, catalytic subunit, and PI3K. *)
  from asm have "RegulatorySubunit z ∧ CatalyticSubunit x ∧ PI3K y" by simp
  (* Explanation 1 provides a direct relation between binding and relieving the inhibitory effect. *)
  (* We can use the logical relation Implies(A, B), which states that if the regulatory subunit binds to the catalytic subunit, the inhibitory effect is relieved. *)
  (* Explanation 1 also provides the existence of such a binding event. *)
  from explanation_1 obtain e1 e2 w where
    "Binds e1 ∧ Agent e1 z ∧ Patient e1 x ∧ Within e1 y ∧ Binding e2 ∧ Relieves e2 ∧ Effect w ∧ Inhibitory w ∧ On w x" sledgehammer
  (* We can now conclude that there exists a binding event that relieves the inhibitory effect on the catalytic subunit. *)
  then have "∃x y z e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x" <ATP>
  then show ?thesis <ATP>
qed

end
