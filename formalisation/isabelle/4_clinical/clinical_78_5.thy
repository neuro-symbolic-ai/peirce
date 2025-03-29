theory clinical_78_5
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
  Causes :: "event ⇒ bool"
  Relief :: "event ⇒ bool"
  Effect :: "entity ⇒ bool"
  Inhibitory :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  Heterodimer :: "entity ⇒ bool"
  ConsistsOf :: "entity ⇒ entity ⇒ entity ⇒ bool"
  Essential :: "event ⇒ bool"
  Relieves :: "event ⇒ bool"

(* Explanation 1: The regulatory subunit (p85) binds to the catalytic subunit (p110) within the PI3K complex, and this binding directly causes the relief of the inhibitory effect on the catalytic subunit (p110). *)
axiomatization where
  explanation_1: "∃x y z e1 e2 e3 w. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Binding e2 ∧ Causes e2 ∧ Relief e3 ∧ Effect w ∧ Inhibitory w ∧ On w y"

(* Explanation 2: PI3Ks are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit, and the binding of these subunits within the complex is essential for the relief of the inhibitory effect on the catalytic subunit. *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ⟶ (Heterodimer x ∧ CatalyticSubunit y ∧ RegulatorySubunit z ∧ ConsistsOf x y z) ∧ (∃e e1 w. Binding e ∧ Within e x ∧ Essential e ∧ Relief e1 ∧ Effect w ∧ Inhibitory w ∧ On w y)"

theorem hypothesis:
  assumes asm: "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110. *)
  shows "∃x y e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x"
proof -
  (* From the premise, we have known information about the catalytic subunit, PI3K, and regulatory subunit. *)
  from asm have "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z" by fastforce
  (* Explanation 1 provides a scenario where the regulatory subunit binds to the catalytic subunit within the PI3K complex, causing relief of the inhibitory effect. *)
  (* We have a logical relation Implies(A, B), which states that if the regulatory subunit binds to the catalytic subunit within the PI3K complex, it leads to the relief of the inhibitory effect. *)
  (* Explanation 2 supports that PI3Ks are heterodimers consisting of these subunits, and the binding is essential for relief. *)
  (* Using the logical relation Implies(A, B) and the known information, we can infer the binding and relief. *)
  then have "∃e. Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x" sledgehammer
  then show ?thesis <ATP>
qed

end
