theory clinical_78_8
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
  Effect :: "event ⇒ bool"
  Inhibitory :: "event ⇒ bool"
  On :: "event ⇒ entity ⇒ bool"
  Heterodimer :: "entity ⇒ bool"
  ConsistsOf :: "entity ⇒ entity ⇒ bool"
  Essential :: "event ⇒ bool"
  Relieves :: "event ⇒ bool"

(* Explanation 1: The regulatory subunit (p85) binds to the catalytic subunit (p110) within the PI3K complex, and this binding directly causes the relief of the inhibitory effect on the catalytic subunit (p110) by the regulatory subunit (p85) *)
axiomatization where
  explanation_1: "∃x y z e1 e2 e3. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Binding e2 ∧ Causes e2 ∧ Relief e3 ∧ Effect e3 ∧ Inhibitory e3 ∧ On e3 y ∧ Agent e3 x"

(* Explanation 2: PI3Ks are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ⟶ (Heterodimer x ∧ ConsistsOf x y ∧ CatalyticSubunit y ∧ ConsistsOf x z ∧ RegulatorySubunit z)"

(* Explanation 3: The binding of the regulatory subunit (p85) to the catalytic subunit (p110) within the PI3K complex is essential because it directly causes the relief of the inhibitory effect on the catalytic subunit (p110) *)
axiomatization where
  explanation_3: "∃x y z e1 e2 e3. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Essential e1 ∧ Causes e2 ∧ Relief e3 ∧ Effect e3 ∧ Inhibitory e3 ∧ On e3 y"

theorem hypothesis:
  assumes asm: "RegulatorySubunit z ∧ CatalyticSubunit x ∧ PI3K y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
  shows "∃x y e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e1 ∧ Effect e1 ∧ Inhibitory e1 ∧ On e1 x"
proof -
  (* From the known information, we have RegulatorySubunit z, CatalyticSubunit x, and PI3K y. *)
  from asm have "RegulatorySubunit z ∧ CatalyticSubunit x ∧ PI3K y" by blast
  (* Explanation 1 provides that the binding of the regulatory subunit to the catalytic subunit within the PI3K complex causes the relief of the inhibitory effect. *)
  (* We can use the logical relation Implies(A, B) to infer the relief of the inhibitory effect. *)
  from explanation_1 have "∃e1 e2 e3. Binds e1 ∧ Agent e1 z ∧ Patient e1 x ∧ Within e1 y ∧ Binding e2 ∧ Causes e2 ∧ Relief e3 ∧ Effect e3 ∧ Inhibitory e3 ∧ On e3 x" sledgehammer
  (* From this, we can infer that there exists an event e such that the binding relieves the inhibitory effect on the catalytic subunit. *)
  then have "∃e. Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect e ∧ Inhibitory e ∧ On e x" <ATP>
  then show ?thesis <ATP>
qed

end
