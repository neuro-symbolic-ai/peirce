theory clinical_78_9
imports Main

begin

typedecl entity
typedecl event

consts
  RegulatorySubunit :: "entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Within :: "event ⇒ entity ⇒ bool"
  Relief :: "event ⇒ bool"
  Effect :: "entity ⇒ bool"
  Inhibitory :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  Cause :: "event ⇒ event ⇒ bool"
  Heterodimer :: "entity ⇒ bool"
  ConsistOf :: "entity ⇒ entity ⇒ bool"
  Essential :: "event ⇒ bool"
  Consequence :: "event ⇒ event ⇒ bool"
  Relieves :: "event ⇒ bool"

(* Explanation 1: The regulatory subunit (p85) binds to the catalytic subunit (p110) within the PI3K complex, and this binding directly causes the relief of the inhibitory effect on the catalytic subunit (p110) by the regulatory subunit (p85) *)
axiomatization where
  explanation_1: "∃x y z e1 e2. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Relief e2 ∧ Effect w ∧ Inhibitory w ∧ On w y ∧ Agent e2 x ∧ Cause e1 e2"

(* Explanation 2: PI3Ks are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ⟶ (Heterodimer x ∧ CatalyticSubunit y ∧ RegulatorySubunit z ∧ ConsistOf x y ∧ ConsistOf x z)"

(* Explanation 3: The binding of the regulatory subunit (p85) to the catalytic subunit (p110) within the PI3K complex is essential because it directly causes the relief of the inhibitory effect on the catalytic subunit (p110) *)
axiomatization where
  explanation_3: "∃x y z e1 e2. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binding e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Essential e1 ∧ Relief e2 ∧ Effect w ∧ Inhibitory w ∧ On w y ∧ Cause e1 e2"

(* Explanation 4: The relief of the inhibitory effect on the catalytic subunit (p110) is a direct consequence of the binding of the regulatory subunit (p85) to the catalytic subunit (p110) within the PI3K complex *)
axiomatization where
  explanation_4: "∃x y z e1 e2. Relief e1 ∧ Effect w ∧ Inhibitory w ∧ On w y ∧ CatalyticSubunit y ∧ RegulatorySubunit x ∧ PI3K z ∧ Binding e2 ∧ Agent e2 x ∧ Patient e2 y ∧ Within e2 z ∧ Consequence e1 e2"

theorem hypothesis:
  assumes asm: "RegulatorySubunit z ∧ CatalyticSubunit x ∧ PI3K y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
  shows "∃x y e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x"
proof -
  (* From the known information, we have the presence of a regulatory subunit, a catalytic subunit, and a PI3K complex. *)
  from asm have "RegulatorySubunit z ∧ CatalyticSubunit x ∧ PI3K y" by blast
  (* Explanation 1 provides a scenario where the binding of the regulatory subunit to the catalytic subunit within the PI3K complex causes relief of the inhibitory effect. *)
  (* This matches the logical relation Implies(A, B), where A is the binding and B is the relief of the inhibitory effect. *)
  from explanation_1 obtain e1 e2 where 
    "Binding e1 ∧ Agent e1 z ∧ Patient e1 x ∧ Within e1 y ∧ Relief e2 ∧ Effect w ∧ Inhibitory w ∧ On w x ∧ Agent e2 z ∧ Cause e1 e2" sledgehammer
  (* Since the binding causes the relief, we can conclude that the binding event e1 relieves the inhibitory effect. *)
  then have "Relieves e1" <ATP>
  (* Therefore, we can construct the hypothesis statement. *)
  then show "∃x y e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x" <ATP>
qed

end
