theory clinical_78_10
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
  EffectOn :: "event ⇒ entity ⇒ bool"
  Heterodimer :: "entity ⇒ entity ⇒ entity ⇒ bool"
  Relieves :: "event ⇒ bool"
  Consequence :: "event ⇒ event ⇒ bool"

(* Explanation 1: The regulatory subunit (p85) binds to the catalytic subunit (p110) within the PI3K complex, and this binding directly causes the relief of the inhibitory effect on the catalytic subunit (p110) by the regulatory subunit (p85) *)
axiomatization where
  explanation_1: "∃x y z e1 e2. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binds e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Within e1 z ∧ Binding e2 ∧ Agent e2 x ∧ Causes e2 ∧ Relief e2 ∧ EffectOn e2 y"

(* Explanation 2: PI3Ks are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ∧ CatalyticSubunit y ∧ RegulatorySubunit z ⟶ Heterodimer x y z"

(* Explanation 3: The binding of the regulatory subunit (p85) to the catalytic subunit (p110) within the PI3K complex directly relieves the inhibitory effect on the catalytic subunit (p110) *)
axiomatization where
  explanation_3: "∃x y z e. RegulatorySubunit x ∧ CatalyticSubunit y ∧ PI3K z ∧ Binding e ∧ Agent e x ∧ Patient e y ∧ Within e z ∧ Relieves e ∧ EffectOn e y"

(* Explanation 4: The relief of the inhibitory effect on the catalytic subunit (p110) is a direct consequence of the binding of the regulatory subunit (p85) to the catalytic subunit (p110) within the PI3K complex *)
axiomatization where
  explanation_4: "∃x y z e1 e2. CatalyticSubunit x ∧ RegulatorySubunit y ∧ PI3K z ∧ Relief e1 ∧ EffectOn e1 x ∧ Binding e2 ∧ Agent e2 y ∧ Patient e2 x ∧ Within e2 z ⟶ Consequence e1 e2"

theorem hypothesis:
  assumes asm: "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit y"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110 *)
  shows "∃x y e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit y ∧ Binding e ∧ Agent e y ∧ Patient e x ∧ Relieves e ∧ EffectOn e x"
proof -
  (* From the premise, we have known information about the catalytic subunit, PI3K, and regulatory subunit. *)
  from asm have "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit y" by blast
  (* Explanation 3 states that the binding of the regulatory subunit to the catalytic subunit within the PI3K complex directly relieves the inhibitory effect on the catalytic subunit. *)
  (* This directly corresponds to the hypothesis we want to prove. *)
  from explanation_3 obtain e where "Binding e ∧ Agent e y ∧ Patient e x ∧ Relieves e ∧ EffectOn e x" sledgehammer
  (* Combine the known information with the result from explanation 3. *)
  then have "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit y ∧ Binding e ∧ Agent e y ∧ Patient e x ∧ Relieves e ∧ EffectOn e x" <ATP>
  then show ?thesis <ATP>
qed

end
