theory clinical_78_0
imports Main

begin

typedecl entity
typedecl event

consts
  GrowthFactor :: "entity ⇒ bool"
  Stimulation :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Binds :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Relieves :: "event ⇒ bool"
  Effect :: "entity ⇒ bool"
  Inhibitory :: "entity ⇒ bool"
  Over :: "entity ⇒ entity ⇒ bool"
  Upon :: "event ⇒ entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Heterodimer :: "entity ⇒ bool"
  ConsistsOf :: "entity ⇒ entity ⇒ entity ⇒ bool"
  CatalyticSubunit :: "entity ⇒ bool"
  Family :: "entity ⇒ bool"
  LipidKinase :: "entity ⇒ bool"
  Comprise :: "entity ⇒ entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Upon growth factor stimulation p85 binds… relieving its inhibitory effect over p110. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. GrowthFactor x ∧ Stimulation y ∧ RegulatorySubunit z ∧ Binds e1 ∧ Agent e1 z ∧ Relieves e2 ∧ Effect w ∧ Inhibitory w ∧ Over w y ∧ Upon e1 x"

(* Explanation 2: PI3Ks… are heterodimers consisting of a catalytic (p110) and a regulatory (p85) subunit. *)
axiomatization where
  explanation_2: "∀x y z. PI3K x ⟶ (Heterodimer x ∧ ConsistsOf x y z ∧ CatalyticSubunit y ∧ RegulatorySubunit z)"

(* Explanation 3: Phosphoinositide 3-kinases (PI3Ks) comprise a family of lipid kinases. *)
axiomatization where
  explanation_3: "∀x y. PI3K x ⟶ (Family y ∧ LipidKinase y ∧ Comprise x y)"

theorem hypothesis:
  assumes asm: "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z"
  (* Hypothesis: Binding of the catalytic subunit (p110) of PI3K by the regulatory subunit (p85) relieves the inhibitory effect on p110. *)
  shows "∃x y z e. CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z ∧ Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x"
proof -
  (* From the premise, we have known information about the catalytic subunit, PI3K, and regulatory subunit. *)
  from asm have "CatalyticSubunit x ∧ PI3K y ∧ RegulatorySubunit z" by blast
  (* Explanation 2 provides that PI3Ks are heterodimers consisting of a catalytic and a regulatory subunit. *)
  (* This aligns with the known information, allowing us to infer the binding event. *)
  from explanation_2 have "Heterodimer y ∧ ConsistsOf y x z" using assms by blast
  (* Explanation 1 states that upon growth factor stimulation, p85 binds, relieving its inhibitory effect over p110. *)
  (* We can use this to infer the binding and relieving event. *)
  from explanation_1 have "∃e. Binds e ∧ Agent e z ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x" sledgehammer
  (* Combining these, we can conclude the hypothesis. *)
  then have "∃e. Binding e ∧ Agent e z ∧ Patient e x ∧ Relieves e ∧ Effect w ∧ Inhibitory w ∧ On w x" <ATP>
  then show ?thesis <ATP>
qed

end
