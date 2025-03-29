theory clinical_70_0
imports Main

begin

typedecl entity
typedecl event

consts
  Subunit :: "entity ⇒ bool"
  P110 :: "entity ⇒ bool"
  P110α :: "entity ⇒ bool"
  Gene :: "entity ⇒ bool"
  PIK3CA :: "entity ⇒ bool"
  Transcribed :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Source :: "event ⇒ entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  PI3K :: "entity ⇒ bool"
  Tumor :: "entity ⇒ bool"
  Spectrum :: "entity ⇒ bool"
  Broad :: "entity ⇒ bool"
  Identified :: "event ⇒ bool"
  Location :: "event ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  Cancer :: "entity ⇒ bool"
  Breast :: "entity ⇒ bool"
  Has :: "event ⇒ bool"
  Seen :: "event ⇒ bool"
  Frequently :: "event ⇒ bool"

(* Explanation 1: PI3Ks catalytic subunit p110, of which p110α is transcribed from the PIK3CA gene. *)
axiomatization where
  explanation_1: "∀x y z e. Subunit x ∧ P110 x ∧ P110α y ∧ Gene z ∧ PIK3CA z ∧ Transcribed e ∧ Agent e y ∧ Source e z"

(* Explanation 2: Activating mutations of the p110α subunit of PI3K (PIK3CA) have been identified in a broad spectrum of tumors. *)
axiomatization where
  explanation_2: "∃x y z e. Mutation x ∧ Subunit x ∧ P110α x ∧ PI3K x ∧ PIK3CA x ∧ Tumor y ∧ Spectrum z ∧ Broad z ∧ Identified e ∧ Agent e x ∧ Location e y ∧ In y z"

(* Explanation 3: Patient has an activating PIK3Ca mutation which is seen frequently in breast cancer. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. Patient x ∧ Mutation y ∧ PIK3CA y ∧ Cancer z ∧ Breast z ∧ Has e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Seen e2 ∧ Agent e2 y ∧ Location e2 z ∧ Frequently e2"

theorem hypothesis:
  assumes asm: "Patient x"
  (* Hypothesis: Patient likely has activating mutation of p110α subunit of PI3K (PIK3CA). *)
  shows "∃x y e. Patient x ∧ Mutation y ∧ Subunit y ∧ P110α y ∧ PI3K y ∧ PIK3CA y ∧ Has e ∧ Agent e x ∧ Agent e y"
  using explanation_1 explanation_2 explanation_3 by blast
  

end
