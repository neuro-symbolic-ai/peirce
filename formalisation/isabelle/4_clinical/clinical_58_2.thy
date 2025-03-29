theory clinical_58_2
imports Main

begin

typedecl entity
typedecl event

consts
  BRCA2 :: "entity ⇒ bool"
  RAD51 :: "entity ⇒ bool"
  HRR :: "entity ⇒ bool"
  Human :: "entity ⇒ bool"
  Involved :: "entity ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Molecules :: "entity ⇒ bool"
  Undamaged :: "entity ⇒ bool"
  Homologous :: "entity ⇒ bool"
  Binding :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Joining :: "event ⇒ bool"
  Catalyze :: "event ⇒ event ⇒ bool"
  Repair :: "entity ⇒ bool"
  Promote :: "event ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Via :: "event ⇒ entity ⇒ bool"

(* Explanation 1: BRCA2 and RAD51 homolog 1 are both involved in HRR in humans. *)
axiomatization where
  explanation_1: "∃x y z. BRCA2 x ∧ RAD51 y ∧ HRR z ∧ Human z ∧ Involved x z ∧ Involved y z ∧ In x z ∧ In y z"

(* Explanation 2: The binding of BRCA2 and RAD51 homolog 1 catalyzes the joining of undamaged homologous molecules. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. BRCA2 x ∧ RAD51 y ∧ Molecules z ∧ Undamaged z ∧ Homologous z ∧ Binding e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Joining e2 ∧ Agent e2 z ∧ Catalyze e1 e2"

theorem hypothesis:
  assumes asm: "BRCA2 x ∧ Molecules y ∧ Undamaged y ∧ Homologous y ∧ Repair y ∧ RAD51 z ∧ Human z"
  (* Hypothesis: BRCA2 promotes the joining of undamaged homologous repair molecules via RAD51 homolog 1 in humans. *)
  shows "∃x y z e1 e2. BRCA2 x ∧ Molecules y ∧ Undamaged y ∧ Homologous y ∧ Repair y ∧ RAD51 z ∧ Human z ∧ Joining e1 ∧ Agent e1 y ∧ Promote e2 ∧ Agent e2 x ∧ Patient e2 e1 ∧ Via e2 z ∧ In e2 z"
  sledgehammer
  oops

end
