theory clinical_96_5
imports Main


begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  Common :: "entity ⇒ bool"
  BRAF_V600E_Mutation :: "entity ⇒ bool"
  Has :: "entity ⇒ entity ⇒ bool"
  Vemurafenib :: "entity ⇒ bool"
  Inhibitor :: "entity ⇒ bool"
  LowMolecularWeight :: "entity ⇒ bool"
  OrallyAvailable :: "entity ⇒ bool"
  BindsTo :: "entity ⇒ bool"
  Selectively :: "entity ⇒ bool"
  ATPbindingSite :: "entity ⇒ bool"
  BRAF_V600E_Kinase :: "entity ⇒ bool"
  InhibitsActivity :: "entity ⇒ bool"
  Of :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: Patient has common BRAF V600E mutation. *)
axiomatization where
  explanation_1: "∃x y. Patient x ∧ Common y ∧ BRAF_V600E_Mutation y ∧ Has x y"

(* Explanation 2: Vemurafenib is a low-molecular-weight, orally available inhibitor which selectively binds to the ATPbinding site of BRAF V600E kinase and inhibits its activity. *)
axiomatization where
  explanation_2: "∀x y z w. Vemurafenib x ∧ Inhibitor y ∧ LowMolecularWeight y ∧ OrallyAvailable y ∧ BindsTo z ∧ Selectively z ∧ ATPbindingSite z ∧ BRAF_V600E_Kinase w ∧ InhibitsActivity w ∧ Of z w"


theorem hypothesis:
  assumes asm: "Patient x ∧ Treatment y ∧ Vemurafenib z ∧ V600E_Mutation z"
  (* Hypothesis: Patient could receive treatment with vemurafenib for V600E mutation. *)
  shows "∃x y z e. Patient x ∧ Treatment y ∧ Vemurafenib z ∧ V600E_Mutation z ∧ Receive e ∧ Agent e x ∧ Patient e y ∧ With e z"
  sledgehammer
  oops

end
