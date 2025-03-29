theory clinical_96_6
imports Main


begin

typedecl entity
typedecl event

consts
  Patient :: "entity ⇒ bool"
  Common :: "entity ⇒ bool"
  BRAF :: "entity ⇒ bool"
  V600E :: "entity ⇒ bool"
  Mutation :: "entity ⇒ bool"
  Has :: "entity ⇒ entity ⇒ bool"
  Vemurafenib :: "entity ⇒ bool"
  Inhibitor :: "entity ⇒ bool"
  LowMolecularWeight :: "entity ⇒ bool"
  OrallyAvailable :: "entity ⇒ bool"
  Binds :: "entity ⇒ bool"
  Selectively :: "entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  ATPBindingSite :: "entity ⇒ bool"
  Kinase :: "entity ⇒ bool"
  Inhibits :: "entity ⇒ bool"
  Activity :: "entity ⇒ bool"

(* Explanation 1: Patient has common BRAF V600E mutation. *)
axiomatization where
  explanation_1: "∃x y. Patient x ∧ Common y ∧ BRAF y ∧ V600E y ∧ Mutation y ∧ Has x y"

(* Explanation 2: vemurafenib is a low-molecular-weight, orally available inhibitor which selectively binds to the ATPbinding site of BRAF V600E kinase and inhibits its activity. *)
axiomatization where
  explanation_2: "∀x y z w. Vemurafenib x ∧ Inhibitor y ∧ LowMolecularWeight y ∧ OrallyAvailable y ∧ Binds z ∧ Selectively z ∧ To z w ∧ ATPBindingSite w ∧ BRAF w ∧ V600E w ∧ Kinase w ∧ Inhibits w ∧ Activity w"


theorem hypothesis:
 assumes asm: "Patient x ∧ Treatment y ∧ Vemurafenib z ∧ V600E z ∧ Mutation z"
  (* Hypothesis: Patient could receive treatment with vemurafenib for V600E mutation. *)
 shows "∃x y z e. Patient x ∧ Treatment y ∧ Vemurafenib z ∧ V600E z ∧ Mutation z ∧ Receive e ∧ Agent e x ∧ Patient e y ∧ With e z"
  sledgehammer
  oops

end
