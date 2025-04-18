theory clinical_57_3
imports Main


begin

typedecl entity
typedecl event

consts
  PALB2 :: "entity ⇒ bool"
  BindingPartner :: "entity ⇒ bool"
  BRCA2 :: "entity ⇒ bool"
  RequiredFor :: "entity ⇒ bool"
  Agent :: "entity ⇒ entity ⇒ bool"
  Patient :: "entity ⇒ entity ⇒ bool"
  LocalisationTo :: "entity ⇒ entity ⇒ bool"
  SitesOfDNADamage :: "entity ⇒ bool"
  Major :: "entity ⇒ bool"
  Links :: "entity ⇒ bool"
  BRCA1 :: "entity ⇒ bool"
  HRRepair :: "entity ⇒ bool"
  DNADamage :: "entity ⇒ bool"

(* Explanation 1: PALB2 encodes a binding partner of BRCA2 that is required for its localisation to sites of DNA damage *)
axiomatization where
  explanation_1: "∃x y z e. PALB2 x ∧ BindingPartner y ∧ BRCA2 z ∧ RequiredFor e ∧ Agent e y ∧ Patient e z ∧ LocalisationTo e z ∧ SitesOfDNADamage z"

(* Explanation 2: PALB2 encodes a major BRCA2 binding partner that links BRCA1 and BRCA2 in HR repair and DNA damage *)
axiomatization where
  explanation_2: "∃x y z e. PALB2 x ∧ Major y ∧ BRCA2 z ∧ BindingPartner y ∧ Links e ∧ Agent e y ∧ Patient e z ∧ BRCA1 z ∧ HRRepair z ∧ DNADamage z"


theorem hypothesis:
 assumes asm: "PALB2 x ∧ BindingPartner y ∧ BRCA2 z"
  (* Hypothesis: PALB2 encodes a binding partner that localises BRCA2 to sites of DNA damage and links BRCA1 and BRCA2 in HR repair and DNA damage *)
 shows "∃x y z e1 e2. PALB2 x ∧ BindingPartner y ∧ BRCA2 z ∧ LocalisationTo e1 ∧ Agent e1 x ∧ Patient e1 z ∧ SitesOfDNADamage z ∧ Links e2 ∧ Agent e2 y ∧ Patient e2 z ∧ BRCA1 z ∧ HRRepair z ∧ DNADamage z"
  sledgehammer
  oops

end
