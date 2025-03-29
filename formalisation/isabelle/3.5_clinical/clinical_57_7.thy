theory clinical_57_7
imports Main


begin

typedecl entity
typedecl event

consts
  PALB2 :: "entity ⇒ bool"
  BindingPartner :: "entity ⇒ bool"
  RequiredFor :: "entity ⇒ bool"
  Agent :: "entity ⇒ entity ⇒ bool"
  Patient :: "entity ⇒ entity ⇒ bool"
  LocalisationTo :: "entity ⇒ entity ⇒ bool"
  SitesOfDNADamage :: "entity ⇒ bool"
  Major :: "entity ⇒ bool"
  BRCA2BindingPartner :: "entity ⇒ bool"
  Links :: "entity ⇒ bool"
  HRRepair :: "entity ⇒ bool"
  DNADamage :: "entity ⇒ bool"
  BRCA1 :: "entity"
  BRCA2 :: "entity"

(* Explanation 1: PALB2 encodes a binding partner of BRCA2 that is required for its localisation to sites of DNA damage *)
axiomatization where
  explanation_1: "∃x y z e. PALB2 x ∧ BindingPartner y ∧ RequiredFor e ∧ Agent e y ∧ Patient e z ∧ LocalisationTo e z ∧ SitesOfDNADamage z"

(* Explanation 2: PALB2 encodes a major BRCA2 binding partner that links BRCA1 and BRCA2 in HR repair and DNA damage *)
axiomatization where
  explanation_2: "∃x y z e. PALB2 x ∧ Major y ∧ BRCA2BindingPartner y ∧ Links e ∧ Agent e y ∧ Patient e BRCA1 ∧ Patient e BRCA2 ∧ HRRepair e ∧ DNADamage e"


theorem hypothesis:
 assumes asm: "PALB2 x ∧ BindingPartner y ∧ RequiredFor e1 ∧ Localises e1 z ∧ Links e2 ∧ Major y ∧ BRCA2BindingPartner y"
  (* Hypothesis: PALB2 encodes a binding partner that localises BRCA2 to sites of DNA damage and links BRCA1 and BRCA2 in HR repair and DNA damage *)
 shows "∃x y z e1 e2 e3. PALB2(x) ∧ BindingPartner(y) ∧ Localises(e1) ∧ Agent(e1, x) ∧ Patient(e1, z) ∧ SitesOfDNADamage(z) ∧ Links(e2) ∧ Agent(e2, y) ∧ Patient(e2, BRCA2) ∧ HRRepair(e2) ∧ DNADamage(e2) ∧ Links(e3) ∧ Agent(e3, y) ∧ Patient(e3, BRCA1) ∧ Patient(e3, BRCA2) ∧ HRRepair(e3) ∧ DNADamage(e3)"
  sledgehammer
  oops

end
