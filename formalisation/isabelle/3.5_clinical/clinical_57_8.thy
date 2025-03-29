theory clinical_57_8
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
  Localisation :: "entity ⇒ bool"
  SitesOfDamage :: "entity ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Major :: "entity ⇒ bool"
  BRCA2BindingPartner :: "entity ⇒ bool"
  Links :: "event ⇒ bool"
  InRepair :: "event ⇒ bool"
  InDamage :: "event ⇒ bool"
  BRCA1 :: "entity"
  BRCA2 :: "entity"

(* Explanation 1: PALB2 encodes a binding partner of BRCA2 that is required for its localisation to sites of DNA damage *)
axiomatization where
  explanation_1: "∃x y z e. PALB2 x ∧ BindingPartner y ∧ RequiredFor e ∧ Agent e x ∧ Patient e y ∧ Localisation z ∧ SitesOfDamage z ∧ To y z"

(* Explanation 2: PALB2 encodes a major BRCA2 binding partner that links BRCA1 and BRCA2 in HR repair and DNA damage *)
axiomatization where
  explanation_2: "∃x y z e. PALB2 x ∧ Major y ∧ BRCA2BindingPartner z ∧ Links e ∧ InRepair e ∧ InDamage e ∧ To BRCA1 z ∧ To BRCA2 z"


theorem hypothesis:
 assumes asm: "PALB2 x ∧ BindingPartner y ∧ Localisation z ∧ SitesOfDamage z"
  (* Hypothesis: PALB2 encodes a binding partner that localises BRCA2 to sites of DNA damage and links BRCA1 and BRCA2 in HR repair and DNA damage *)
 shows "∃x y z e. PALB2 x ∧ BindingPartner y ∧ Localisation z ∧ Agent e x ∧ Patient e z ∧ SitesOfDamage z ∧ Links e ∧ InRepair e ∧ InDamage e ∧ To y z ∧ To x z ∧ To BRCA1 z ∧ To BRCA2 z"
  sledgehammer
  oops

end
