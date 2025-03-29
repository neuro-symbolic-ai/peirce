theory clinical_57_5
imports Main


begin

typedecl entity
typedecl event

consts
  PALB2 :: "entity ⇒ bool"
  BindingPartner :: "entity ⇒ bool"
  RequiredFor :: "entity ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  LocalisationTo :: "event ⇒ entity ⇒ bool"
  SitesOfDNADamage :: "entity ⇒ bool"
  Major :: "entity ⇒ bool"
  BRCA2BindingPartner :: "entity ⇒ bool"
  Links :: "event ⇒ bool"
  HRRepair :: "entity ⇒ entity ⇒ bool"
  DNADamage :: "entity ⇒ entity ⇒ bool"
  BRCA1 :: entity
  BRCA2 :: entity

(* Explanation 1: PALB2 encodes a binding partner of BRCA2 that is required for its localisation to sites of DNA damage *)
axiomatization where
  explanation_1: "∃x y z e. PALB2 x ∧ BindingPartner y ∧ RequiredFor e ∧ Agent e y ∧ Patient e z ∧ LocalisationTo e z ∧ SitesOfDNADamage z"

(* Explanation 2: PALB2 encodes a major BRCA2 binding partner that links BRCA1 and BRCA2 in HR repair and DNA damage *)
axiomatization where
  explanation_2: "∃x y z e. PALB2 x ∧ Major y ∧ BRCA2BindingPartner y ∧ Links e ∧ Agent e y ∧ Patient e BRCA1 ∧ Patient e BRCA2 ∧ HRRepair BRCA1 BRCA2 ∧ DNADamage BRCA1 BRCA2"


theorem hypothesis:
 assumes asm: "PALB2 x ∧ BindingPartner y ∧ RequiredFor e ∧ LocalisationTo e z ∧ Major y ∧ BRCA2BindingPartner y"
  (* Hypothesis: PALB2 encodes a binding partner that localises BRCA2 to sites of DNA damage and links BRCA1 and BRCA2 in HR repair and DNA damage *)
 shows "∃x y z e1 e2 e3. PALB2(x) ∧ BindingPartner(y) ∧ LocalisationTo(e1, x) ∧ Agent(e1, x) ∧ Patient(e1, z) ∧ SitesOfDNADamage(z) ∧ Links(e2) ∧ Agent(e2, y) ∧ Patient(e2, BRCA2) ∧ HRRepair(BRCA1, BRCA2) ∧ Agent(e3, BRCA1) ∧ Patient(e3, BRCA2) ∧ DNADamage(BRCA1, BRCA2)"
proof -
  (* From the premise, we can get known information about PALB2, binding partner, required for, localisation to, major, and BRCA2 binding partner. *)
  from asm have "PALB2 x" and "BindingPartner y" and "RequiredFor e" and "LocalisationTo e z" and "Major y" and "BRCA2BindingPartner y" <ATP>
  (* We have the logical relation Implies(A, B), Implies(PALB2 encodes a binding partner of BRCA2, PALB2 is required for the localization of BRCA2 to sites of DNA damage) *)
  (* A is from explanatory sentence 1, B is from explanatory sentence 1. *)
  (* We already have PALB2 x, binding partner y, required for e, and localisation to e z, so we can infer SitesOfDNADamage z. *)
  then have "SitesOfDNADamage z" <ATP>
  (* We have the logical relation Implies(C, D), Implies(PALB2 encodes a major BRCA2 binding partner, PALB2 links BRCA1 and BRCA2 in HR repair and DNA damage) *)
  (* C is from explanatory sentence 2, D is from explanatory sentence 2. *)
  (* We already have major y and BRCA2 binding partner y, so we can infer links e, agent e y, patient e BRCA1, patient e BRCA2, HRRepair BRCA1 BRCA2, agent e BRCA1, patient e BRCA2, and DNADamage BRCA1 BRCA2. *)
  then have "Links e" and "Agent e y" and "Patient e BRCA1" and "Patient e BRCA2" and "HRRepair BRCA1 BRCA2" and "Agent e BRCA1" and "Patient e BRCA2" and "DNADamage BRCA1 BRCA2" <ATP>
  then show ?thesis <ATP>
qed

end
