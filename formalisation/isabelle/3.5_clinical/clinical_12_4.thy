theory clinical_12_4
imports Main


begin

typedecl entity
typedecl event

consts
  PARP1 :: "entity ⇒ bool"
  PAR :: "entity ⇒ bool"
  Synthesises :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  RepairProteins :: "entity ⇒ bool"
  DNADamageSite :: "entity ⇒ bool"
  Recruits :: "event ⇒ bool"
  Destination :: "event ⇒ entity ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DNADamageSite z ∧ Recruits e ∧ Agent e x ∧ Patient e y ∧ Destination e z"


theorem hypothesis:
 assumes asm: "PARP1 x ∧ PAR y ∧ RepairProteins z ∧ SitesOfDNADamage e"
  (* Hypothesis: PARP1 synthesis PAR which recruits repair proteins to sites of DNA damage *)
 shows "∃x y z e. PARP1 x ∧ PAR y ∧ RepairProteins z ∧ SitesOfDNADamage e ∧ Synthesises e ∧ Agent e x ∧ Patient e y ∧ Recruits e z"
  sledgehammer
  oops

end
