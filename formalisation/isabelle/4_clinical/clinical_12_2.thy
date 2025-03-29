theory clinical_12_2
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
  DNA_Site :: "entity ⇒ bool"
  Damaged :: "entity ⇒ bool"
  Recruits :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR. *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site. *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DNA_Site z ∧ Damaged z ∧ Recruits e ∧ Agent e x ∧ Patient e y ∧ To y z"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PAR y ∧ RepairProteins z"
  (* Hypothesis: PARP1 synthesis PAR which recruits repair proteins to sites of DNA damage *)
  shows "∃x y z e1 e2. PARP1 x ∧ PAR y ∧ RepairProteins z ∧ Synthesis e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Recruits e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z DNA_Damage_Sites"
proof -
  (* From the known information, we have PARP1 x, PAR y, and RepairProteins z. *)
  from asm have "PARP1 x ∧ PAR y ∧ RepairProteins z" by meson
  (* Explanation 1 provides that PARP1 synthesises PAR. *)
  (* We can instantiate the existential quantifiers in explanation_1 with x, y, and some event e1. *)
  then obtain e1 where "Synthesises e1 ∧ Agent e1 x ∧ Patient e1 y" sledgehammer
  (* Explanation 2 provides that PAR recruits repair proteins to damaged DNA site. *)
  (* We can instantiate the existential quantifiers in explanation_2 with y, z, and some event e2. *)
  then obtain e2 where "Recruits e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z DNA_Damage_Sites" <ATP>
  (* Combining these, we have the required hypothesis. *)
  then show ?thesis <ATP>
qed

end
