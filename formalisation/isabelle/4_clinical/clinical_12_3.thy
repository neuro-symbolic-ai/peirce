theory clinical_12_3
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
  Synthesised :: "event ⇒ bool"
  Damaged_DNA_Site :: "entity"

(* Explanation 1: PARP1 synthesises PAR *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DNA_Site z ∧ Damaged z ∧ Recruits e ∧ Agent e x ∧ Patient e y ∧ To y z"

(* Explanation 3: The PAR synthesised by PARP1 is the same PAR that recruits repair proteins to the damaged DNA site *)
axiomatization where
  explanation_3: "∀x y z e1 e2. PAR x ∧ PARP1 y ∧ RepairProteins z ∧ Synthesised e1 ∧ Agent e1 y ∧ Patient e1 x ∧ Recruits e2 ∧ Agent e2 x ∧ Patient e2 z ∧ To z Damaged_DNA_Site"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PAR y ∧ RepairProteins z"
  (* Hypothesis: PARP1 synthesis PAR which recruits repair proteins to sites of DNA damage *)
  shows "∃x y z e1 e2. PARP1 x ∧ PAR y ∧ RepairProteins z ∧ Synthesis e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Recruits e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z DNA_Damage_Sites"
proof -
  (* From the known information, we have PARP1 x, PAR y, and RepairProteins z. *)
  from asm have "PARP1 x ∧ PAR y ∧ RepairProteins z" by auto
  
  (* Explanation 1 states that PARP1 synthesises PAR. *)
  (* We can instantiate this explanation with the known entities. *)
  from explanation_1 have "∃e1. Synthesises e1 ∧ Agent e1 x ∧ Patient e1 y" using explanation_3 by blast
  
  (* Explanation 2 states that PAR recruits repair proteins to a damaged DNA site. *)
  (* We can instantiate this explanation with the known entities. *)
  from explanation_2 have "∃e2. Recruits e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z Damaged_DNA_Site" by (simp add: explanation_3)
  
  (* Explanation 3 provides the equivalence between the PAR synthesised by PARP1 and the PAR that recruits repair proteins. *)
  (* Using the logical relation Equivalent(C, D), we can infer the connection between the synthesis and recruitment events. *)
  from explanation_3 have "Synthesised e1 ∧ Recruits e2 ∧ Agent e1 x ∧ Patient e1 y ∧ Agent e2 y ∧ Patient e2 z ∧ To z Damaged_DNA_Site" by blast
  
  (* Combining all the information, we can conclude the hypothesis. *)
  then show "∃x y z e1 e2. PARP1 x ∧ PAR y ∧ RepairProteins z ∧ Synthesises e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Recruits e2 ∧ Agent e2 y ∧ Patient e2 z ∧ To z Damaged_DNA_Site" sledgehammer
qed

end
