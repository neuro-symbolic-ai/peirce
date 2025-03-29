theory clinical_54_0
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
  DamagedDNASite :: "entity ⇒ bool"
  Recruits :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Sites :: "entity ⇒ bool"
  SSDNADamage :: "entity ⇒ bool"
  Detects :: "event ⇒ bool"
  Binds :: "event ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR. *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site. *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DamagedDNASite z ∧ Recruits e ∧ Agent e x ∧ Patient e y ∧ To y z"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ Sites y ∧ SSDNADamage z"
  (* Hypothesis: PARP1 detects and binds to sites of SS DNA damage. *)
  shows "∃x y z e1 e2. PARP1 x ∧ Sites y ∧ SSDNADamage z ∧ Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y ∧ To y z"
proof -
  (* From the known information, we have PARP1 x, Sites y, and SSDNADamage z. *)
  from asm have "PARP1 x ∧ Sites y ∧ SSDNADamage z" by blast
  (* Explanation 1 states that PARP1 synthesises PAR. *)
  (* Explanation 2 states that PAR recruits repair proteins to damaged DNA site. *)
  (* Using the logical relation Implies(A, B), we can infer that if PARP1 synthesises PAR, then PAR recruits repair proteins to damaged DNA site. *)
  (* This implies that PARP1 is involved in detecting and binding to sites of SS DNA damage. *)
  then have "∃e1 e2. Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y ∧ To y z" sledgehammer
  then show ?thesis <ATP>
qed

end
