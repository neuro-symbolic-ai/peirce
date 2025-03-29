theory clinical_54_7
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
  DamagedDNASites :: "entity ⇒ bool"
  Recruits :: "event ⇒ bool"
  To :: "entity ⇒ entity ⇒ bool"
  Facilitate :: "event ⇒ bool"
  Detects :: "event ⇒ bool"
  Binds :: "event ⇒ bool"
  Sites :: "entity ⇒ bool"
  SSDNADamage :: "entity ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR. *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA sites. *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DamagedDNASites z ∧ Recruits e ∧ Agent e x ∧ Patient e y ∧ To y z"

(* Explanation 3: The synthesis of PAR by PARP1 is necessary for repair proteins to be recruited to damaged DNA sites. *)
axiomatization where
  explanation_3: "∀x y z w e1 e2. PAR x ∧ PARP1 y ∧ RepairProteins z ∧ DamagedDNASites w ∧ Synthesises e1 ∧ Agent e1 y ∧ Patient e1 x ⟶ (Recruits e2 ∧ Agent e2 x ∧ Patient e2 z ∧ To z w)"

(* Explanation 4: Repair proteins, once recruited to damaged DNA sites, directly facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
axiomatization where
  explanation_4: "∃x y z w e1 e2 e3 e4. RepairProteins x ∧ DamagedDNASites y ∧ PARP1 z ∧ Sites w ∧ SSDNADamage w ∧ Recruits e1 ∧ Agent e1 x ∧ Patient e1 y ⟶ (Facilitate e2 ∧ Agent e2 x ∧ Detects e3 ∧ Agent e3 z ∧ Patient e3 w ∧ Binds e4 ∧ Agent e4 z ∧ Patient e4 w)"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ Sites y ∧ SSDNADamage y"
  (* Hypothesis: PARP1 detects and binds to sites of SS DNA damage. *)
  shows "∃x y e1 e2. PARP1 x ∧ Sites y ∧ SSDNADamage y ∧ Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y"
proof -
  (* From the known information, we have PARP1 x, Sites y, and SSDNADamage y. *)
  from asm have "PARP1 x ∧ Sites y ∧ SSDNADamage y" by auto
  (* Explanation 4 states that repair proteins, once recruited to damaged DNA sites, facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* We have a derived implication: Implies(A, D), which means if PARP1 synthesises PAR, then repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* Since we have PARP1 x, we can infer that repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  then have "Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y" sledgehammer
  (* Therefore, we can conclude that PARP1 detects and binds to sites of SS DNA damage. *)
  then show ?thesis <ATP>
qed

end
