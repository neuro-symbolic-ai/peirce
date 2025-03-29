theory clinical_54_4
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
  Facilitate :: "event ⇒ bool"
  Detects :: "event ⇒ bool"
  Binds :: "event ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR recruits repair proteins to damaged DNA site *)
axiomatization where
  explanation_2: "∃x y z e. PAR x ∧ RepairProteins y ∧ DamagedDNASite z ∧ Recruits e ∧ Agent e x ∧ Patient e y ∧ To y z"

(* Explanation 3: The synthesis of PAR by PARP1 is necessary for repair proteins to facilitate the detection and binding of PARP1 to sites of SS DNA damage *)
axiomatization where
  explanation_3: "∀x y z w e1 e2 e3 e4. (PAR x ∧ PARP1 y ∧ Synthesises e1 ∧ Agent e1 y ∧ Patient e1 x) ⟶ (RepairProteins z ∧ Sites w ∧ SSDNADamage w ∧ Facilitate e2 ∧ Agent e2 z ∧ Patient e2 e3 ∧ Detects e3 ∧ Agent e3 y ∧ Patient e3 w ∧ Binds e4 ∧ Agent e4 y ∧ Patient e4 w)"

(* Explanation 4: Repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage *)
axiomatization where
  explanation_4: "∃x y z e1 e2 e3. RepairProteins x ∧ PARP1 y ∧ Sites z ∧ SSDNADamage z ∧ Facilitate e1 ∧ Agent e1 x ∧ Patient e1 e2 ∧ Detects e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Binds e3 ∧ Agent e3 y ∧ Patient e3 z"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ Sites y ∧ SSDNADamage z"
  (* Hypothesis: PARP1 detects and binds to sites of SS DNA damage *)
  shows "∃x y z e1 e2. PARP1 x ∧ Sites y ∧ SSDNADamage z ∧ Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y ∧ To y z"
proof -
  (* From the known information, we have PARP1 x, Sites y, and SSDNADamage z. *)
  from asm have "PARP1 x ∧ Sites y ∧ SSDNADamage z" <ATP>
  
  (* Explanation 4 states that repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* This is equivalent to the detection and binding of PARP1 to sites of SS DNA damage (Logical Relation: Equivalent(C, E)). *)
  (* Therefore, we can infer the detection and binding of PARP1 to sites of SS DNA damage. *)
  from explanation_4 have "∃e1 e2. Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y" <ATP>
  
  (* Combine the known information with the inferred detection and binding events. *)
  then have "∃x y z e1 e2. PARP1 x ∧ Sites y ∧ SSDNADamage z ∧ Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y" <ATP>
  
  then show ?thesis <ATP>
qed

end
