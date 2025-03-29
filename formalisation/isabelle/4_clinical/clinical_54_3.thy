theory clinical_54_3
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
  explanation_3: "∀x y z w e1 e2 e3 e4 e5. PAR x ∧ PARP1 y ∧ RepairProteins z ∧ Sites w ∧ SSDNADamage w ∧ Synthesises e1 ∧ Agent e1 y ∧ Patient e1 x ⟶ (Facilitate e2 ∧ Agent e2 z ∧ Patient e2 e3 ∧ Detects e5 ∧ Agent e5 y ∧ Patient e5 w ∧ Binds e4 ∧ Agent e4 y ∧ Patient e4 w)"

(* Explanation 4: Repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage *)
axiomatization where
  explanation_4: "∃x y z e1 e2 e3 e4. RepairProteins x ∧ PARP1 y ∧ Sites z ∧ SSDNADamage z ∧ Facilitate e1 ∧ Agent e1 x ∧ Patient e1 e2 ∧ Detects e3 ∧ Agent e3 y ∧ Patient e3 z ∧ Binds e4 ∧ Agent e4 y ∧ Patient e4 z"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ Sites y ∧ SSDNADamage z"
  (* Hypothesis: PARP1 detects and binds to sites of SS DNA damage *)
  shows "∃x y z e1 e2. PARP1 x ∧ Sites y ∧ SSDNADamage z ∧ Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y ∧ To y z"
proof -
  (* From the known information, we have PARP1 x, Sites y, and SSDNADamage z. *)
  from asm have "PARP1 x ∧ Sites y ∧ SSDNADamage z" <ATP>
  
  (* Explanation 3 states that the synthesis of PAR by PARP1 is necessary for repair proteins to facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* Explanation 4 directly states that repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* Using the logical relation Implies(A, C), we can infer that if PARP1 synthesises PAR, then repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* Since we have PARP1 x, we can use this to infer the detection and binding. *)
  
  (* From explanation_4, we have the existence of detection and binding events facilitated by repair proteins. *)
  from explanation_4 obtain e1 e2 e3 e4 where
    "RepairProteins x ∧ PARP1 y ∧ Sites z ∧ SSDNADamage z ∧ Facilitate e1 ∧ Agent e1 x ∧ Patient e1 e2 ∧ Detects e3 ∧ Agent e3 y ∧ Patient e3 z ∧ Binds e4 ∧ Agent e4 y ∧ Patient e4 z" <ATP>
  
  (* Since we have PARP1 x, Sites y, and SSDNADamage z, we can conclude the existence of detection and binding events. *)
  then have "Detects e3 ∧ Agent e3 x ∧ Patient e3 y ∧ Binds e4 ∧ Agent e4 x ∧ Patient e4 y" <ATP>
  
  (* Therefore, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
