theory clinical_54_8
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
  NecessaryFor :: "entity ⇒ entity ⇒ bool"
  Recruitment :: "entity ⇒ entity ⇒ entity"
  Recruited :: "entity ⇒ entity ⇒ entity ⇒ bool"
  Facilitate :: "event ⇒ bool"
  Detection :: "event ⇒ bool"
  Binds :: "event ⇒ bool"
  Sites :: "entity ⇒ bool"
  SSDNADamage :: "entity ⇒ bool"

(* Explanation 1: PARP1 synthesises PAR *)
axiomatization where
  explanation_1: "∃x y e. PARP1 x ∧ PAR y ∧ Synthesises e ∧ Agent e x ∧ Patient e y"

(* Explanation 2: PAR is necessary for the recruitment of repair proteins to damaged DNA sites *)
axiomatization where
  explanation_2: "∀x y z. PAR x ∧ RepairProteins y ∧ DamagedDNASites z ⟶ NecessaryFor x (Recruitment y z)"

(* Explanation 3: Repair proteins, once recruited to damaged DNA sites by PAR, directly facilitate the detection and binding of PARP1 to sites of SS DNA damage *)
axiomatization where
  explanation_3: "∃x y z w e1 e2. RepairProteins x ∧ DamagedDNASites y ∧ PAR z ∧ Sites w ∧ SSDNADamage w ∧ Recruited x y z ∧ Facilitate e1 ∧ Agent e1 x ∧ Detection e2 ∧ Binds e2 ∧ Agent e2 z ∧ Patient e2 w"

(* Explanation 4: The synthesis of PAR by PARP1 is necessary for repair proteins to be recruited to damaged DNA sites, which in turn facilitates the detection and binding of PARP1 to sites of SS DNA damage *)
axiomatization where
  explanation_4: "∃x y z w e1 e2 e3. PAR x ∧ PARP1 y ∧ RepairProteins z ∧ DamagedDNASites w ∧ Sites w ∧ SSDNADamage w ∧ Synthesises e1 ∧ Agent e1 y ∧ Patient e1 x ∧ NecessaryFor x (Recruitment z w) ∧ Facilitate e2 ∧ Agent e2 z ∧ Detection e3 ∧ Binds e3 ∧ Agent e3 y ∧ Patient e3 w"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ Sites y ∧ SSDNADamage y"
  (* Hypothesis: PARP1 detects and binds to sites of SS DNA damage *)
  shows "∃x y e1 e2. PARP1 x ∧ Sites y ∧ SSDNADamage y ∧ Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y"
proof -
  (* From the known information, we have PARP1 x, Sites y, and SSDNADamage y. *)
  from asm have "PARP1 x ∧ Sites y ∧ SSDNADamage y" by simp
  (* Explanation 4 states that the synthesis of PAR by PARP1 is necessary for repair proteins to be recruited to damaged DNA sites, which facilitates detection and binding. *)
  (* This implies that if PARP1 synthesises PAR, then repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage. *)
  (* We have the logical relation Implies(A, D), which is Implies(PARP1 synthesises PAR, Repair proteins facilitate the detection and binding of PARP1 to sites of SS DNA damage). *)
  (* From explanation_4, we can infer that PARP1 detects and binds to sites of SS DNA damage. *)
  then have "∃e1 e2. Detects e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Binds e2 ∧ Agent e2 x ∧ Patient e2 y" sledgehammer
  then show ?thesis <ATP>
qed

end
