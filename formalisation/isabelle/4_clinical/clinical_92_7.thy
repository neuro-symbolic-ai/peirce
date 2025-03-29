theory clinical_92_7
imports Main

begin

typedecl entity
typedecl event

consts
  PARP2 :: "entity ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  Protein :: "entity ⇒ bool"
  Encodes :: "entity ⇒ entity ⇒ bool"
  Domain :: "entity ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"
  Catalytic :: "entity ⇒ bool"
  CapableOf :: "entity ⇒ event ⇒ bool"
  Transferase :: "entity ⇒ bool"
  NuclearProtein :: "entity ⇒ bool"
  PolyADP_Ribosylation :: "entity ⇒ bool"
  Is :: "entity ⇒ entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Via :: "event ⇒ entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  CellularProcess :: "entity ⇒ bool"
  Important :: "entity ⇒ bool"
  RecoveryFromDNA :: "entity ⇒ bool"
  Crucial :: "entity ⇒ bool"
  Modifying :: "event ⇒ bool"
  Play :: "event ⇒ bool"
  Role :: "event ⇒ bool"
  In :: "event ⇒ entity ⇒ bool"
  RecoveryProcess :: "entity ⇒ bool"
  Contributes :: "event ⇒ bool"
  Directly :: "event ⇒ bool"
  Essential :: "entity ⇒ entity ⇒ bool"
  Process :: "entity ⇒ bool"

(* Explanation 1: PARP2 encodes poly(ADP-ribosyl)transferase-like 2 protein, which contains a catalytic domain capable of catalyzing a poly(ADP-ribosyl)ation reaction. *)
axiomatization where
  explanation_1: "∃x y z. PARP2 x ∧ Protein y ∧ Encodes x y ∧ Domain z ∧ Contains y z ∧ Catalytic z ∧ CapableOf z Catalyzing"

(* Explanation 2: PARP1 is a polyADP-ribosyl transferase which, via polyADP-ribosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
axiomatization where
  explanation_2: "∃x y z w e. PARP1 x ∧ Transferase y ∧ NuclearProtein z ∧ PolyADP_Ribosylation w ∧ Is x y ∧ Modifies e ∧ Agent e x ∧ Patient e z ∧ Via e w ∧ InvolvedIn z y ∧ Important y ∧ RecoveryFromDNA y"

(* Explanation 3: PolyADP-ribosylation, involving both PARP1 and PARP2, is crucial for modifying nuclear proteins that play a role in recovery from DNA damage and is important for these recovery processes. *)
axiomatization where
  explanation_3: "∃x y z e1 e2 w. PolyADP_Ribosylation x ∧ PARP1 y ∧ PARP2 z ∧ InvolvedIn y x ∧ InvolvedIn z x ∧ Crucial x ∧ Modifying e1 ∧ NuclearProtein w ∧ Agent e1 x ∧ Patient e1 w ∧ Play e2 ∧ Role e2 ∧ In e2 w ∧ Important x ∧ RecoveryProcess w"

(* Explanation 4: PolyADP-ribosylation, involving both PARP1 and PARP2, directly contributes to the recovery from DNA damage by modifying nuclear proteins essential for this process. *)
axiomatization where
  explanation_4: "∃x y z e1 e2 w. PolyADP_Ribosylation x ∧ PARP1 y ∧ PARP2 z ∧ InvolvedIn y x ∧ InvolvedIn z x ∧ Contributes e1 ∧ Agent e1 x ∧ Patient e1 w ∧ Directly e1 ∧ Modifying e2 ∧ NuclearProtein w ∧ Agent e2 x ∧ Patient e2 w ∧ Essential w z"

(* Explanation 5: The involvement of both PARP1 and PARP2 in polyADP-ribosylation is important for recovery processes, including recovery from DNA damage. *)
axiomatization where
  explanation_5: "∃x y z w. PARP1 x ∧ PARP2 y ∧ PolyADP_Ribosylation z ∧ InvolvedIn x z ∧ InvolvedIn y z ∧ Important z ∧ RecoveryProcess w ∧ RecoveryFromDNA w ∧ In e w ∧ Process w"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PARP2 y ∧ PolyADP_Ribosylation z"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage *)
  shows "∃x y z w. PARP1 x ∧ PARP2 y ∧ PolyADP_Ribosylation z ∧ InvolvedIn x z ∧ InvolvedIn y z ∧ Important z ∧ Process w ∧ RecoveryFromDNA w ∧ In w z"
  sledgehammer
  oops

end
