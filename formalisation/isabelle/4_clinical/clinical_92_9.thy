theory clinical_92_9
imports Main

begin

typedecl entity
typedecl event

consts
  PARP2 :: "entity ⇒ bool"
  Protein :: "entity ⇒ bool"
  Encode :: "entity ⇒ entity ⇒ bool"
  Domain :: "entity ⇒ bool"
  Contains :: "entity ⇒ entity ⇒ bool"
  Catalytic :: "entity ⇒ bool"
  CapableOf :: "entity ⇒ event ⇒ bool"
  Catalyzing :: "event ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  Transferase :: "entity ⇒ bool"
  Is :: "entity ⇒ entity ⇒ bool"
  PolyADP_Ribosylation :: "entity ⇒ bool"
  Modifies :: "entity ⇒ entity ⇒ bool"
  NuclearProtein :: "entity ⇒ bool"
  InvolvedIn :: "entity ⇒ entity ⇒ bool"
  Important :: "entity ⇒ bool"
  Process :: "entity ⇒ bool"
  RecoveryFromDNA :: "entity ⇒ bool"
  Crucial :: "entity ⇒ bool"
  Modifying :: "entity ⇒ entity ⇒ bool"
  PlayRole :: "entity ⇒ entity ⇒ bool"
  RecoveryProcess :: "entity ⇒ bool"
  Contributes :: "entity ⇒ entity ⇒ bool"
  Directly :: "entity ⇒ bool"
  Essential :: "entity ⇒ entity ⇒ bool"
  Involvement :: "entity ⇒ bool"

(* Explanation 1: PARP2 encodes poly(ADP-ribosyl)transferase-like 2 protein, which contains a catalytic domain capable of catalyzing a poly(ADP-ribosyl)ation reaction. *)
axiomatization where
  explanation_1: "∃x y z e. PARP2 x ∧ Protein y ∧ Encode x y ∧ Domain z ∧ Contains y z ∧ Catalytic z ∧ CapableOf z e ∧ Catalyzing e"

(* Explanation 2: PARP1 is a polyADP-ribosyl transferase which, via polyADP-ribosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
axiomatization where
  explanation_2: "∃x y z w. PARP1 x ∧ Transferase y ∧ Is x y ∧ PolyADP_Ribosylation z ∧ Modifies x y ∧ NuclearProtein y ∧ InvolvedIn y z ∧ Important z ∧ Process w ∧ RecoveryFromDNA w"

(* Explanation 3: PolyADP-ribosylation, involving both PARP1 and PARP2, is crucial for modifying nuclear proteins that play a role in recovery from DNA damage and is important for these recovery processes. *)
axiomatization where
  explanation_3: "∃x y z w v. PolyADP_Ribosylation x ∧ PARP1 y ∧ PARP2 z ∧ InvolvedIn y x ∧ InvolvedIn z x ∧ Crucial x ∧ Modifying x w ∧ NuclearProtein w ∧ PlayRole w v ∧ RecoveryFromDNA v ∧ Important x ∧ RecoveryProcess v"

(* Explanation 4: PolyADP-ribosylation, involving both PARP1 and PARP2, directly contributes to the recovery from DNA damage by modifying nuclear proteins essential for this process. *)
axiomatization where
  explanation_4: "∃x y z w v. PolyADP_Ribosylation x ∧ PARP1 y ∧ PARP2 z ∧ InvolvedIn y x ∧ InvolvedIn z x ∧ Contributes x v ∧ Directly x ∧ Modifying x w ∧ NuclearProtein w ∧ Essential w v ∧ RecoveryFromDNA v"

(* Explanation 5: The involvement of both PARP1 and PARP2 in polyADP-ribosylation is important for recovery processes, including recovery from DNA damage. *)
axiomatization where
  explanation_5: "∃x y z v. Involvement x ∧ PARP1 y ∧ PARP2 z ∧ PolyADP_Ribosylation x ∧ Important x ∧ RecoveryProcess v ∧ RecoveryFromDNA v"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PARP2 y"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage *)
  shows "∃x y z w. PARP1 x ∧ PARP2 y ∧ PolyADP_Ribosylation z ∧ InvolvedIn x z ∧ InvolvedIn y z ∧ Important z ∧ Process w ∧ RecoveryFromDNA w"
  using explanation_2 explanation_3 by blast
  

end
