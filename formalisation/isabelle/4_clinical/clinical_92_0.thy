theory clinical_92_0
imports Main

begin

typedecl entity
typedecl event

consts
  PARP2 :: "entity ⇒ bool"
  Protein :: "entity ⇒ bool"
  CatalyticDomain :: "entity ⇒ bool"
  Encodes :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Contains :: "event ⇒ bool"
  Capable :: "entity ⇒ bool"
  Catalyzing :: "event ⇒ bool"
  Reaction :: "entity ⇒ bool"
  PolyADPRibosylation :: "entity ⇒ bool"
  PARP1 :: "entity ⇒ bool"
  Transferase :: "entity ⇒ bool"
  NuclearProteins :: "entity ⇒ bool"
  Modifies :: "event ⇒ bool"
  Via :: "event ⇒ entity ⇒ bool"
  Involved :: "event ⇒ bool"
  Process :: "entity ⇒ bool"
  Important :: "entity ⇒ bool"
  Recovery :: "entity ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  DNA_Damage :: "entity ⇒ bool"

(* Explanation 1: [PARP2] encodes poly(ADP-ribosyl)transferase-like 2 protein, which contains a catalytic domain. *)
axiomatization where
  explanation_1: "∃x y z e1 e2. PARP2 x ∧ Protein y ∧ CatalyticDomain z ∧ Encodes e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Contains e2 ∧ Agent e2 y ∧ Patient e2 z"

(* Explanation 2: ] capable of catalyzing a poly(ADP-ribosyl)ation reaction. *)
axiomatization where
  explanation_2: "∃x y e. Capable x ∧ Catalyzing e ∧ Agent e x ∧ Reaction y ∧ PolyADPRibosylation y ∧ Patient e y"

(* Explanation 3: PARP1 is a polyADP-ribosyl transferse which, via polyADP-riosylation, modifies nuclear proteins involved in important cellular processes including recovery from DNA damage. *)
axiomatization where
  explanation_3: "∃x y z w e1 e2 e3. PARP1 x ∧ Transferase y ∧ NuclearProteins z ∧ PolyADPRibosylation w ∧ Modifies e1 ∧ Agent e1 x ∧ Patient e1 z ∧ Via e1 w ∧ Involved e2 ∧ Agent e2 z ∧ Process e3 ∧ Important e3 ∧ Recovery e3 ∧ From e3 DNA_Damage"

theorem hypothesis:
  assumes asm: "PARP1 x ∧ PARP2 y ∧ PolyADPRibosylation z"
  (* Hypothesis: PARP1 and PARP2 are both involved in polyADP-ribosylation which is important in processes including recovery from DNA damage. *)
  shows "∃x y z e1 e2. PARP1 x ∧ PARP2 y ∧ PolyADPRibosylation z ∧ Involved e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Patient e1 z ∧ Important e2 ∧ Process e2 ∧ Recovery e2 ∧ From e2 DNA_Damage"
proof -
  (* From the premise, we have known information about PARP1, PARP2, and PolyADPRibosylation. *)
  from asm have "PARP1 x ∧ PARP2 y ∧ PolyADPRibosylation z" <ATP>
  (* Explanation 3 provides that PARP1 is a polyADP-ribosyl transferase involved in important cellular processes. *)
  (* Explanation 2 and derived implications show that PARP2 is capable of catalyzing a polyADP-ribosylation reaction. *)
  (* We can use the logical relations to infer the involvement of both PARP1 and PARP2 in polyADP-ribosylation. *)
  (* Explanation 3 also indicates that these processes include recovery from DNA damage. *)
  then have "Involved e1 ∧ Agent e1 x ∧ Agent e1 y ∧ Patient e1 z ∧ Important e2 ∧ Process e2 ∧ Recovery e2 ∧ From e2 DNA_Damage" <ATP>
  then show ?thesis <ATP>
qed

end
