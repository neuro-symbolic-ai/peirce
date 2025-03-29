theory clinical_72_2
imports Main

begin

typedecl entity
typedecl event

consts
  PI3Ks :: "entity ⇒ bool"
  Family :: "entity ⇒ bool"
  Lipids :: "entity ⇒ bool"
  Subunit :: "entity ⇒ bool"
  Catalytic :: "entity ⇒ bool"
  Includes :: "entity ⇒ entity ⇒ bool"
  p110 :: "entity ⇒ bool"
  RegulatorySubunit :: "entity ⇒ bool"
  Isoforms :: "entity ⇒ bool"
  p110Subunit :: "entity ⇒ bool"
  Mammals :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  p110α :: "entity ⇒ bool"
  OneOf :: "entity ⇒ entity ⇒ bool"
  Gene :: "entity ⇒ bool"
  PIK3CA :: "entity ⇒ bool"
  Transcribed :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Source :: "event ⇒ entity ⇒ bool"
  Event :: "event ⇒ bool"
  Involves :: "event ⇒ event ⇒ bool"
  ActsAsAgent :: "event ⇒ entity ⇒ bool"
  ActsAsSource :: "event ⇒ entity ⇒ bool"
  TranscriptionEvent :: "event ⇒ bool"
  Involving :: "event ⇒ entity ⇒ entity ⇒ bool"
  Process :: "event ⇒ bool"
  PartOf :: "event ⇒ event ⇒ bool"
  Forms :: "event ⇒ entity ⇒ bool"

(* Explanation 1: PI3Ks are a family of lipids comprised of a catalytic subunit, which includes p110, and a regulatory subunit. *)
axiomatization where
  explanation_1: "∃x y z. PI3Ks x ∧ Family y ∧ Lipids y ∧ Subunit z ∧ Catalytic z ∧ Includes y z ∧ p110 z ∧ RegulatorySubunit z"

(* Explanation 2: There are three different isoforms of the p110 subunit in mammals, and p110α is one of these isoforms. *)
axiomatization where
  explanation_2: "∃x y z. Isoforms x ∧ p110Subunit y ∧ Mammals z ∧ In x y ∧ In x z ∧ p110α y ∧ OneOf x y"

(* Explanation 3: p110α is transcribed from the PIK3CA gene, and this transcription involves a specific event where p110α acts as the agent and PIK3CA gene as the source. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. p110α x ∧ Gene y ∧ PIK3CA y ∧ Transcribed e1 ∧ Agent e1 x ∧ Source e1 y ∧ Event e2 ∧ Involves e2 e1 ∧ ActsAsAgent e2 x ∧ ActsAsSource e2 y"

(* Explanation 4: The transcription event involving p110α and the PIK3CA gene is part of the process that forms the catalytic subunit of PI3Ks. *)
axiomatization where
  explanation_4: "∃x y z e1 e2. TranscriptionEvent e1 ∧ Involving e1 x y ∧ p110α x ∧ Gene y ∧ PIK3CA y ∧ Process e2 ∧ PartOf e1 e2 ∧ Forms e2 z ∧ Subunit z ∧ Catalytic z ∧ PI3Ks z"

theorem hypothesis:
  assumes asm: "p110α y ∧ Gene z ∧ PIK3CA z"
  (* Hypothesis: PI3Ks catalytic subunit p110, of which p110α is transcribed from the PIK3CA gene *)
  shows "∃x y z e. Subunit x ∧ PI3Ks x ∧ p110 x ∧ p110α y ∧ Gene z ∧ PIK3CA z ∧ Transcribed e ∧ Agent e y ∧ Source e z"
proof -
  (* From the premise, we have known information about p110α and the PIK3CA gene. *)
  from asm have "p110α y ∧ Gene z ∧ PIK3CA z" by blast
  (* Explanation 3 provides that p110α is transcribed from the PIK3CA gene, involving a specific event. *)
  (* This matches with logical proposition D and E. *)
  then obtain e where "Transcribed e ∧ Agent e y ∧ Source e z" sledgehammer
  (* Explanation 4 states that the transcription event is part of the process that forms the catalytic subunit of PI3Ks. *)
  (* This matches with logical proposition F. *)
  then obtain x where "Subunit x ∧ Catalytic x ∧ PI3Ks x ∧ p110 x" <ATP>
  (* Combine all the information to satisfy the hypothesis. *)
  then show ?thesis <ATP>
qed

end
