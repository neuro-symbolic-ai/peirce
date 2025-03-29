theory clinical_72_4
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
  RegulatorySubunit :: "entity ⇒ bool"
  Isoforms :: "entity ⇒ bool"
  ThreeDifferent :: "entity ⇒ bool"
  p110 :: "entity ⇒ bool"
  Mammals :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  p110α :: "entity ⇒ bool"
  IsoformOf :: "entity ⇒ entity ⇒ bool"
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
  Essential :: "event ⇒ bool"
  Formation :: "entity ⇒ bool"

(* Explanation 1: PI3Ks are a family of lipids comprised of a catalytic subunit, which includes p110, and a regulatory subunit *)
axiomatization where
  explanation_1: "∃x y z. PI3Ks x ∧ Family x ∧ Lipids y ∧ Subunit z ∧ Catalytic z ∧ Includes z x ∧ RegulatorySubunit z"

(* Explanation 2: There are three different isoforms of the p110 subunit in mammals, and p110α is one of these isoforms *)
axiomatization where
  explanation_2: "∃x y z. Isoforms x ∧ ThreeDifferent x ∧ Subunit y ∧ p110 y ∧ Mammals z ∧ In x z ∧ p110α y ∧ IsoformOf y x"

(* Explanation 3: p110α is transcribed from the PIK3CA gene, and this transcription involves a specific event where p110α acts as the agent and the PIK3CA gene as the source *)
axiomatization where
  explanation_3: "∃x y z e1 e2. p110α x ∧ Gene y ∧ PIK3CA y ∧ Transcribed e1 ∧ Agent e1 x ∧ Source e1 y ∧ Event e2 ∧ Involves e2 e1 ∧ ActsAsAgent e2 x ∧ ActsAsSource e2 y"

(* Explanation 4: The transcription event involving p110α and the PIK3CA gene is essential for the formation of the catalytic subunit of PI3Ks, which includes p *)
axiomatization where
  explanation_4: "∃x y z e. TranscriptionEvent e ∧ Involves e x ∧ Involves e y ∧ p110α z ∧ Gene z ∧ PIK3CA z ∧ Essential e ∧ Formation z ∧ Subunit z ∧ Catalytic z ∧ PI3Ks z ∧ Includes z y"

theorem hypothesis:
  assumes asm: "p110α y ∧ Gene z ∧ PIK3CA z"
  (* Hypothesis: PI3Ks catalytic subunit p110, of which p110α is transcribed from the PIK3CA gene *)
  shows "∃x y z e. Subunit x ∧ PI3Ks x ∧ p110 x ∧ p110α y ∧ Gene z ∧ PIK3CA z ∧ Transcribed e ∧ Agent e y ∧ Source e z"
proof -
  (* From the premise, we have known information about p110α, Gene, and PIK3CA. *)
  from asm have "p110α y ∧ Gene z ∧ PIK3CA z" <ATP>
  (* Explanation 3 provides the transcription event involving p110α and the PIK3CA gene. *)
  (* We can use this to infer the existence of a transcription event e where p110α acts as the agent and PIK3CA as the source. *)
  from explanation_3 obtain e where "Transcribed e ∧ Agent e y ∧ Source e z" <ATP>
  (* Explanation 4 states that this transcription event is essential for the formation of the catalytic subunit of PI3Ks. *)
  (* Therefore, we can infer the existence of a subunit x that is part of PI3Ks and includes p110. *)
  from explanation_4 obtain x where "Subunit x ∧ PI3Ks x ∧ p110 x" <ATP>
  (* Combining all the information, we can conclude the hypothesis. *)
  then show ?thesis <ATP>
qed

end
