theory clinical_72_5
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
  p110 :: "entity ⇒ bool"
  Mammals :: "entity ⇒ bool"
  p110α :: "entity ⇒ bool"
  OneOf :: "entity ⇒ entity ⇒ bool"
  Gene :: "entity ⇒ bool"
  PIK3CA :: "entity ⇒ bool"
  Transcribed :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Source :: "event ⇒ entity ⇒ bool"
  Transcription :: "event ⇒ bool"
  Involves :: "event ⇒ event ⇒ bool"
  ActsAsAgent :: "event ⇒ entity ⇒ bool"
  ActsAsSource :: "event ⇒ entity ⇒ bool"
  TranscriptionEvent :: "event ⇒ bool"
  Involving :: "event ⇒ entity ⇒ entity ⇒ bool"
  EssentialFor :: "event ⇒ entity ⇒ bool"
  Formation :: "entity ⇒ bool"

(* Explanation 1: PI3Ks are a family of lipids comprised of a catalytic subunit, which includes p110, and a regulatory subunit. *)
axiomatization where
  explanation_1: "∃x y z w. PI3Ks x ∧ Family y ∧ Lipids y ∧ Subunit z ∧ Catalytic z ∧ Includes z w ∧ p110 w ∧ RegulatorySubunit z"

(* Explanation 2: There are three different isoforms of the p110 subunit in mammals, and p110α is one of these isoforms. *)
axiomatization where
  explanation_2: "∃x y. Isoforms x ∧ Subunit y ∧ p110 y ∧ Mammals y ∧ p110α y ∧ OneOf x y"

(* Explanation 3: p110α is transcribed from the PIK3CA gene, and this transcription involves a specific event where p110α acts as the agent and the PIK3CA gene as the source. *)
axiomatization where
  explanation_3: "∃x y z e1 e2. p110α x ∧ Gene y ∧ PIK3CA y ∧ Transcribed e1 ∧ Agent e1 x ∧ Source e1 y ∧ Transcription e2 ∧ Involves e2 e1 ∧ ActsAsAgent e2 x ∧ ActsAsSource e2 y"

(* Explanation 4: The transcription event involving p110α and the PIK3CA gene is essential for the formation of the catalytic subunit of PI3Ks, which includes p. *)
axiomatization where
  explanation_4: "∃x y z e w. TranscriptionEvent e ∧ Involving e x y ∧ p110α x ∧ Gene y ∧ PIK3CA y ∧ EssentialFor e z ∧ Formation z ∧ Subunit z ∧ Catalytic z ∧ PI3Ks z ∧ Includes z w ∧ p110 w"

theorem hypothesis:
  assumes asm: "Subunit x ∧ PI3Ks x ∧ p110 x ∧ p110α y ∧ Gene z ∧ PIK3CA z"
  (* Hypothesis: PI3Ks catalytic subunit p110, of which p110α is transcribed from the PIK3CA gene. *)
  shows "∃x y z e. Subunit x ∧ PI3Ks x ∧ p110 x ∧ p110α y ∧ Gene z ∧ PIK3CA z ∧ Transcribed e ∧ Agent e y ∧ Source e z"
  using assms explanation_3 by auto
  

end
