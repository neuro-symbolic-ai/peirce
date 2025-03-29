theory clinical_72_0
imports Main


begin

typedecl entity
typedecl event

consts
  PI3Ks :: "entity ⇒ bool"
  Family :: "entity ⇒ bool"
  Lipids :: "entity ⇒ bool"
  Comprised :: "entity ⇒ bool"
  Catalytic :: "entity ⇒ bool"
  Regulatory :: "entity ⇒ bool"
  Name :: "entity ⇒ entity ⇒ bool"
  Of :: "entity ⇒ entity ⇒ bool"
  Isoforms :: "entity ⇒ bool"
  Number :: "entity ⇒ bool"
  Three :: "entity ⇒ bool"
  Subunit :: "entity ⇒ bool"
  Mammals :: "entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Transcribed :: "entity ⇒ bool"
  Genes :: "entity ⇒ bool"
  PIK3CA :: "entity ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  TranscribedFrom :: "entity ⇒ entity ⇒ bool"

(* Explanation 1: PI3Ks are a family of lipids comprised of a catalytic (p100) and regulatory (p85) subunit *)
axiomatization where
  explanation_1: "∀x y z. PI3Ks x ∧ Family y ∧ Lipids y ∧ Comprised z ∧ Catalytic z ∧ Name z p100 ∧ Regulatory z p85 ∧ Of x y ∧ Of x z"

(* Explanation 2: There are three different isoforms of the p110 subunit in mammals *)
axiomatization where
  explanation_2: "∃x y z. Isoforms x ∧ Number y ∧ Three y ∧ Subunit z ∧ Name z p110 ∧ Mammals z ∧ In x z ∧ Of x y"

(* Explanation 3: p110α… transcribed from the genes PIK3CA *)
axiomatization where
  explanation_3: "∃x y z. Subunit x ∧ Name x p110α ∧ Transcribed y ∧ Genes z ∧ PIK3CA z ∧ From y z ∧ TranscribedFrom x y"


theorem hypothesis:
 assumes asm: "PI3Ks x ∧ Subunit y ∧ Transcribed z ∧ Source z PIK3CA"
  (* Hypothesis: PI3Ks catalytic subunit p110, of which p110α is transcribed from the PIK3CA gene *)
 shows "∃x y z. PI3Ks x ∧ Subunit y ∧ Catalytic y ∧ Name y p110 ∧ Transcribed z ∧ Source z PIK3CA ∧ From z y ∧ TranscribedFrom x z ∧ TranscribedTo x p110α"
proof -
  (* From the premise, we have the information about PI3Ks, Subunit, and Transcribed related to the gene PIK3CA. *)
  from asm have "PI3Ks x ∧ Subunit y ∧ Transcribed z ∧ Source z PIK3CA" <ATP>
  (* We have the explanatory sentence 1 stating that PI3Ks are comprised of a catalytic subunit. *)
  (* There is a logical relation Implies(A, B), Implies(PI3Ks are a family of lipids comprised of a catalytic subunit, PI3Ks are comprised of a catalytic subunit) *)
  (* We can infer that the Subunit y is Catalytic. *)
  then have "PI3Ks x ∧ Subunit y ∧ Catalytic y" <ATP>
  (* We also have the explanatory sentence 3 stating that p110α is transcribed from the gene PIK3CA. *)
  (* There is a logical relation Implies(C, B), Implies(p110α is transcribed from the gene PIK3CA, There are three different isoforms of the p110 subunit in mammals) *)
  (* We can infer that the Subunit y is named p110. *)
  then have "PI3Ks x ∧ Subunit y ∧ Catalytic y ∧ Name y p110" <ATP>
  (* We have the information about Transcribed z and Source z PIK3CA. *)
  (* There is a logical relation Implies(C, C), Implies(p110α is transcribed from the gene PIK3CA, p110α is transcribed from the gene PIK3CA) *)
  (* We can infer that the Transcribed z is related to the gene PIK3CA. *)
  then have "PI3Ks x ∧ Subunit y ∧ Catalytic y ∧ Name y p110 ∧ Transcribed z ∧ Source z PIK3CA" <ATP>
  (* We have the explanatory sentence 3 stating that p110α is transcribed from the gene PIK3CA. *)
  (* There is a logical relation Implies(C, C), Implies(p110α is transcribed from the gene PIK3CA, p110α is transcribed from the gene PIK3CA) *)
  (* We can infer that the Transcribed z is TranscribedFrom x z. *)
  then have "PI3Ks x ∧ Subunit y ∧ Catalytic y ∧ Name y p110 ∧ Transcribed z ∧ Source z PIK3CA ∧ TranscribedFrom x z" <ATP>
  (* We have the explanatory sentence 3 stating that p110α is transcribed from the gene PIK3CA. *)
  (* There is a logical relation Implies(C, C), Implies(p110α is transcribed from the gene PIK3CA, p110α is transcribed from the gene PIK3CA) *)
  (* We can infer that the Subunit y is TranscribedTo x p110α. *)
  then have "PI3Ks x ∧ Subunit y ∧ Catalytic y ∧ Name y p110 ∧ Transcribed z ∧ Source z PIK3CA ∧ TranscribedFrom x z ∧ TranscribedTo x p110α" <ATP>
  then show ?thesis <ATP>
qed

end
