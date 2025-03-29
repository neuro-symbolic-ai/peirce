theory clinical_72_3
imports Main


begin

typedecl entity
typedecl event

consts
  TranscriptionOfP110α :: "entity ⇒ bool"
  From :: "entity ⇒ entity ⇒ bool"
  PIK3CAGene :: "entity"
  PI3KsCatalyticSubunitP110 :: "entity ⇒ bool"
  Transcribed :: "entity ⇒ bool"
  Source :: "entity ⇒ entity ⇒ bool"
  Transcriber :: "entity ⇒ entity ⇒ entity ⇒ bool"
  p110α :: "entity"

(* Explanation 1: The transcription of p110α is from the PIK3CA gene *)
axiomatization where
  explanation_1: "∃x y. TranscriptionOfP110α x ∧ From x PIK3CAGene"


theorem hypothesis:
 assumes asm: "PI3KsCatalyticSubunitP110(x) ∧ Transcribed(z) ∧ Source z PIK3CAGene ∧ Transcriber z x p110α"
  (* Hypothesis: PI3Ks catalytic subunit p110, of which p110α is transcribed from the PIK3CA gene *)
 shows "∃x y z. PI3KsCatalyticSubunitP110(x) ∧ Transcribed(z) ∧ Source z PIK3CAGene ∧ Transcriber z x p110α"
  using assms by blast
  

end
