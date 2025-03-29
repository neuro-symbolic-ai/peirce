theory clinical_19_10
imports Main


begin

typedecl entity
typedecl event

consts
  Dasatinib :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  Effective :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Access :: "event ⇒ bool"
  OffLicence :: "event ⇒ bool"
  ForPatient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: If Dasatinib is effective in treating a specific patient, then it will need to be accessed off licence for that patient. *)
axiomatization where
  explanation_1: "∀x y e1 e2. Dasatinib x ∧ Patient y ∧ Effective e1 ∧ Agent e1 x ∧ Patient e2 ⟶ (Access e2 ∧ OffLicence e2 ∧ ForPatient e2 y)"


theorem hypothesis:
 assumes asm: "Dasatinib x ∧ Effective e1 ∧ Agent e1 x ∧ Patient y"
  (* Hypothesis: Dasatinib will need to be accessed off licence. *)
 shows "∃x e. Dasatinib x ∧ Access e ∧ OffLicence e"
proof -
  (* From the premise, we have the information about Dasatinib, Effective, Agent, and Patient. *)
  from asm have "Dasatinib x ∧ Effective e1 ∧ Agent e1 x ∧ Patient y" <ATP>
  (* There is an explanatory sentence that connects Dasatinib being effective and needing to be accessed off licence. *)
  (* We can apply the implication Implies(A, B) where A is Dasatinib is effective in treating a specific patient and B is Dasatinib needs to be accessed off licence for that patient. *)
  (* Given that Dasatinib x ∧ Effective e1, we can infer that Dasatinib needs to be accessed off licence. *)
  then have "Dasatinib x ∧ Access e2 ∧ OffLicence e2" for e2
  (* We found the required x and e, so the hypothesis is proven. *)
  then show ?thesis <ATP>
qed

end
