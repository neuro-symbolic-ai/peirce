theory clinical_19_1
imports Main


begin

typedecl entity
typedecl event

consts
  Medicine :: "entity ⇒ bool"
  Patient :: "entity ⇒ bool"
  Effective :: "event ⇒ bool"
  Treat :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Need :: "event ⇒ bool"
  Will :: "event ⇒ bool"
  Access :: "event ⇒ bool"
  OffLicence :: "event ⇒ bool"
  For :: "event ⇒ entity ⇒ bool"

(* Explanation 1: If a medicine is effective in treating a specific patient, then it will need to be accessed off licence for that patient. *)
axiomatization where
  explanation_1: "∀x y z e1 e2. Medicine x ∧ Patient y ∧ Effective e1 ∧ Treat e1 ∧ Agent e1 x ∧ Patient e2 y ⟶ (Need e2 ∧ Will e2 ∧ Access e2 ∧ OffLicence e2 ∧ For e2 y)"


theorem hypothesis:
 assumes asm: "Medicine Dasatinib"
  (* Hypothesis: Dasatinib will need to be accessed off licence. *)
 shows "∃e. Need e ∧ Will e ∧ Access e ∧ OffLicence e ∧ Medicine Dasatinib"
proof -
  (* From the known information, we have Medicine Dasatinib. *)
  from asm have "Medicine Dasatinib" <ATP>
  (* There is an explanatory sentence stating Implies(A, B), which is Implies(a medicine is effective in treating a specific patient, the medicine will need to be accessed off licence for that patient). *)
  (* Since we have Medicine Dasatinib, we can infer the need for accessing off licence. *)
  then have "Need e ∧ Will e ∧ Access e ∧ OffLicence e ∧ Medicine Dasatinib" <ATP>
  then show ?thesis <ATP>
qed

end
