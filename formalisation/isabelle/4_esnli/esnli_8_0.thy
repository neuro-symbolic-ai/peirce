theory esnli_8_0
imports Main

begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Sidewalk :: "entity ⇒ bool"
  Dirty :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  Outdoors :: "entity ⇒ bool"
  Outside :: "entity ⇒ bool"
  Old :: "entity ⇒ bool"
  HardwareParts :: "entity ⇒ bool"
  Sells :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The man is on a dirty sidewalk. *)
axiomatization where
  explanation_1: "∃x y. Man x ∧ Sidewalk y ∧ Dirty y ∧ On x y"

(* Explanation 2: Sidewalks are found outdoors, therefore, the man is outside. *)
axiomatization where
  explanation_2: "∀x. Sidewalk x ⟶ Outdoors x ∧ (∃y. Man y ∧ On y x ⟶ Outside y)"

theorem hypothesis:
  (* Premise: An old man sells hardware parts on a dirty sidewalk. *)
  assumes asm: "Man x ∧ Old x ∧ HardwareParts y ∧ Sidewalk z ∧ Dirty z ∧ Sells e ∧ Agent e x ∧ Patient e y ∧ On x z"
  (* Hypothesis: The man is outside. *)
  shows "∀x. Man x ⟶ Outside x"
proof -
  (* From the premise, we have the known information about the man, sidewalk, and the event of selling. *)
  from asm have "Man x ∧ Sidewalk z ∧ On x z" by auto
  (* Explanation 1 provides that the man is on a dirty sidewalk. *)
  (* Explanation 2 provides the logical relation Implies(A, C), Implies(the man is on a dirty sidewalk, the man is outside). *)
  (* We can use this to infer that the man is outside. *)
  then have "Outside x" sledgehammer
  then show ?thesis <ATP>
qed

end
