theory esnli_8_2
imports Main

begin

typedecl entity
typedecl event

consts
  Man :: "entity ⇒ bool"
  Sidewalk :: "entity ⇒ bool"
  Dirty :: "entity ⇒ bool"
  On :: "entity ⇒ entity ⇒ bool"
  FoundOutdoors :: "entity ⇒ bool"
  Outside :: "entity ⇒ bool"
  OldMan :: "entity ⇒ bool"
  HardwareParts :: "entity ⇒ bool"
  Sells :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The man is on a dirty sidewalk. *)
axiomatization where
  explanation_1: "∃x y. Man x ∧ Sidewalk y ∧ Dirty y ∧ On x y"

(* Explanation 2: Sidewalks are found outdoors. *)
axiomatization where
  explanation_2: "∀x. Sidewalk x ⟶ FoundOutdoors x"

(* Explanation 3: If a man is on a sidewalk and sidewalks are outdoors, then the man is outside. *)
axiomatization where
  explanation_3: "∀x y. (Man x ∧ Sidewalk y ∧ On x y ∧ FoundOutdoors y) ⟶ Outside x"

(* Explanation 4: An old man is a man. *)
axiomatization where
  explanation_4: "∀x. OldMan x ⟶ Man x"

theorem hypothesis:
  (* Premise: An old man sells hardware parts on a dirty sidewalk. *)
  assumes asm: "OldMan x ∧ HardwareParts y ∧ Sidewalk z ∧ Dirty z ∧ Sells e ∧ Agent e x ∧ Patient e y ∧ On x z"
  (* Hypothesis: The man is outside. *)
  shows "∀x. Man x ⟶ Outside x"
proof -
  (* From the premise, we have information about an old man, hardware parts, and a dirty sidewalk. *)
  from asm have "OldMan x ∧ Sidewalk z ∧ Dirty z ∧ On x z" by auto
  (* Using explanation_4, we know that an old man is a man. *)
  then have "Man x" using explanation_4 by blast
  (* From explanation_2, we know that sidewalks are found outdoors. *)
  have "FoundOutdoors z" using assms explanation_2 by auto
  (* Now, we can use explanation_3 which states that if a man is on a sidewalk and sidewalks are outdoors, then the man is outside. *)
  then have "Outside x" using \<open>Man x\<close> assms explanation_3 by blast
  then show ?thesis sledgehammer
qed

end
