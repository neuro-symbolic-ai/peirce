theory esnli_8_3
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
  OldMan :: "entity ⇒ bool"
  HardwareParts :: "entity ⇒ bool"
  Sells :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"

(* Explanation 1: The man is on a dirty sidewalk. *)
axiomatization where
  explanation_1: "∃x y. Man x ∧ Sidewalk y ∧ Dirty y ∧ On x y"

(* Explanation 2: If a specific sidewalk is dirty, it is found outdoors. *)
axiomatization where
  explanation_2: "∀y. (Sidewalk y ∧ Dirty y) ⟶ Outdoors y"

(* Explanation 3: If a man is on a sidewalk and that sidewalk is outdoors, then the man is outside. *)
axiomatization where
  explanation_3: "∀x y. (Man x ∧ Sidewalk y ∧ On x y ∧ Outdoors y) ⟶ Outside x"

(* Explanation 4: An old man is a man. *)
axiomatization where
  explanation_4: "∀x. OldMan x ⟶ Man x"

theorem hypothesis:
  (* Premise: An old man sells hardware parts on a dirty sidewalk. *)
  assumes asm: "OldMan x ∧ HardwareParts y ∧ Sidewalk z ∧ Dirty z ∧ Sells e ∧ Agent e x ∧ Patient e y ∧ On x z"
  (* Hypothesis: The man is outside. *)
  shows "∀x. Man x ⟶ Outside x"
proof -
  (* From the premise, we have information about an old man, hardware parts, a sidewalk, and the fact that the sidewalk is dirty. *)
  from asm have "OldMan x ∧ Sidewalk z ∧ Dirty z ∧ On x z" by auto
  
  (* Explanation 4 tells us that an old man is a man. *)
  from explanation_4 and `OldMan x` have "Man x" by (simp add: \<open>OldMan x \<and> Sidewalk z \<and> Dirty z \<and> On x z\<close> explanation_4)
  
  (* Explanation 2 states that if a sidewalk is dirty, it is found outdoors. *)
  from explanation_2 and `Sidewalk z ∧ Dirty z` have "Outdoors z" by (simp add: \<open>OldMan x \<and> Sidewalk z \<and> Dirty z \<and> On x z\<close> explanation_2)
  
  (* Explanation 3 states that if a man is on a sidewalk and that sidewalk is outdoors, then the man is outside. *)
  from explanation_3 and `Man x ∧ Sidewalk z ∧ On x z ∧ Outdoors z` have "Outside x" using \<open>Man x\<close> \<open>OldMan x \<and> Sidewalk z \<and> Dirty z \<and> On x z\<close> \<open>Outdoors z\<close> explanation_3 by blast
  
  then show ?thesis sledgehammer
qed

end
