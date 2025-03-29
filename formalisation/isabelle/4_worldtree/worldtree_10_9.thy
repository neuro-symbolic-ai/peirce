theory worldtree_10_9
imports Main

begin

typedecl entity
typedecl event

consts
  Shape :: "entity ⇒ bool"
  Object :: "entity ⇒ bool"
  PropertyOf :: "entity ⇒ entity ⇒ bool"
  Classifying :: "event ⇒ bool"
  Grouping :: "event ⇒ bool"
  Objects :: "entity ⇒ bool"
  Materials :: "entity ⇒ bool"
  ByProperties :: "entity ⇒ entity ⇒ bool"
  Leaf :: "entity ⇒ bool"
  ScienceProcess :: "event ⇒ bool"
  Putting :: "event ⇒ bool"
  InDifferentGroups :: "event ⇒ bool"
  Students :: "entity ⇒ bool"
  Leaves :: "entity ⇒ bool"
  Using :: "event ⇒ bool"
  Studying :: "event ⇒ bool"
  They :: "entity ⇒ bool"
  Group :: "event ⇒ bool"
  By :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Shape is a property of an object. *)
axiomatization where
  explanation_1: "∀x y. Shape x ∧ Object y ⟶ PropertyOf x y"

(* Explanation 2: Classifying means grouping objects; materials by their properties. *)
axiomatization where
  explanation_2: "∀e1 e2 x y. Classifying e1 ⟷ (Grouping e2 ∧ Objects x ∧ Materials y ∧ ByProperties x y)"

(* Explanation 3: A leaf is a kind of object. *)
axiomatization where
  explanation_3: "∀x. Leaf x ⟶ Object x"

(* Explanation 4: Classifying is a kind of science process. *)
axiomatization where
  explanation_4: "∀x. Classifying x ⟶ ScienceProcess x"

(* Explanation 5: Grouping means putting; placing in different groups. *)
axiomatization where
  explanation_5: "∀e1 e2. Grouping e1 ⟷ (Putting e2 ∧ InDifferentGroups e2)"

theorem hypothesis:
  (* Premise 1: Students are studying some leaves. *)
  assumes asm1: "∃x y e. Students x ∧ Leaves y ∧ Studying e ∧ Agent e x ∧ Patient e y"
  (* Premise 2: They group the leaves by shape. *)
  assumes asm2: "∃x y z e. They x ∧ Leaves y ∧ Shape z ∧ Group e ∧ Agent e x ∧ Patient e y ∧ By e z"
  (* Hypothesis: The students are using the science process of classifying when they put the leaves in different groups. *)
  shows "∃x y z e1 e2. Students x ∧ ScienceProcess y ∧ Classifying y ∧ Leaves z ∧ Using e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Putting e2 ∧ Agent e2 x ∧ Patient e2 z ∧ InDifferentGroups z"
  sledgehammer
  oops

end
