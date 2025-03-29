theory worldtree_5_0
imports Main

begin

typedecl entity
typedecl event

consts
  Mouse :: "entity ⇒ bool"
  Animal :: "entity ⇒ bool"
  Consumer :: "entity ⇒ bool"
  Producers :: "entity ⇒ bool"
  FoodChainProcess :: "event ⇒ bool"
  HasRole :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  Eat :: "event ⇒ bool"
  GreenPlants :: "entity ⇒ bool"
  Producer :: "entity ⇒ bool"
  Food :: "entity ⇒ bool"
  Energy :: "entity ⇒ bool"
  Source :: "entity ⇒ entity ⇒ bool"
  Eating :: "event ⇒ bool"
  Nutrients :: "entity ⇒ bool"
  Animals :: "entity ⇒ bool"
  LivingThings :: "entity ⇒ bool"
  Used :: "event ⇒ bool"
  Purpose :: "event ⇒ entity ⇒ bool"
  Require :: "event ⇒ bool"
  Survival :: "entity"
  LivingThing :: "entity ⇒ bool"
  Organism :: "entity ⇒ bool"
  Receive :: "event ⇒ bool"
  Get :: "event ⇒ bool"
  Herbivores :: "entity ⇒ bool"
  Plants :: "entity ⇒ bool"
  Herbivore :: "entity ⇒ bool"
  MeadowEcosystem :: "event ⇒ bool"
  In :: "entity ⇒ event ⇒ bool"

(* Explanation 1: a mouse is a kind of animal. *)
axiomatization where
  explanation_1: "∀x. Mouse x ⟶ Animal x"

(* Explanation 2: In the food chain process an animal has the role of consumer which eats producers; other animals for food. *)
axiomatization where
  explanation_2: "∀x y z e1 e2. Animal x ∧ Consumer y ∧ Producers z ∧ FoodChainProcess e1 ∧ HasRole e1 ∧ Agent e1 x ∧ Patient e1 y ∧ Eat e2 ∧ Agent e2 x ∧ Patient e2 z"

(* Explanation 3: green plants are a kind of producer. *)
axiomatization where
  explanation_3: "∀x. GreenPlants x ⟶ Producer x"

(* Explanation 4: food is a source of energy for animals; plants. *)
axiomatization where
  explanation_4: "∀x y. Food x ∧ Energy y ⟶ Source x y"

(* Explanation 5: eating; taking in food is used to get nutrients; energy by animals; living things. *)
axiomatization where
  explanation_5: "∀x y z e1 e2. Eating e1 ∧ Food x ∧ Nutrients y ∧ Energy z ∧ Animals e2 ∧ LivingThings e2 ∧ Used e1 ∧ Purpose e1 y ∧ Purpose e1 z ∧ Agent e1 e2"

(* Explanation 6: living things all require energy for survival. *)
axiomatization where
  explanation_6: "∀x y e. LivingThings x ∧ Energy y ∧ Require e ∧ Agent e x ∧ Patient e y ∧ Purpose e Survival"

(* Explanation 7: an animal is a kind of living thing. *)
axiomatization where
  explanation_7: "∀x. Animal x ⟶ LivingThing x"

(* Explanation 8: if an organism eats something then that something is a source of food to that organism. *)
axiomatization where
  explanation_8: "∀x y e. Organism x ∧ Eat e ∧ Agent e x ∧ Patient e y ⟶ Source y x"

(* Explanation 9: receive means get. *)
axiomatization where
  explanation_9: "∀e1 e2. Receive e1 ⟷ Get e2"

(* Explanation 10: herbivores only eat plants. *)
axiomatization where
  explanation_10: "∀x y e. Herbivores x ∧ Plants y ∧ Eat e ∧ Agent e x ∧ Patient e y"

(* Explanation 11: a mouse is a kind of herbivore. *)
axiomatization where
  explanation_11: "∀x. Mouse x ⟶ Herbivore x"

theorem hypothesis:
  assumes asm: "Mouse x ∧ Energy y ∧ Plants z ∧ MeadowEcosystem e"
  (* Hypothesis: In a meadow ecosystem, mice receive most of the energy they need to survive directly from plants. *)
  shows "∃x y z e. Mouse x ∧ Energy y ∧ Plants z ∧ MeadowEcosystem e ∧ Receive e ∧ Agent e x ∧ Patient e y ∧ Source e z ∧ In x e"
  sledgehammer
  oops

end
