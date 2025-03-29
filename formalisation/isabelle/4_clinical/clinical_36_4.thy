theory clinical_36_4
imports Main

begin

typedecl entity
typedecl event

consts
  Mutations :: "entity ⇒ bool"
  CTNNB1 :: "entity ⇒ bool"
  BetaCatenin :: "entity ⇒ bool"
  Cells :: "entity ⇒ bool"
  Accumulation :: "entity ⇒ bool"
  Lead :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  Patient :: "event ⇒ entity ⇒ bool"
  In :: "entity ⇒ entity ⇒ bool"
  Present :: "event ⇒ bool"
  GeneExpression :: "event ⇒ bool"
  CyclinD1 :: "event ⇒ bool"
  Activation :: "event ⇒ bool"
  Result :: "event ⇒ bool"
  Necessary :: "event ⇒ bool"
  Proliferation :: "entity ⇒ bool"
  Promote :: "event ⇒ bool"
  Contribute :: "event ⇒ bool"
  Accumulate :: "event ⇒ bool"
  Via :: "event ⇒ entity ⇒ bool"

(* Explanation 1: Activating mutations of CTNNB1 directly lead to the accumulation of β-catenin in the same specific cells where CTNNB1 is present. *)
axiomatization where
  explanation_1: "∃x y z w e1 e2. Mutations x ∧ CTNNB1 y ∧ BetaCatenin z ∧ Cells w ∧ Accumulation z ∧ Lead e1 ∧ Agent e1 x ∧ Patient e1 z ∧ In z w ∧ Present e2 ∧ Agent e2 y ∧ In y w"

(* Explanation 2: The accumulation of β-catenin in these cells results in the activation of gene expression, including cyclin D1, which is necessary for the proliferation of those cells. *)
axiomatization where
  explanation_2: "∃x y z e1 e2. Accumulation x ∧ BetaCatenin y ∧ Cells z ∧ GeneExpression e1 ∧ CyclinD1 e1 ∧ Activation e1 ∧ Result e2 ∧ Agent e2 x ∧ Patient e2 z ∧ Necessary e1 ∧ Proliferation z"

(* Explanation 3: The accumulation of β-catenin directly contributes to the proliferation of cells by promoting the activation of cyclin D1 expression. *)
axiomatization where
  explanation_3: "∃x y z e1 e2 e3. Accumulation x ∧ BetaCatenin y ∧ Cells z ∧ Proliferation z ∧ CyclinD1 e1 ∧ Activation e1 ∧ Promote e2 ∧ Agent e2 y ∧ Patient e2 z ∧ Contribute e3 ∧ Agent e3 x ∧ Patient e3 z"

(* Explanation 4: The activation of cyclin D1 expression by β-catenin specifically promotes the proliferation of cells where β-catenin accumulates. *)
axiomatization where
  explanation_4: "∃x y z w e1 e2. Activation x ∧ CyclinD1 y ∧ BetaCatenin z ∧ Cells w ∧ Proliferation w ∧ Promote e1 ∧ Agent e1 z ∧ Patient e1 w ∧ Accumulate e2 ∧ Agent e2 z ∧ In z w"

theorem hypothesis:
  assumes asm: "Mutations x ∧ CTNNB1 y ∧ Cells z ∧ BetaCatenin y"
  (* Hypothesis: Activating mutations of CTNNB1 promote proliferation of cells via β-catenin. *)
  shows "∃x y z e. Mutations x ∧ CTNNB1 y ∧ Cells z ∧ Proliferation z ∧ BetaCatenin y ∧ Promote e ∧ Agent e x ∧ Patient e z ∧ Via e y"
proof -
  (* From the premise, we have known information about mutations, CTNNB1, cells, and β-catenin. *)
  from asm have "Mutations x ∧ CTNNB1 y ∧ Cells z ∧ BetaCatenin y" by blast
  (* There is a logical relation Implies(A, B), Implies(Activating mutations of CTNNB1 are present, Accumulation of β-catenin in specific cells) *)
  (* A is from explanatory sentence 1, B is from explanatory sentence 1. *)
  (* We already have Mutations x and CTNNB1 y, so we can infer Accumulation of β-catenin in specific cells. *)
  then have "Accumulation y" sledgehammer
  (* There is a logical relation Implies(B, D), Implies(Accumulation of β-catenin in specific cells, Proliferation of cells) *)
  (* B is from explanatory sentence 1, D is from explanatory sentence 2 and 3. *)
  (* We already have Accumulation y, so we can infer Proliferation of cells. *)
  then have "Proliferation z" <ATP>
  (* We need to show that the mutations promote proliferation via β-catenin. *)
  (* From explanation 3, we know that the accumulation of β-catenin contributes to proliferation by promoting cyclin D1 expression. *)
  (* Therefore, we can conclude that mutations promote proliferation via β-catenin. *)
  then have "Promote e ∧ Agent e x ∧ Patient e z ∧ Via e y" <ATP>
  then show ?thesis <ATP>
qed

end
