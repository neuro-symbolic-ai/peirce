theory worldtree_3_0
imports Main


begin

typedecl entity
typedecl event

consts
  Hurricane :: "entity ⇒ bool"
  Tornado :: "entity ⇒ bool"
  HighWindSpeeds :: "event ⇒ bool"
  Has :: "event ⇒ entity ⇒ bool"

(* Explanation 1: A hurricane has high wind speeds. *)
axiomatization where
  explanation_1: "∀x e. Hurricane x ∧ HighWindSpeeds e ∧ Has e x"

(* Explanation 2: A tornado has high wind speeds. *)
axiomatization where
  explanation_2: "∀x e. Tornado x ∧ HighWindSpeeds e ∧ Has e x"


theorem hypothesis:
 assumes asm: "Hurricane x ∨ Tornado x"
  (* Hypothesis: Both hurricanes and tornadoes always have high winds. *)
 shows "∃x e. (Hurricane x ∨ Tornado x) ∧ Have e ∧ HighWinds e"
proof -
  (* From the premise, we know that either a hurricane or a tornado is present. *)
  consider cases
    (* Case 1: A hurricane is present. *)
    assume "Hurricane x"
    (* Using Explanation 1, we know that a hurricane has high wind speeds. *)
    then obtain e where "HighWindSpeeds e ∧ Has e x" sledgehammer
    (* Therefore, a hurricane has high winds. *)
    then have "(Hurricane x ∨ Tornado x) ∧ Have e ∧ HighWinds e" by auto
  next
    (* Case 2: A tornado is present. *)
    assume "Tornado x"
    (* Using Explanation 2, we know that a tornado has high wind speeds. *)
    then obtain e where "HighWindSpeeds e ∧ Has e x" <ATP>
    (* Therefore, a tornado has high winds. *)
    then have "(Hurricane x ∨ Tornado x) ∧ Have e ∧ HighWinds e" by auto
  qed

end
