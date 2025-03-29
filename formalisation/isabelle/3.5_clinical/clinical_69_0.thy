theory clinical_69_0
imports Main


begin

typedecl entity
typedecl event

consts
  PhosphorylationOfAktAtS473 :: "event ⇒ bool"
  InCarboxyTerminalHydrophobicMotif :: "event ⇒ bool"
  Stimulates :: "event ⇒ bool"
  FullAktActivity :: "event ⇒ bool"
  ByMtor :: "event ⇒ bool"
  ByDnaPk :: "event ⇒ bool"
  PkbAkt :: "event ⇒ bool"
  Binds :: "event ⇒ bool"
  DockingSiteOnPik3 :: "event ⇒ bool"
  AtPlasmaMembrane :: "event ⇒ bool"
  LeadsTo :: "event ⇒ event ⇒ bool"
  PartialPkbAktActivation :: "event ⇒ bool"

(* Explanation 1: Phosphorylation of Akt at S473 in the carboxy-terminal hydrophobic motif, either by mTOR or by DNA-PK stimulates full Akt activity. *)
axiomatization where
  explanation_1: "∃e. PhosphorylationOfAktAtS473 e ∧ InCarboxyTerminalHydrophobicMotif e ∧ Stimulates e ∧ FullAktActivity e ∧ (ByMtor e ∨ ByDnaPk e)"

(* Explanation 2: PKB/Akt binds to the docking site on PIK3 at the plasma membrane leading to a partial PKB/Akt activation. *)
axiomatization where
  explanation_2: "∃e. PkbAkt e ∧ Binds e ∧ DockingSiteOnPik3 e ∧ AtPlasmaMembrane e ∧ LeadsTo e (PartialPkbAktActivation e)"


theorem hypothesis:
 assumes asm: "PhosphorylationOfAktAtS473 e ∧ InCarboxyTerminalHydrophobicMotif e"
  (* Hypothesis: Phosphorylation of bound Akt stimulates full activity of Akt. *)
 shows "∃e. PhosphorylationOfAktAtS473 e ∧ Stimulates e ∧ FullAktActivity e"
proof -
  (* From the premise, we know that Akt is phosphorylated at S473 in the carboxy-terminal hydrophobic motif. *)
  from asm have "PhosphorylationOfAktAtS473 e ∧ InCarboxyTerminalHydrophobicMotif e" <ATP>
  (* We have the explanatory sentence 1 stating that phosphorylation of Akt at S473 in the carboxy-terminal hydrophobic motif stimulates full Akt activity. *)
  (* This implies that PhosphorylationOfAktAtS473 e ∧ InCarboxyTerminalHydrophobicMotif e leads to Akt activity being stimulated and full Akt activity. *)
  from explanation_1 obtain e where "PhosphorylationOfAktAtS473 e ∧ InCarboxyTerminalHydrophobicMotif e ∧ Stimulates e ∧ FullAktActivity e" <ATP>
  then show ?thesis <ATP>
qed

end
