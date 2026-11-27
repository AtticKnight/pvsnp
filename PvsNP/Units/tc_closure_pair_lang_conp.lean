import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_np_all_prefixes

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_pair_lang_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.m2_np_all_prefixes

theorem pairB_eq_rep (u v : List Bool) :
    pairB u v = List.replicate u.length true ++ false :: (u ++ v) := by
  have hun : ∀ n : ℕ, un n = List.replicate n true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [un, ih, List.replicate_succ]
  simp [pairB, hun, List.append_assoc]

def verPL (f₁ f₂ : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  let x := p.1
  let w := p.2
  let u := (unpairB x).1
  let v := (unpairB x).2
  let bad := decide (x = pairB u v)
  let b1 := f₁ (u, w)
  let b2 := f₂ (v, w)
  (!bad) || b1 || b2

def boolOrD (q b : Bool) : Bool × Option Bool :=
  (q || b, none)

theorem cpt_verPL (f₁ f₂ : List Bool × List Bool → Bool)
    (hf₁ : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f₁)
    (hf₂ : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool f₂) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (verPL f₁ f₂) := by
  have hx : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := cpt_fst
  have hw : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := cpt_snd
  have hu := cpt_comp hx cpt_unpairB1
  have hv := cpt_comp hx cpt_unpairB2
  have hre := cpt_comp (cpt_pairG hu hv) cpt_pairB
  have hEq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2)) :=
    cpt_comp (cpt_pairG hx hre) PvsNP.Units.m2_eq_polytime
  have hNotEq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => boolToFlag (decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2))) :=
    cpt_comp hEq cpt_boolToFlag
  have hb1 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => boolToFlag (f₁ ((unpairB p.1).1, p.2))) :=
    cpt_comp (cpt_comp (cpt_pairG hu hw) hf₁) cpt_boolToFlag
  have hb2 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => boolToFlag (f₂ ((unpairB p.1).2, p.2))) :=
    cpt_comp (cpt_comp (cpt_pairG hv hw) hf₂) cpt_boolToFlag
  -- Wait: boolToFlag true = [], boolToFlag false = [true]!
  -- So (!bad) || b1 || b2 = true iff (bad = false) ∨ (b1 = true) ∨ (b2 = true)
  -- iff (boolToFlag bad ≠ []) ∨ (boolToFlag b1 = []) ∨ (boolToFlag b2 = [])!
  -- Using sel on string encoding: return [] iff (!bad || b1 || b2 = true), else [true]!
  have hComb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s =>
        let fl0 := (unpairB s).1
        let r := (unpairB s).2
        let fl1 := (unpairB r).1
        let fl2 := (unpairB r).2
        sel fl0 (sel fl1 [] (sel fl2 [] [true])) []) := by
    have h0 := cpt_unpairB1
    have hr := cpt_unpairB2
    have h1 := cpt_unpairB1_1 hr
    have h2 := cpt_unpairB2_1 hr
    exact cpt_sel h0 (cpt_sel h1 (cpt_const []) (cpt_sel h2 (cpt_const []) (cpt_const [true]))) (cpt_const [])
  have hPack := cpt_comp (cpt_pairG hNotEq (cpt_comp (cpt_pairG hb1 hb2) cpt_pairB)) cpt_pairB
  have hFlag := cpt_comp hPack hComb
  have hRes := cpt_comp hFlag cpt_isEmpty
  have heq : (fun p : List Bool × List Bool =>
      decide ((sel (boolToFlag (decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2)))
        (sel (boolToFlag (f₁ ((unpairB p.1).1, p.2))) []
          (sel (boolToFlag (f₂ ((unpairB p.1).2, p.2))) [] [true])) []) = [])) = verPL f₁ f₂ := by
    funext ⟨x, w⟩
    simp only [verPL]
    cases h0 : decide (x = pairB (unpairB x).1 (unpairB x).2) <;>
      cases h1 : f₁ ((unpairB x).1, w) <;>
      cases h2 : f₂ ((unpairB x).2, w) <;>
      simp [boolToFlag, sel]
  have hRes' : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (verPL f₁ f₂) := by
    rw [← heq]
    have hPackEq : ∀ p : List Bool × List Bool,
        (fun s => decide ((sel (unpairB s).1
          (sel (unpairB (unpairB s).2).1 [] (sel (unpairB (unpairB s).2).2 [] [true])) []) = []))
          (pairB (boolToFlag (decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2)))
            (pairB (boolToFlag (f₁ ((unpairB p.1).1, p.2)))
              (boolToFlag (f₂ ((unpairB p.1).2, p.2))))) =
        decide ((sel (boolToFlag (decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2)))
          (sel (boolToFlag (f₁ ((unpairB p.1).1, p.2))) []
            (sel (boolToFlag (f₂ ((unpairB p.1).2, p.2))) [] [true])) []) = []) := by
      intro p
      simp only [unpairB_pairB]
    have hfun : (fun s => decide ((sel (unpairB s).1
        (sel (unpairB (unpairB s).2).1 [] (sel (unpairB (unpairB s).2).2 [] [true])) []) = [])) ∘
        (fun p : List Bool × List Bool =>
          pairB (boolToFlag (decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2)))
            (pairB (boolToFlag (f₁ ((unpairB p.1).1, p.2)))
              (boolToFlag (f₂ ((unpairB p.1).2, p.2))))) =
        (fun p : List Bool × List Bool =>
          decide ((sel (boolToFlag (decide (p.1 = pairB (unpairB p.1).1 (unpairB p.1).2)))
            (sel (boolToFlag (f₁ ((unpairB p.1).1, p.2))) []
              (sel (boolToFlag (f₂ ((unpairB p.1).2, p.2))) [] [true])) []) = [])) :=
      funext hPackEq
    rw [← hfun]
    exact hRes
  exact hRes'

theorem main :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.coNP → L₂ ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool,
          x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂} :
        Language Bool) ∈ PvsNP.coNP := by
  classical
  intro L₁ L₂ hL₁ hL₂
  change ({x : List Bool | ∃ u v : List Bool,
      x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂} :
    Language Bool)ᶜ ∈ PvsNP.NP
  obtain ⟨R₁, p₁, ⟨f₁, hfR₁, hfc₁⟩, hlen₁, hmem₁⟩ :=
    L045 L₁ᶜ ((PvsNP.Units.fr_ladner.NP_iff L₁ᶜ).1 hL₁)
  obtain ⟨R₂, p₂, ⟨f₂, hfR₂, hfc₂⟩, hlen₂, hmem₂⟩ :=
    L045 L₂ᶜ ((PvsNP.Units.fr_ladner.NP_iff L₂ᶜ).1 hL₂)
  have hfL₁ : ∀ u w : List Bool, f₁ (u, w) = true → u ∈ L₁ᶜ := fun u w h =>
    (hmem₁ u).2 ⟨w, (hfR₁ (u, w)).2 h⟩
  have hfL₂ : ∀ v w : List Bool, f₂ (v, w) = true → v ∈ L₂ᶜ := fun v w h =>
    (hmem₂ v).2 ⟨w, (hfR₂ (v, w)).2 h⟩
  have hb₁ : ∀ u w : List Bool, f₁ (u, w) = true → w.length ≤ p₁.eval u.length := fun u w h =>
    hlen₁ u w ((hfR₁ (u, w)).2 h)
  have hb₂ : ∀ v w : List Bool, f₂ (v, w) = true → w.length ≤ p₂.eval v.length := fun v w h =>
    hlen₂ v w ((hfR₂ (v, w)).2 h)
  refine ⟨verPL f₁ f₂, p₁ + p₂, cpt_verPL f₁ f₂ hfc₁ hfc₂, fun x => ?_⟩
  have hu_le : (unpairB x).1.length ≤ x.length := by
    have := unpairB_length x; omega
  have hv_le : (unpairB x).2.length ≤ x.length := by
    have := unpairB_length x; omega
  constructor
  · intro hx
    by_cases hfmt : x = pairB (unpairB x).1 (unpairB x).2
    · by_cases hu1 : (unpairB x).1 ∈ L₁
      · have hv2 : (unpairB x).2 ∈ L₂ᶜ := by
          intro hvL₂
          exact hx ⟨(unpairB x).1, (unpairB x).2, hfmt.trans (pairB_eq_rep _ _), hu1, hvL₂⟩
        obtain ⟨w, hw⟩ := (hmem₂ (unpairB x).2).1 hv2
        have hfw : f₂ ((unpairB x).2, w) = true := (hfR₂ ((unpairB x).2, w)).1 hw
        have hwl : w.length ≤ (p₁ + p₂).eval x.length := by
          simp only [Polynomial.eval_add]
          exact le_trans ((hb₂ _ w hfw).trans (poly_eval_mono p₂ hv_le)) (Nat.le_add_left _ _)
        exact ⟨w, hwl, by simp [verPL, hfw]⟩
      · obtain ⟨w, hw⟩ := (hmem₁ (unpairB x).1).1 hu1
        have hfw : f₁ ((unpairB x).1, w) = true := (hfR₁ ((unpairB x).1, w)).1 hw
        have hwl : w.length ≤ (p₁ + p₂).eval x.length := by
          simp only [Polynomial.eval_add]
          exact le_trans ((hb₁ _ w hfw).trans (poly_eval_mono p₁ hu_le)) (Nat.le_add_right _ _)
        exact ⟨w, hwl, by simp [verPL, hfw]⟩
    · refine ⟨[], Nat.zero_le _, ?_⟩
      simp [verPL, hfmt]
  · rintro ⟨w, _, hacc⟩
    rintro ⟨u, v, rfl, hu1, hv2⟩
    have hxpb : List.replicate u.length true ++ false :: (u ++ v) = pairB u v :=
      (pairB_eq_rep u v).symm
    rw [hxpb] at hacc
    simp only [verPL, unpairB_pairB, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hacc
    rcases hacc with h1 | h2
    · exact hfL₁ u w h1 hu1
    · exact hfL₂ v w h2 hv2

end PvsNP.Units.tc_closure_pair_lang_conp

theorem PvsNP.Units.tc_closure_pair_lang_conp :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.coNP → L₂ ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool,
          x = List.replicate u.length true ++ false :: (u ++ v) ∧ u ∈ L₁ ∧ v ∈ L₂} :
        Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_pair_lang_conp.main
