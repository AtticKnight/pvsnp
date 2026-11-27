import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_unary_pad_np
import PvsNP.Units.m2_upward_padding

set_option autoImplicit false

namespace PvsNP.Units.m2_nexp_padded_np

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner
open PvsNP.Units.m2_unary_pad_np
open PvsNP.Units.m2_upward_padding_aux

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neU :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neU_true, Computability.encodeBool])

private def padVerB (V : List Bool × List Bool → Bool) (k : ℕ) (z : List Bool) : Bool :=
  let s := (unpairB z).1
  let c := (unpairB z).2
  !(upPadA s).isEmpty &&
    (decide ((pow2Cap k s ++ un k).length ≤ (hd s).length) &&
      (decide ((hd s).length ≤ (pow2Cap k s ++ un k).length) &&
        (decide (c.length ≤ (hd s).length) &&
          V (dropN s, c))))

private def padVer (V : List Bool × List Bool → Bool) (k : ℕ) (p : List Bool × List Bool) : Bool :=
  !(upPadA p.1).isEmpty &&
    (decide ((pow2Cap k p.1 ++ un k).length ≤ (hd p.1).length) &&
      (decide ((hd p.1).length ≤ (pow2Cap k p.1 ++ un k).length) &&
        (decide (p.2.length ≤ (hd p.1).length) &&
          V (dropN p.1, p.2))))

private theorem comb5 (A : List Bool) (a b c d : Bool) :
    (!(sel A [] (sel (if a then [true] else []) []
      (sel (if b then [true] else []) []
        (sel (if c then [true] else []) []
          (sel (if d then [true] else []) [] [true]))))).isEmpty) =
      (!A.isEmpty && (a && (b && (c && d)))) := by
  cases A <;> cases a <;> cases b <;> cases c <;> cases d <;> simp [sel]

private theorem cpt_padVerB (V : List Bool × List Bool → Bool) (k : ℕ)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool (padVerB V k) := by
  have hV' : ComputableInPolyTime encodePair Computability.encodeBool V := hV
  have hS : CPT (fun z : List Bool => (unpairB z).1) := cpt_unpairB1
  have hC : CPT (fun z : List Bool => (unpairB z).2) := cpt_unpairB2
  have fA : CPT (fun z : List Bool => upPadA (unpairB z).1) := cpt_comp hS cpt_upPadA
  have hLHS : CPT (fun z : List Bool => pow2Cap k (unpairB z).1 ++ un k) :=
    cpt_comp hS (cpt_app2 (cpt_pow2Cap k) (cpt_const (un k)))
  have hRHS : CPT (fun z : List Bool => hd (unpairB z).1) := cpt_hd1 hS
  have f1 := cpt_le hLHS hRHS
  have f2 := cpt_le hRHS hLHS
  have f3 := cpt_le hC hRHS
  have hDrop : CPT (fun z : List Bool => dropN (unpairB z).1) := cpt_dropN1 hS
  have f4 := cpt_bitFlag (cpt_comp (cpt_pair hDrop hC) hV')
  have all := cpt_sel fA (cpt_const []) (cpt_sel f1 (cpt_const [])
    (cpt_sel f2 (cpt_const []) (cpt_sel f3 (cpt_const [])
      (cpt_sel f4 (cpt_const []) (cpt_const [true])))))
  exact cptU (cpt_comp all cpt_neU) (fun z => comb5 _ _ _ _ _)

private theorem cpt_padVer (V : List Bool × List Bool → Bool) (k : ℕ)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (padVer V k) := by
  have h := cpt_comp cpt_pairB (cpt_padVerB V k hV)
  exact cptU h (fun p => by simp only [Function.comp_apply, padVerB, padVer, unpairB_pairB])

end PvsNP.Units.m2_nexp_padded_np

theorem PvsNP.Units.m2_nexp_padded_np :
    ∀ L : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
      ∃ k : ℕ, ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈ PvsNP.NP := by
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
  open PvsNP.Units.m2_unary_pad_np in
  open PvsNP.Units.m2_upward_padding_aux in
  open PvsNP.Units.m2_nexp_padded_np in
  rintro L ⟨V, k, hV, hspec⟩
  refine ⟨k, padVer V k, Polynomial.X, cpt_padVer V k hV, fun s => ?_⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hwlen, hVw⟩ := (hspec x).mp hx
    set t := 2 ^ (x.length ^ k) + k
    have hhd : hd (List.replicate t true ++ false :: x) = un t := hd_un t x
    have hdrop : dropN (List.replicate t true ++ false :: x) = x := dropN_un t x
    have hpadA : upPadA (List.replicate t true ++ false :: x) = x ++ [false] := by
      have e : (List.replicate t true ++ false :: x) ++ [false] =
          un t ++ false :: (x ++ [false]) := by simp [un]
      rw [upPadA, e, dropN_un]
    have hpow : (pow2Cap k (List.replicate t true ++ false :: x)).length + k = t := by
      rw [pow2Cap_length, hhd, hdrop, un_length]
      have hmin : min (2 ^ (x.length ^ k)) (t + 1) = 2 ^ (x.length ^ k) :=
        min_eq_left (by omega)
      rw [hmin]
    refine ⟨w, ?_, ?_⟩
    · simp only [Polynomial.eval_X, List.length_append, List.length_replicate, List.length_cons]
      omega
    · simp only [padVer, hpadA, hdrop, hhd, un_length, List.length_append, hpow, le_refl,
        decide_true, Bool.true_and, hVw, Bool.and_true, List.isEmpty_append, List.isEmpty_cons,
        Bool.and_false, Bool.not_false]
      exact decide_eq_true hwlen
  · rintro ⟨w, _, hs⟩
    simp only [padVer, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hs
    obtain ⟨hA, hle1, hle2, hwle, hVw⟩ := hs
    have hA' : upPadA s ≠ [] := by
      intro h; rw [h] at hA; simp at hA
    have hsplit := (up_hd_split s).resolve_left hA'
    have hlen : (pow2Cap k s).length + k = (hd s).length := by
      simp only [List.length_append, un_length] at hle1 hle2
      omega
    rw [pow2Cap_length] at hlen
    have hmin : min (2 ^ ((dropN s).length ^ k)) ((hd s).length + 1) = 2 ^ ((dropN s).length ^ k) := by
      rcases min_cases (2 ^ ((dropN s).length ^ k)) ((hd s).length + 1) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · omega
    rw [hmin] at hlen
    set t := (hd s).length
    set x := dropN s
    have hxL : x ∈ L := (hspec x).mpr ⟨w, by omega, hVw⟩
    refine ⟨x, hxL, ?_⟩
    have hu : hd s = List.replicate t true := up_hd_eq_un s
    rw [hlen, ← hu]
    exact hsplit
