import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_unary_pad_np
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_inter

set_option autoImplicit false

namespace PvsNP.Units.m2_np_poly_padding_iff

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner
open PvsNP.Units.m2_unary_pad_np

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

private theorem comb3 (A : List Bool) (a b : Bool) :
    (!(sel A [] (sel (if a then [true] else []) []
      (sel (if b then [true] else []) [] [true]))).isEmpty) =
      (!A.isEmpty && (a && b)) := by
  cases A <;> cases a <;> cases b <;> simp [sel]

def padPoly (k : ℕ) (x : List Bool) : List Bool :=
  List.replicate (x.length ^ k) true ++ false :: x

theorem cpt_padPoly (k : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (padPoly k) := by
  have h1 := L055 (Polynomial.X ^ k)
  have hpow : CPT (fun x : List Bool => List.replicate (x.length ^ k) true) :=
    cptU h1 (fun x => by simp)
  have h2 := cpt_app2 hpow (cpt_app2 (cpt_const [false]) cpt_id)
  exact cptU h2 (fun _ => rfl)

def shapeDec (k : ℕ) (s : List Bool) : Bool :=
  !(upPadA s).isEmpty &&
    (decide ((List.replicate ((dropN s).length ^ k) true).length ≤ (hd s).length) &&
      decide ((hd s).length ≤ (List.replicate ((dropN s).length ^ k) true).length))

theorem cpt_shapeDec (k : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool (shapeDec k) := by
  have fA : CPT upPadA := cpt_upPadA
  have hLHS : CPT (fun s : List Bool => List.replicate ((dropN s).length ^ k) true) := by
    have h1 := L055 (Polynomial.X ^ k)
    have h2 : CPT (fun s : List Bool => List.replicate ((Polynomial.X ^ k).eval (dropN s).length) true) :=
      cpt_comp (cpt_dropN1 cpt_id) h1
    exact cptU h2 (fun s => by simp)
  have hRHS : CPT (fun s : List Bool => hd s) := cpt_hd1 cpt_id
  have f1 := cpt_le hLHS hRHS
  have f2 := cpt_le hRHS hLHS
  have all := cpt_sel fA (cpt_const []) (cpt_sel f1 (cpt_const [])
    (cpt_sel f2 (cpt_const []) (cpt_const [true])))
  exact cptU (cpt_comp all cpt_neU) (fun s => comb3 _ _ _)

theorem shape_in_P (k : ℕ) :
    ({s : List Bool | ∃ x : List Bool, s = padPoly k x} : Language Bool) ∈ PvsNP.P := by
  refine (PvsNP.Units.fr_ladner.P_iff _).mpr ⟨shapeDec k, fun s => ?_, cpt_shapeDec k⟩
  constructor
  · rintro ⟨x, rfl⟩
    dsimp only [padPoly]
    set t := x.length ^ k
    have hhd : hd (List.replicate t true ++ false :: x) = un t := hd_un t x
    have hdrop : dropN (List.replicate t true ++ false :: x) = x := dropN_un t x
    have hpadA : upPadA (List.replicate t true ++ false :: x) = x ++ [false] := by
      have e : (List.replicate t true ++ false :: x) ++ [false] =
          un t ++ false :: (x ++ [false]) := by simp [un]
      rw [upPadA, e, dropN_un]
    simp only [shapeDec, hpadA, hdrop, hhd, un_length, List.length_replicate]
    simp [t]
  · intro hs
    simp only [shapeDec, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      List.length_replicate] at hs
    obtain ⟨hA, hle1, hle2⟩ := hs
    have hA' : upPadA s ≠ [] := by
      intro h
      rw [h] at hA
      simp at hA
    have hsplit := (up_hd_split s).resolve_left hA'
    have hlen : (hd s).length = (dropN s).length ^ k := by omega
    have hu : hd s = List.replicate (hd s).length true := up_hd_eq_un s
    refine ⟨dropN s, ?_⟩
    rw [padPoly, ← hlen, ← hu]
    exact hsplit

end PvsNP.Units.m2_np_poly_padding_iff

/-- Polynomial padding by `|x|^k` trues keeps a language in NP and out of it (TM2). -/
theorem PvsNP.Units.m2_np_poly_padding_iff :
    ∀ (L : Language Bool) (k : ℕ), L ∈ PvsNP.NP ↔
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.NP := by
  intro L k
  constructor
  · intro hL
    have hShapeNP : ({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool) ∈ PvsNP.NP :=
      PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_np_poly_padding_iff.shape_in_P k)
    have hPullNP : ({s : List Bool | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈ L} : Language Bool) ∈ PvsNP.NP :=
      PvsNP.Units.m2_np_down_closed _ L
        ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN,
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_dropN,
          fun _ => Iff.rfl⟩ hL
    have hInter := PvsNP.Units.m2_np_inter _ _ hShapeNP hPullNP
    have heq : (({s : List Bool | ∃ x : List Bool, s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool) ⊓
        ({s : List Bool | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈ L} : Language Bool)) =
        ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) := by
      ext s
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
            (PvsNP.Units.m2_np_poly_padding_iff.padPoly k x) = x :=
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
        change PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (PvsNP.Units.m2_np_poly_padding_iff.padPoly k x) ∈ L at hx
        rw [hdx] at hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, rfl⟩, ?_⟩
        have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
            (List.replicate (x.length ^ k) true ++ false :: x) = x :=
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
        show PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (List.replicate (x.length ^ k) true ++ false :: x) ∈ L
        rw [hdx]
        exact hx
    rw [← heq]
    exact hInter
  · intro hPad
    refine PvsNP.Units.m2_np_down_closed L _
      ⟨PvsNP.Units.m2_np_poly_padding_iff.padPoly k,
        PvsNP.Units.m2_np_poly_padding_iff.cpt_padPoly k, fun x => ?_⟩ hPad
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hd := congrArg PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN hxy
      have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (PvsNP.Units.m2_np_poly_padding_iff.padPoly k x) = x :=
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
      have hdy : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (List.replicate (y.length ^ k) true ++ false :: y) = y :=
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (y.length ^ k) y
      rw [hdx, hdy] at hd
      subst hd
      exact hy
