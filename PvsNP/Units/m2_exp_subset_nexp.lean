import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_upward_padding

/-
Built on the settled units PvsNP.Units.fr_ladner and PvsNP.Units.m2_upward_padding of
github.com/makedotfun/pvsnp (Apache License 2.0), where fr_ladner's machine combinators come
from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_subset_nexp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem encodePair_eq : encodePair = PvsNP.encodePair := by
  funext ⟨x, y⟩
  simp [encodePair, PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]

private def allTrueD : Bool → Bool → Bool × Option Bool
  | q, b => (q && b, none)

private def allTrueFin : Bool → Option Bool
  | true => some true
  | false => none

private theorem allTrue_run_false (l : List Bool) :
    fstRun allTrueD allTrueFin false l = [] := by
  induction l with
  | nil => rfl
  | cons b tl ih => simpa [fstRun, allTrueD] using ih

private theorem allTrue_run (l : List Bool) :
    (if l.all id then [true] else []) = fstRun allTrueD allTrueFin true l := by
  induction l with
  | nil => rfl
  | cons b tl ih =>
    cases b with
    | false => simp [fstRun, allTrueD, allTrue_run_false]
    | true => simpa [fstRun, allTrueD] using ih

private theorem cpt_allTrueFlag :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun w : List Bool => if w.all id then [true] else []) :=
  fst_polyTime _ _ _ allTrueD allTrueFin true allTrue_run

private theorem dropWhile_replicate_false (m : ℕ) (u : List Bool) :
    ((List.replicate m true ++ false :: u).dropWhile id).tail = u := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [List.replicate_succ, List.dropWhile] using ih

private theorem exp_subset_nexp (L : Language Bool)
    (hL : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔
          ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true := by
  obtain ⟨k, f, M, hf, htime⟩ := hL
  obtain ⟨d, hd, hdec⟩ := PvsNP.Units.m2_upward_padding L k ⟨f, M, hf, htime⟩
  let V : List Bool × List Bool → Bool := fun p => p.2.all id && d (p.2 ++ false :: p.1)
  let Vlist : List Bool → List Bool := fun s =>
    sel (if (unpairB s).2.all id then [true] else []) [false]
      (sel (if d ((unpairB s).2 ++ false :: (unpairB s).1) then [true] else []) [false] [true])
  have hVlist : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) Vlist := by
    have h1 := cpt_comp cpt_unpairB2 cpt_allTrueFlag
    have h2 := cpt_bitFlag
      (cpt_comp (cpt_app2 cpt_unpairB2 (cpt_cons1 false cpt_unpairB1)) hd)
    exact cpt_sel h1 (cpt_const [false]) (cpt_sel h2 (cpt_const [false]) (cpt_const [true]))
  have hVpair : ∀ p : List Bool × List Bool, Vlist (pairB p.1 p.2) = [V p] := by
    intro p
    simp only [Vlist, V, unpairB_pairB, sel]
    cases p.2.all id <;> cases d (p.2 ++ false :: p.1) <;> rfl
  have hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V := by
    have h1 : ComputableInPolyTime encodePair (fun x : List Bool => x)
        (fun p : List Bool × List Bool => [V p]) :=
      cpt_congr (cpt_comp cpt_pairB hVlist) hVpair
    rw [encodePair_eq] at h1
    obtain ⟨c⟩ := h1
    exact ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩
  refine ⟨V, k, hV, fun x => ?_⟩
  constructor
  · intro hx
    refine ⟨List.replicate (2 ^ (x.length ^ k) + k) true, by simp, ?_⟩
    have hmem : List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x ∈
        ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) :=
      ⟨x, hx, rfl⟩
    have hd_true : d (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = true :=
      (hdec _).mp hmem
    simp [V, hd_true]
  · rintro ⟨w, -, hVw⟩
    simp only [V, Bool.and_eq_true] at hVw
    obtain ⟨hall, hd_true⟩ := hVw
    obtain ⟨x', hx', heq⟩ := (hdec _).mpr hd_true
    have hw : w = List.replicate w.length true :=
      List.eq_replicate_iff.mpr ⟨rfl, fun b hb => List.all_eq_true.mp hall b hb⟩
    rw [hw] at heq
    have hx_eq : x = x' := by
      have := congrArg (fun l : List Bool => (l.dropWhile id).tail) heq
      rwa [dropWhile_replicate_false, dropWhile_replicate_false] at this
    rwa [hx_eq]

end PvsNP.Units.m2_exp_subset_nexp

theorem PvsNP.Units.m2_exp_subset_nexp :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true :=
  PvsNP.Units.m2_exp_subset_nexp.exp_subset_nexp
