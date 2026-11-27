import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.tl_lang_len_square_p

/-
Built on the settled units PvsNP.Units.fr_ladner, m2_len_le_polytime, m2_bounded_unary_search_polytime
and tl_lang_len_square_p of github.com/makedotfun/pvsnp (same shape as the cube-length unit).
|x| = k^e iff for some i ≤ |x|: the unary power (1^i)^e has the length of x.
-/

namespace PvsNP.Units.tl_lang_len_pow_all_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

def powU : ℕ → List Bool → List Bool
  | 0, _ => [true]
  | e + 1, u => mulU (powU e u) u

theorem powU_length (e : ℕ) (u : List Bool) : (powU e u).length = u.length ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    show (mulU (powU e u) u).length = u.length ^ (e + 1)
    rw [PvsNP.Units.tl_lang_len_square_p.mulU_length_eq, ih, pow_succ]

theorem cpt_powU (e : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (powU e) := by
  induction e with
  | zero => exact cpt_const [true]
  | succ e ih => exact cpt_mulU2 ih cpt_id

def pw (e : ℕ) (p : List Bool × List Bool) : List Bool := powU e p.2

def le1 (e : ℕ) (p : List Bool × List Bool) : List Bool :=
  if decide ((pw e p).length ≤ p.1.length) then [true] else []

def le2 (e : ℕ) (p : List Bool × List Bool) : List Bool :=
  if decide (p.1.length ≤ (pw e p).length) then [true] else []

def Fv (e : ℕ) (p : List Bool × List Bool) : List Bool :=
  if le1 e p = [] then [] else le2 e p

def V (e : ℕ) (p : List Bool × List Bool) : Bool := !(Fv e p).isEmpty

theorem cpt_V (e : ℕ) :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (V e) := by
  have hpw : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (pw e) := by
    have h := cpt_comp cpt_snd (cpt_powU e)
    exact h
  have hpa : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (pw e p, p.1)) :=
    cpt_pairG hpw cpt_fst
  have hpb : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (p.1, pw e p)) :=
    cpt_pairG cpt_fst hpw
  have hle0 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length)) := by
    rw [encodePair_eq]; exact PvsNP.Units.m2_len_le_polytime
  have hlea : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide ((pw e p).length ≤ p.1.length)) := by
    have h := cpt_comp hpa hle0
    exact h
  have hleb : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1.length ≤ (pw e p).length)) := by
    have h := cpt_comp hpb hle0
    exact h
  have hl1 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (le1 e) := by
    have h := cpt_bitFlag hlea
    exact h
  have hl2 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (le2 e) := by
    have h := cpt_bitFlag hleb
    exact h
  have hp2 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (le1 e p, le2 e p)) :=
    cpt_pairG hl1 hl2
  have hF : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (Fv e) := by
    have h := cpt_comp hp2 cpt_ifNonempty
    exact h
  have h := cpt_comp hF PvsNP.Units.tl_lang_len_square_p.cpt_nonEmpty
  exact h

theorem V_poly (e : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (V e) := by
  rw [← encodePair_eq]; exact cpt_V e

theorem V_iff (e : ℕ) (p : List Bool × List Bool) :
    V e p = true ↔ ((pw e p).length ≤ p.1.length ∧ p.1.length ≤ (pw e p).length) := by
  unfold V Fv le1 le2
  by_cases h1 : (pw e p).length ≤ p.1.length <;>
    by_cases h2 : p.1.length ≤ (pw e p).length <;> simp [h1, h2]

end PvsNP.Units.tl_lang_len_pow_all_p

theorem PvsNP.Units.tl_lang_len_pow_all_p :
    ∀ e : ℕ, ({x : List Bool | ∃ k : ℕ, x.length = k ^ e} : Language Bool) ∈ PvsNP.P := by
  intro e
  have hS := PvsNP.Units.m2_bounded_unary_search_polytime (PvsNP.Units.tl_lang_len_pow_all_p.V e)
    (PvsNP.Units.tl_lang_len_pow_all_p.V_poly e)
  refine ⟨_, hS, fun x => ?_⟩
  change (∃ k : ℕ, x.length = k ^ e) ↔
    (List.range (x.length + 1)).any (fun i => PvsNP.Units.tl_lang_len_pow_all_p.V e (x, List.replicate i true)) = true
  rw [List.any_eq_true]
  simp only [List.mem_range, PvsNP.Units.tl_lang_len_pow_all_p.V_iff, PvsNP.Units.tl_lang_len_pow_all_p.pw,
    PvsNP.Units.tl_lang_len_pow_all_p.powU_length, List.length_replicate]
  constructor
  · rintro ⟨k, hk⟩
    cases e with
    | zero => exact ⟨0, by omega, by simp [hk], by simp [hk]⟩
    | succ e' =>
      have hkle : k ≤ k ^ (e' + 1) := by
        cases k with
        | zero => omega
        | succ k' => exact Nat.le_self_pow (by omega) _
      exact ⟨k, by omega, by omega, by omega⟩
  · rintro ⟨i, _, h1, h2⟩
    exact ⟨i, by omega⟩
