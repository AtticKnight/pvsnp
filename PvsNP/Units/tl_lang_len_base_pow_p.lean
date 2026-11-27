import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_len_base_pow_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

abbrev libEncodePair : List Bool × List Bool → List (Bool ⊕ Bool) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem toTrue_eq_rep : ∀ s : List Bool,
    s.filterMap (fun _ => some true) = List.replicate s.length true
  | [] => rfl
  | _ :: xs => by
    simp only [List.length_cons, List.replicate_succ]
    exact congrArg (true :: ·) (toTrue_eq_rep xs)

private theorem le_pow_three : ∀ k : ℕ, k ≤ 3 ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := le_pow_three k
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
    rw [Nat.pow_succ]
    omega

def pow3TestS (w : List Bool) : Bool :=
  let x := (unpairB w).1
  let u_cnt := (unpairB w).2
  decide ((tpw [true, true, true] u_cnt x).filterMap (fun _ => some true) =
    x.filterMap (fun _ => some true))

def pow3Test (p : List Bool × List Bool) : Bool :=
  pow3TestS (pairB p.1 p.2)

theorem cpt_pow3Test :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer pow3Test := by
  have hencP : PvsNP.encodePair = libEncodePair := by
    funext _
    rfl
  have hEqLib : ComputableInPolyTime libEncodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
    rw [← hencP]
    exact PvsNP.Units.m2_eq_polytime
  have hToTrue : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.filterMap (fun _ => some true)) :=
    filterMap_polyTime _ _ _ (fun _ => some true) (fun _ => rfl)
  have hX := cpt_unpairB1
  have hU := cpt_unpairB2
  have hTpw := cpt_tpw (cpt_const [true, true, true]) hU hX
  have hCand := cpt_comp hTpw hToTrue
  have hTarg := cpt_comp hX hToTrue
  have hBool : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool pow3TestS :=
    cptp (cpt_comp (cpt_pair hCand hTarg) hEqLib) (fun _ => rfl)
  rw [hencP]
  exact cptp (cpt_comp cpt_pairB hBool) (fun _ => rfl)

def pow3Dec (x : List Bool) : Bool :=
  (List.range (x.length + 1)).any (fun k => pow3Test (x, List.replicate k true))

theorem cpt_pow3Dec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer pow3Dec :=
  PvsNP.Units.m2_bounded_unary_search_polytime pow3Test cpt_pow3Test

theorem len_base_pow_p :
    ({x : List Bool | ∃ k : ℕ, x.length = 3 ^ k} : Language Bool) ∈ PvsNP.P := by
  refine ⟨pow3Dec, cpt_pow3Dec, fun x => ?_⟩
  change (∃ k : ℕ, x.length = 3 ^ k) ↔
    (List.range (x.length + 1)).any (fun k => pow3Test (x, List.replicate k true)) = true
  rw [List.any_eq_true]
  have h3 : ([true, true, true] : List Bool).length = 3 := rfl
  constructor
  · rintro ⟨k, hk⟩
    have hk_le : k ≤ x.length := by
      have hkp := le_pow_three k
      omega
    refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
    simp only [pow3Test, pow3TestS, unpairB_pairB, decide_eq_true_eq, toTrue_eq_rep]
    rw [tpw_length [true, true, true] (List.replicate k true) x (by decide),
      h3, List.length_replicate, ← hk]
    have hmin : min x.length (x.length + 1) = x.length := by omega
    rw [hmin]
  · rintro ⟨k, _, hok⟩
    simp only [pow3Test, pow3TestS, unpairB_pairB, decide_eq_true_eq, toTrue_eq_rep] at hok
    have hlen := congrArg List.length hok
    simp only [List.length_replicate] at hlen
    rw [tpw_length [true, true, true] (List.replicate k true) x (by decide),
      h3, List.length_replicate] at hlen
    exact ⟨k, by omega⟩

end PvsNP.Units.tl_lang_len_base_pow_p

theorem PvsNP.Units.tl_lang_len_base_pow_p :
    ({x : List Bool | ∃ k : ℕ, x.length = 3 ^ k} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_len_base_pow_p.len_base_pow_p
