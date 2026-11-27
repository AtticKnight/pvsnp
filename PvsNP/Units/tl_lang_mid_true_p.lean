import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tl_lang_mid_true_p

/-- The DFA fold that reads off the first bit: once a bit has been seen, the state sticks. -/
theorem foldl_head (y : List Bool) (q : Option Bool) :
    (y.foldl (fun q b => q.or (some b)) q) = q.or y.head? := by
  induction y generalizing q with
  | nil => cases q <;> rfl
  | cons b ys ih =>
    rw [List.foldl_cons, ih]
    cases q with
    | none => rfl
    | some c => rfl

/-- The head of a dropped list is the element at the drop point. -/
theorem head_drop (x : List Bool) (m : ℕ) : (x.drop m).head? = x[m]? := by
  rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]

/-- The language of strings whose head bit is `true` is in P, by a two-state DFA. -/
theorem head_lang_in_P :
    ({y : List Bool | y.head? = some true} : Language Bool) ∈ PvsNP.P := by
  have hset : ({y : List Bool | y.head? = some true} : Language Bool)
      = {y : List Bool | (fun q : Option Bool => decide (q = some true))
          (y.foldl (fun q b => q.or (some b)) none) = true} := by
    ext y
    simp only [Set.mem_setOf_eq, decide_eq_true_eq]
    rw [foldl_head]
    exact Iff.rfl
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p (Option Bool)
    (fun q b => q.or (some b)) none (fun q => decide (q = some true))

/-- Dropping the first half of a string is computable in polynomial time:
the pair `(half x, x)` is built by `cpt_pair` from the polytime `half`,
then `m2_take_drop_length_polytime` drops by the length of `half x`. -/
theorem dropHalf_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.drop (x.length / 2)) := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool =>
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.half x, x)) :=
    PvsNP.Units.m2_np_down_closed.PEqualNP.Library.Machines.cpt_pair
      PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner.cpt_half
      PvsNP.Units.m2_np_down_closed.PEqualNP.Library.Machines.cpt_id
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun p : List Bool × List Bool => p.2.drop p.1.length) ∘
        (fun x : List Bool =>
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.half x, x))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool =>
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.half x, x))
      (fun p : List Bool × List Bool => p.2.drop p.1.length)
      hpair PvsNP.Units.m2_take_drop_length_polytime.2
  have hfun : ((fun p : List Bool × List Bool => p.2.drop p.1.length) ∘
        (fun x : List Bool =>
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.half x, x)))
      = fun x : List Bool => x.drop (x.length / 2) := by
    funext x
    simp only [Function.comp_apply]
    have hlen : (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.half x).length
        = x.length / 2 := by
      rw [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.half_eq]
      simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.un]
    rw [hlen]
  rw [hfun] at hcomp
  exact hcomp

end PvsNP.Units.tl_lang_mid_true_p

/-- The strings whose middle bit is true are in P: split at half the length and
answer the first bit of the second part. -/
theorem PvsNP.Units.tl_lang_mid_true_p :
    ({x : List Bool | x[x.length / 2]? = some true} : Language Bool) ∈ PvsNP.P := by
  have hkarp : PvsNP.KarpReducible
      ({x : List Bool | x[x.length / 2]? = some true} : Language Bool)
      ({y : List Bool | y.head? = some true} : Language Bool) := by
    refine ⟨fun x : List Bool => x.drop (x.length / 2),
      PvsNP.Units.tl_lang_mid_true_p.dropHalf_polyTime, fun x => ?_⟩
    show (x[x.length / 2]? = some true) ↔ ((x.drop (x.length / 2)).head? = some true)
    rw [PvsNP.Units.tl_lang_mid_true_p.head_drop]
  exact PvsNP.Units.m2_p_down_closed _ _
    hkarp PvsNP.Units.tl_lang_mid_true_p.head_lang_in_P
