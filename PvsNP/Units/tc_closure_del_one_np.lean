import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_np_union

/-!
Copyright 2026 bumz. Licensed under Apache-2.0.

Original closure proof. For each fixed bit, a unary certificate chooses the
insertion position. Its length is at most the input length. The insertion map
is a composition of the campaign's settled take/drop, cons and pairing
machines. Bounded projection gives NP membership for each bit; their union
allows either bit. The proof includes positions zero and the full length.

This proves only the posted closure statement in PvsNP.Defs.
-/

namespace PvsNP.Units.tc_closure_del_one_np

def insert (b : Bool) (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.length ++ b :: p.1.drop p.2.length

theorem insert_polytime (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (insert b) := by
  have ht : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_tm_pair_swap_polytime
      PvsNP.Units.m2_take_drop_length_polytime.1
  have hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_tm_pair_swap_polytime
      PvsNP.Units.m2_take_drop_length_polytime.2
  have hb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => b :: p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hd
      (PvsNP.Units.m2_join_karp_sides.cpt_cons b)
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ ht hb)
    PvsNP.Units.m2_pair_build_polytime.cpt_append

def one (L : Language Bool) (b : Bool) : Language Bool :=
  {x | ∃ c : List Bool, c.length ≤ x.length ∧ insert b (x, c) ∈ L}

theorem one_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) (b : Bool) :
    one L b ∈ PvsNP.NP := by
  simpa only [one, Language, Polynomial.eval_X] using
    (PvsNP.Units.m2_np_projection L (insert b) Polynomial.X hL (insert_polytime b))

theorem mem_one (L : Language Bool) (b : Bool) (x : List Bool) :
    x ∈ one L b ↔ ∃ u v : List Bool, x = u ++ v ∧ u ++ b :: v ∈ L := by
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨x.take c.length, x.drop c.length,
      (List.take_append_drop c.length x).symm, hc⟩
  · rintro ⟨u, v, hx, hm⟩
    refine ⟨List.replicate u.length false, ?_, ?_⟩
    · simp [hx]
    · simpa [insert, hx] using hm

theorem deletion_eq (L : Language Bool) :
    ({x : List Bool | ∃ (u v : List Bool) (b : Bool),
      x = u ++ v ∧ u ++ b :: v ∈ L} : Language Bool) = one L false ⊔ one L true := by
  ext x
  change (∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L) ↔
    x ∈ one L false ∨ x ∈ one L true
  rw [mem_one, mem_one]
  constructor
  · rintro ⟨u, v, b, hx, hm⟩
    cases b with
    | false => exact Or.inl ⟨u, v, hx, hm⟩
    | true => exact Or.inr ⟨u, v, hx, hm⟩
  · rintro (⟨u, v, hx, hm⟩ | ⟨u, v, hx, hm⟩)
    · exact ⟨u, v, false, hx, hm⟩
    · exact ⟨u, v, true, hx, hm⟩

end PvsNP.Units.tc_closure_del_one_np

theorem PvsNP.Units.tc_closure_del_one_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({x : List Bool | ∃ (u v : List Bool) (b : Bool),
        x = u ++ v ∧ u ++ b :: v ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_del_one_np.deletion_eq]
  exact PvsNP.Units.m2_np_union _ _
    (PvsNP.Units.tc_closure_del_one_np.one_in_np L hL false)
    (PvsNP.Units.tc_closure_del_one_np.one_in_np L hL true)
