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

namespace PvsNP.Units.tc_closure_del_block_np

def insert (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.length ++ true :: false :: p.1.drop p.2.length

theorem insert_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString insert := by
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
  have hf : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => false :: p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hd
      (PvsNP.Units.m2_join_karp_sides.cpt_cons false)
  have hb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => true :: false :: p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hf
      (PvsNP.Units.m2_join_karp_sides.cpt_cons true)
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ ht hb)
    PvsNP.Units.m2_pair_build_polytime.cpt_append

def one (L : Language Bool) : Language Bool :=
  {x | ∃ c : List Bool, c.length ≤ x.length ∧ insert (x, c) ∈ L}

theorem one_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) : one L ∈ PvsNP.NP := by
  simpa only [one, Language, Polynomial.eval_X] using
    (PvsNP.Units.m2_np_projection L insert Polynomial.X hL insert_polytime)

theorem block_eq (L : Language Bool) :
    ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L} :
      Language Bool) = one L := by
  ext x
  change (∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L) ↔ x ∈ one L
  constructor
  · rintro ⟨u, v, hx, hm⟩
    refine ⟨List.replicate u.length false, ?_, ?_⟩
    · simp [hx]
    · simpa [insert, hx] using hm
  · rintro ⟨c, _, hc⟩
    refine ⟨x.take c.length, x.drop c.length, (List.take_append_drop c.length x).symm, ?_⟩
    simpa [insert] using hc

end PvsNP.Units.tc_closure_del_block_np

theorem PvsNP.Units.tc_closure_del_block_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_del_block_np.block_eq]
  exact PvsNP.Units.tc_closure_del_block_np.one_in_np L hL
