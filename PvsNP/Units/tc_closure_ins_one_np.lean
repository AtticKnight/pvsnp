import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np

/-!
Original closure proof. A unary certificate names the deletion position: the
certificate has length one more than the position it names, so the position is
the length of the certificate's tail. The deletion map is a composition of the
campaign's settled take/drop, tail and pairing machines. Bounded projection
gives NP membership for the projected language, which is the insertion language
except for the empty string (the empty string has no bit to delete); intersecting
with the complement of the singleton empty string removes that one case.

This proves only the posted closure statement in PvsNP.Defs.
-/

namespace PvsNP.Units.tc_closure_ins_one_np

/-- Delete the bit at the position named by the certificate: the certificate's
tail has the position as its length. -/
def delete (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.tail.length ++ (p.1.drop p.2.tail.length).tail

theorem delete_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString delete := by
  have htail : PvsNP.PolyTimeComputable (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.tail) :=
    PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.cpt_tail
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.2.tail)) :=
    PvsNP.Units.m2_pair_build_polytime.cpt_second htail
  have ht : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take p.2.tail.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpair
      (PvsNP.Units.m2_polytime_comp _ _ _ _ _
        PvsNP.Units.m2_tm_pair_swap_polytime
        PvsNP.Units.m2_take_drop_length_polytime.1)
  have hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.1.drop p.2.tail.length).tail) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      (PvsNP.Units.m2_polytime_comp _ _ _ _ _ hpair
        (PvsNP.Units.m2_polytime_comp _ _ _ _ _
          PvsNP.Units.m2_tm_pair_swap_polytime
          PvsNP.Units.m2_take_drop_length_polytime.2))
      htail
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ ht hd)
    PvsNP.Units.m2_pair_build_polytime.cpt_append

/-- The strings with a deletion in `L`, as a bounded projection of `delete`. -/
def one (L : Language Bool) : Language Bool :=
  {x | ∃ c : List Bool, c.length ≤ x.length ∧ delete (x, c) ∈ L}

theorem one_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) :
    one L ∈ PvsNP.NP := by
  simpa only [one, Language, Polynomial.eval_X] using
    (PvsNP.Units.m2_np_projection L delete Polynomial.X hL delete_polytime)

theorem ins_eq (L : Language Bool) :
    ({x : List Bool | ∃ (u v : List Bool) (b : Bool),
      x = u ++ b :: v ∧ u ++ v ∈ L} : Language Bool) =
      one L ⊓ {x : List Bool | x ≠ []} := by
  ext x
  simp only [one, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨u, v, b, hx, hm⟩
    refine ⟨⟨List.replicate (u.length + 1) false, ?_, ?_⟩, ?_⟩
    · have hcl : (List.replicate (u.length + 1) false).length = u.length + 1 :=
        List.length_replicate
      rw [hcl, hx, List.length_append, List.length_cons]
      omega
    · subst hx
      have hpos : (List.replicate (u.length + 1) false).tail.length = u.length := by simp
      simp only [delete, hpos, List.take_left, List.drop_left, List.tail_cons]
      exact hm
    · intro hnil
      rw [hx] at hnil
      have h0 := congrArg List.length hnil
      simp only [List.length_append, List.length_cons, List.length_nil] at h0
      omega
  · rintro ⟨⟨c, hc_len, hc⟩, hxne⟩
    have hxlen : 0 < x.length := by
      cases x with
      | nil => exact absurd rfl hxne
      | cons b v => exact Nat.zero_lt_succ _
    have hi : c.tail.length < x.length := by
      cases c with
      | nil => exact hxlen
      | cons d c' =>
        have hc' : c'.length + 1 ≤ x.length := hc_len
        simp only [List.tail_cons]
        omega
    obtain ⟨b, v, hbv⟩ : ∃ b v, x.drop c.tail.length = b :: v := by
      have hne : x.drop c.tail.length ≠ [] := by
        intro hnil
        have h0 : (x.drop c.tail.length).length = 0 := by rw [hnil]; rfl
        rw [List.length_drop] at h0
        omega
      cases hl : x.drop c.tail.length with
      | nil => exact absurd hl hne
      | cons b v =>
        refine ⟨b, v, ?_⟩
        rw [← hl]
    refine ⟨x.take c.tail.length, v, b, ?_, ?_⟩
    · exact (List.take_append_drop c.tail.length x).symm.trans (by rw [hbv])
    · have hdel : delete (x, c) = x.take c.tail.length ++ v := by
        simp only [delete, hbv, List.tail_cons]
      rw [← hdel]
      exact hc

theorem nonempty_in_np :
    ({x : List Bool | x ≠ []} : Language Bool) ∈ PvsNP.NP := by
  have hfin : ({x : List Bool | x = []} : Language Bool) ∈ PvsNP.P := by
    simpa using PvsNP.Units.m2_p_finite ({[]} : Finset (List Bool))
  have hcomp : ({x : List Bool | x ≠ []} : Language Bool) =
      ({x : List Bool | x = []} : Language Bool)ᶜ := by
    ext y
    simp
  rw [hcomp]
  exact PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_compl _ hfin)

end PvsNP.Units.tc_closure_ins_one_np

/-- NP is closed under inserting one bit (TM2). -/
theorem PvsNP.Units.tc_closure_ins_one_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({x : List Bool | ∃ (u v : List Bool) (b : Bool),
        x = u ++ b :: v ∧ u ++ v ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_ins_one_np.ins_eq]
  exact PvsNP.Units.m2_np_inter _ _
    (PvsNP.Units.tc_closure_ins_one_np.one_in_np L hL)
    (PvsNP.Units.tc_closure_ins_one_np.nonempty_in_np)
