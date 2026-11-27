import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_length_projection
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_padded_test_exp

namespace PvsNP.Units.tc_exp_length_proj

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

abbrev W := List Bool
abbrev C (f : W → W) := PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f
def pad (k : ℕ) (x : W) := un (2 ^ (x.length ^ k) + k) ++ false :: x
def word (x : W) (i : ℕ) := PvsNP.Units.m2_np_length_projection.G (x, cand i)

theorem word_len (x : W) (i : ℕ) : (word x i).length = x.length := by
  rw [word, PvsNP.Units.m2_np_length_projection.F_eq]
  simp only [List.length_take, List.length_append]
  omega

theorem word_idx (x y : W) (h : y.length = x.length) : word x (idx y) = y := by
  rw [word, cand_idx, PvsNP.Units.m2_np_length_projection.F_eq, ← h, List.take_left]

def query (z : W) : W :=
  hd (unpairB (unpairB z).1).1 ++ false ::
    word (unpairB (unpairB z).1).2 (unpairB z).2.length

theorem query_poly : C query := by
  have hleft := cpt_comp cpt_unpairB1 cpt_unpairB1
  have hp := cpt_comp hleft cpt_hd
  have hx := cpt_comp cpt_unpairB1 cpt_unpairB2
  have hc := cpt_iterGrow bf_cpt_succB 1 bf_succB_length cpt_unpairB2 (cpt_const [])
  have hw := cpt_comp (PvsNP.Units.m2_pair_build_polytime _ _ hx hc) PvsNP.Units.m2_np_length_projection.hG
  have h := cpt_app2 hp (cpt_cons1 false hw)
  exact h

def verify (d : W → Bool) (p : W × W) := d (query (pairB p.1 p.2))
def search (d : W → Bool) (w : W) :=
  (List.range (w.length + 1)).any (fun i => verify d (w, List.replicate i true))
def whole (d : W → Bool) (p : W × W) := search d (pairB p.1 p.2)

theorem whole_poly (d : W → Bool) (h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer d) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (whole d) := by
  have hq := cpt_comp cpt_pairB query_poly
  have hv := cpt_comp hq h
  have hs := PvsNP.Units.m2_bounded_unary_search_polytime (verify d) hv
  have hend := cpt_comp cpt_pairB hs
  exact hend

theorem verify_at (d : W → Bool) (k : ℕ) (x : W) (i : ℕ) :
    verify d (pairB (pad k x) x, List.replicate i true) = d (pad k (word x i)) := by
  simp only [verify, query, unpairB_pairB, List.length_replicate, pad, hd_un, word_len]

theorem covered (k : ℕ) (hk : 0 < k) (x y : W) (h : y.length = x.length) :
    idx y ≤ (pairB (pad k x) x).length := by
  have hn : x.length ≤ x.length ^ k := Nat.le_self_pow (Nat.ne_of_gt hk) _
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hi := idx_bound y
  rw [h, pow_succ] at hi
  simp only [pairB_length, pad, un, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem raised (n k : ℕ) : 2 ^ (n ^ k) + k ≤ 2 ^ (n ^ (k+1)) + (k+1) := by
  cases n with
  | zero => cases k <;> simp
  | succ a =>
    have he : (a+1)^k ≤ (a+1)^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) he
    omega

theorem projection :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y ∈ L, y.length = x.length) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L ⟨k, f, M, accepts, time⟩
  obtain ⟨d, hd, mem⟩ := PvsNP.Units.m2_upward_padding L (k+1)
    ⟨f, M, accepts, fun n => (time n).trans (raised n k)⟩
  have decodes (z : W) : d (pad (k+1) z) = true ↔ z ∈ L := by
    constructor
    · intro hz
      obtain ⟨y, hy, eq⟩ := (mem _).2 hz
      change pad (k+1) z = pad (k+1) y at eq
      have e : z = y := by simpa only [pad, dropN_un] using congrArg dropN eq
      exact e.symm ▸ hy
    · intro hz
      exact (mem _).1 ⟨z, hz, rfl⟩
  have hid : C id := ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  obtain ⟨j, N, limit⟩ := PvsNP.Units.m2_padded_test_exp (k+1) id id (whole d) hid hid (whole_poly d hd)
  refine ⟨j, _, N, ?_, limit⟩
  intro x
  change (∃ y ∈ L, y.length = x.length) ↔ search d (pairB (pad (k+1) x) x) = true
  rw [search, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, same⟩
    have hi := covered (k+1) (by omega) x y same
    refine ⟨idx y, List.mem_range.mpr (by omega), ?_⟩
    rw [verify_at, word_idx x y same]
    exact (decodes y).2 hy
  · rintro ⟨i, _, hi⟩
    rw [verify_at] at hi
    exact ⟨word x i, (decodes _).1 hi, word_len x i⟩

end PvsNP.Units.tc_exp_length_proj

/-- Use the exponential padding as a unary search budget. Each shortlex word of the required length is visited, and each test reuses the padded decider. -/
theorem PvsNP.Units.tc_exp_length_proj :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y ∈ L, y.length = x.length) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_length_proj.projection
