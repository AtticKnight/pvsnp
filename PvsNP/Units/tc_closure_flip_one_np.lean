import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_zip_bne_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on settled units of github.com/makedotfun/pvsnp (Apache License 2.0), which this file
imports: the bounded projection m2_np_projection, the closure lemmas m2_np_inter,
m2_p_subset_np, m2_p_compl and m2_p_finite, and the polynomial-time pieces m2_transducer_polytime,
m2_prod_map_polytime, m2_tm_pair_swap_polytime, m2_pair_split_polytime, m2_tm_pair_fork_polytime,
m2_zip_bne_polytime and m2_polytime_comp. The certificate `c` names the flipped position
`c.length - 1`; the flip is the bitwise xor of `x` with a one-hot mask.
-/

namespace PvsNP.Units.tc_closure_flip_one_np

/-- The one-hot head of the mask: `false` repeated (`x.length - 1`, or `x.length` once the first
symbol is dropped), then `true`. -/
def T (q : Bool) (x : List Bool) : List Bool :=
  List.replicate (if q then x.length else x.length - 1) false ++ [true]

/-- All-false padding as long as the input. -/
def Z (_ : Unit) (x : List Bool) : List Bool :=
  List.replicate x.length false

theorem cpt_T : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (T false) :=
  PvsNP.Units.m2_transducer_polytime Bool (fun q _ => (true, if q then some false else none))
    (fun _ => some true) T
    (by intro q; cases q <;> simp [T])
    (by intro q b x; cases q <;> simp [T, List.replicate_succ]) false

theorem cpt_Z : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (Z ()) :=
  PvsNP.Units.m2_transducer_polytime Unit (fun _ _ => ((), some false)) (fun _ => none) Z
    (by intro q; simp [Z])
    (by intro q b x; simp [Z, List.replicate_succ]) ()

/-- The mask for the pair `(x, c)`. -/
def mask (p : List Bool × List Bool) : List Bool := T false p.2 ++ Z () p.1

/-- Flip the bit of `p.1` at position `p.2.length - 1`. -/
def g (p : List Bool × List Bool) : List Bool :=
  List.zipWith (fun a b : Bool => a != b) p.1 (mask p)

theorem cpt_mask : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString mask := by
  have h1 := PvsNP.Units.m2_prod_map_polytime (Z ()) (T false) cpt_Z cpt_T
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodePair _ _
    h1 PvsNP.Units.m2_tm_pair_swap_polytime
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString _ _
    h2 PvsNP.Units.m2_pair_split_polytime.2.2

theorem cpt_g : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g := by
  have hf := PvsNP.Units.m2_tm_pair_fork_polytime (fun p : List Bool × List Bool => p.1) mask
    PvsNP.Units.m2_pair_split_polytime.1 cpt_mask
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString _ _
    hf PvsNP.Units.m2_zip_bne_polytime

theorem mask_eq (x c : List Bool) :
    mask (x, c) = List.replicate (c.length - 1) false ++ true :: List.replicate x.length false := by
  simp [mask, T, Z]

theorem zip_rep (v : List Bool) : ∀ m : ℕ, v.length ≤ m →
    List.zipWith (fun a b : Bool => a != b) v (List.replicate m false) = v := by
  induction v with
  | nil => intro m _; simp
  | cons a v ih =>
      intro m hm
      cases m with
      | zero => simp at hm
      | succ m =>
          rw [List.replicate_succ, List.zipWith_cons_cons, ih m (by simp at hm; omega)]
          simp

theorem zip_app (u w r : List Bool) :
    List.zipWith (fun a b : Bool => a != b) (u ++ w) (List.replicate u.length false ++ r) =
      u ++ List.zipWith (fun a b : Bool => a != b) w r := by
  induction u with
  | nil => simp
  | cons a u ih =>
      rw [List.length_cons, List.replicate_succ, List.cons_append, List.cons_append,
        List.zipWith_cons_cons, ih]
      simp

theorem g_flip (u v : List Bool) (b : Bool) (c : List Bool) (hc : c.length - 1 = u.length) :
    g (u ++ b :: v, c) = u ++ (!b) :: v := by
  show List.zipWith (fun a b : Bool => a != b) (u ++ b :: v) (mask (u ++ b :: v, c)) = _
  rw [mask_eq, hc, zip_app, List.zipWith_cons_cons, zip_rep v _ (by simp; omega)]
  simp

/-- The nonempty strings. -/
def NE : Language Bool := {x | x ≠ []}

theorem ne_mem : NE ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_p_compl _ (PvsNP.Units.m2_p_finite {[]})
  have e : NE = ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool)ᶜ := by
    ext x
    show x ≠ [] ↔ ¬ (x ∈ ({[]} : Finset (List Bool)))
    simp
  rw [e]
  exact h

theorem set_eq (L : Language Bool) :
    ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L} :
        Language Bool) =
      ({x : List Bool | ∃ c : List Bool, c.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧
        g (x, c) ∈ L} : Language Bool) ⊓ NE := by
  ext x
  show (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L) ↔
    (∃ c : List Bool, c.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧ g (x, c) ∈ L) ∧
      x ≠ []
  constructor
  · rintro ⟨u, v, b, rfl, h⟩
    refine ⟨⟨List.replicate (u.length + 1) false, ?_, ?_⟩, by simp⟩
    · simp [Polynomial.eval_X]
    · rw [g_flip u v b _ (by simp)]
      exact h
  · rintro ⟨⟨c, hc, hg⟩, hne⟩
    have hpos := List.length_pos_of_ne_nil hne
    rw [Polynomial.eval_X] at hc
    have hd : x.drop (c.length - 1) ≠ [] := by
      intro h
      rw [List.drop_eq_nil_iff] at h
      omega
    obtain ⟨b, v, hbv⟩ := List.exists_cons_of_ne_nil hd
    have hx : x = x.take (c.length - 1) ++ b :: v := by
      rw [← hbv, List.take_append_drop]
    have hu : (x.take (c.length - 1)).length = c.length - 1 := by
      rw [List.length_take]
      omega
    refine ⟨x.take (c.length - 1), v, b, hx, ?_⟩
    have hf := g_flip (x.take (c.length - 1)) v b c hu.symm
    rw [← hx] at hf
    rw [← hf]
    exact hg

end PvsNP.Units.tc_closure_flip_one_np

/-- NP is closed under flipping one bit (TM2): guess the position as the length of a
certificate, flip it, and ask the verifier of `L`. -/
theorem PvsNP.Units.tc_closure_flip_one_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ (!b) :: v ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_flip_one_np.set_eq L]
  exact PvsNP.Units.m2_np_inter _ _
    (PvsNP.Units.m2_np_projection L PvsNP.Units.tc_closure_flip_one_np.g Polynomial.X hL
      PvsNP.Units.tc_closure_flip_one_np.cpt_g)
    (PvsNP.Units.m2_p_subset_np PvsNP.Units.tc_closure_flip_one_np.ne_mem)
