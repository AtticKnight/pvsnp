import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_p_inter


/-
  Original work for the make.fun desk campaign `pvsnp`, unit
  `m2_bool_combine_polytime`: a Boolean combination of two polynomial-time
  tests is polynomial-time.

  Proof idea: an arbitrary binary Boolean operation `op` is reassembled from
  its four truth-table entries,

    op a b = ((a && b) && op true true) || ((a && !b) && op true false)
             || ((!a && b) && op false true) || ((!a && !b) && op false false),

  and each piece is polynomial-time by the settled closure properties carried
  in `PvsNP.Units.m2_p_inter`: intersection and union of polynomial-time
  decidable languages (its closing theorem and its `p_union`), and flipping a
  polynomial-time decider's answer (its `polyTimeComputable_not`). Constant
  answers are obtained from `f` itself, as `f x || !f x` and `f x && !f x`.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_bool_combine_polytime

/-- Polynomial-time computability is closed under pointwise `&&`: the
intersection of the two yes-languages is in `PvsNP.P` by the settled unit
`m2_p_inter`, and its decider computes `f x && g x` pointwise. -/
theorem ptc_and {f g : List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => f x && g x) := by
  have hfP : PvsNP.PolyTimeDecidable {x | f x = true} := ⟨f, hf, fun x => Iff.rfl⟩
  have hgP : PvsNP.PolyTimeDecidable {x | g x = true} := ⟨g, hg, fun x => Iff.rfl⟩
  have hP : PvsNP.PolyTimeDecidable ({x | f x = true} ⊓ {x | g x = true}) :=
    PvsNP.Units.m2_p_inter _ _ hfP hgP
  obtain ⟨h, hh, hdec⟩ := hP
  have e : (fun x => f x && g x) = h := by
    funext x
    have k : (f x = true ∧ g x = true) ↔ h x = true := by
      have e1 : (x ∈ {x | f x = true} ∧ x ∈ {x | g x = true}) ↔ h x = true :=
        hdec x
      exact (and_congr Iff.rfl Iff.rfl).symm.trans e1
    cases hfx : f x <;> cases hgx : g x <;> cases hhx : h x <;> simp_all
  rw [e]
  exact hh

/-- Polynomial-time computability is closed under pointwise `||`: the union
of the two yes-languages is in `PvsNP.P` by `p_union` inside the settled unit
`m2_p_inter`, and its decider computes `f x || g x` pointwise. -/
theorem ptc_or {f g : List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => f x || g x) := by
  have hfP : PvsNP.PolyTimeDecidable {x | f x = true} := ⟨f, hf, fun x => Iff.rfl⟩
  have hgP : PvsNP.PolyTimeDecidable {x | g x = true} := ⟨g, hg, fun x => Iff.rfl⟩
  have hP : PvsNP.PolyTimeDecidable ({x | f x = true} ⊔ {x | g x = true}) :=
    PvsNP.Units.m2_p_inter.p_union _ _ hfP hgP
  obtain ⟨h, hh, hdec⟩ := hP
  have e : (fun x => f x || g x) = h := by
    funext x
    have k : (f x = true ∨ g x = true) ↔ h x = true := by
      have e1 : (x ∈ {x | f x = true} ∨ x ∈ {x | g x = true}) ↔ h x = true :=
        hdec x
      exact (or_congr Iff.rfl Iff.rfl).symm.trans e1
    cases hfx : f x <;> cases hgx : g x <;> cases hhx : h x <;> simp_all
  rw [e]
  exact hh

/-- Polynomial-time computability is closed under pointwise negation, by
`polyTimeComputable_not` inside the settled unit `m2_p_inter`. -/
theorem ptc_not {f : List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => !f x) :=
  PvsNP.Units.m2_p_inter.polyTimeComputable_not hf

/-- Every constant yes/no answer is polynomial-time computable, built from
any polynomial-time `f`: constantly `true` is `f x || !f x` and constantly
`false` is `f x && !f x`. -/
theorem ptc_const {f : List Bool → Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun _ => b) := by
  cases b with
  | true =>
    have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x => f x || !f x) :=
      ptc_or hf (ptc_not hf)
    have e : (fun x => f x || !f x) = (fun _ => true) := by
      funext x
      cases hfx : f x <;> rfl
    rwa [e] at h1
  | false =>
    have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x => f x && !f x) :=
      ptc_and hf (ptc_not hf)
    have e : (fun x => f x && !f x) = (fun _ => false) := by
      funext x
      cases hfx : f x <;> rfl
    rwa [e] at h1

/-- The unit's statement, proved by decomposing `op` into its truth table
and reassembling it from `&&`, `||`, `!` and constant pieces. -/
theorem bool_combine (op : Bool → Bool → Bool) (f g : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => op (f x) (g x)) := by
  have hnf := ptc_not hf
  have hng := ptc_not hg
  have p1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => (f x && g x) && op true true) :=
    ptc_and (ptc_and hf hg) (ptc_const hf (op true true))
  have p2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => (f x && !g x) && op true false) :=
    ptc_and (ptc_and hf hng) (ptc_const hf (op true false))
  have p3 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => (!f x && g x) && op false true) :=
    ptc_and (ptc_and hnf hg) (ptc_const hf (op false true))
  have p4 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => (!f x && !g x) && op false false) :=
    ptc_and (ptc_and hnf hng) (ptc_const hf (op false false))
  have q1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => ((f x && g x) && op true true)
        || ((f x && !g x) && op true false)) :=
    ptc_or p1 p2
  have q2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => (((f x && g x) && op true true)
          || ((f x && !g x) && op true false))
        || ((!f x && g x) && op false true)) :=
    ptc_or q1 p3
  have big : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x => ((((f x && g x) && op true true)
            || ((f x && !g x) && op true false))
          || ((!f x && g x) && op false true))
        || ((!f x && !g x) && op false false)) :=
    ptc_or q2 p4
  have e : (fun x => op (f x) (g x))
      = (fun x => ((((f x && g x) && op true true)
            || ((f x && !g x) && op true false))
          || ((!f x && g x) && op false true))
        || ((!f x && !g x) && op false false)) := by
    funext x
    cases hfx : f x <;> cases hgx : g x <;> simp
  rwa [e]

end PvsNP.Units.m2_bool_combine_polytime


/-- A Boolean combination of two polynomial-time tests is polynomial-time
(TM2): reassemble `op` from its truth table using closure of polynomial-time
computability under `&&`, `||`, `!` and constants. -/
theorem PvsNP.Units.m2_bool_combine_polytime :
    ∀ (op : Bool → Bool → Bool) (f g : List Bool → Bool),
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f →
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => op (f x) (g x)) :=
  PvsNP.Units.m2_bool_combine_polytime.bool_combine
