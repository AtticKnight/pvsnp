import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.m2_tm_count_binary
import PvsNP.Units.m2_pair_build_polytime

open PvsNP.Units.tr_rel_val_coprime

/-- Read the two binary occurrence counts and test their gcd with the binary coprimality decider. -/
theorem PvsNP.Units.tl_lang_count_coprime_p :
    ({x : List Bool | Nat.gcd (x.count true) (x.count false) = 1} : Language Bool) ∈ PvsNP.P := by
  have flipCount (x : List Bool) : (x.map (!·)).count true = x.count false := by
    induction x with
    | nil => rfl
    | cons b xs ih => cases b <;> simp [List.count_cons, ih]
  have hfalse : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.count false)) := by
    simpa only [flipCount] using PvsNP.Units.m2_pair_build_polytime.cpt_comp
      cpt_notBits PvsNP.Units.m2_tm_count_binary
  let counts := fun x : List Bool => (Nat.bits (x.count true), Nat.bits (x.count false))
  have hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair counts :=
    PvsNP.Units.m2_pair_build_polytime _ _ PvsNP.Units.m2_tm_count_binary hfalse
  obtain ⟨f, hf, spec⟩ := PvsNP.Units.tr_rel_val_coprime
  refine ⟨fun x => f (counts x), PvsNP.Units.m2_pair_build_polytime.cpt_comp hc hf, ?_⟩
  intro x
  have eqn := spec (counts x)
  change (Nat.gcd (val (Nat.bits (x.count true))) (val (Nat.bits (x.count false))) = 1 ↔ f (counts x) = true) at eqn
  simpa only [val_bits] using eqn
