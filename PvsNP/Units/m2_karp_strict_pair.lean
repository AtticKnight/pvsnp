import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_not_in_p
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_finite_patch

set_option autoImplicit false

theorem PvsNP.Units.m2_karp_strict_pair :
    ∃ L₁ L₂ : Language Bool, (∃ x : List Bool, x ∈ L₁) ∧ (∃ x : List Bool, x ∉ L₁) ∧
      PvsNP.KarpReducible L₁ L₂ ∧ ¬ PvsNP.KarpReducible L₂ L₁ := by
  classical
  obtain ⟨L₂, _, hL₂_not_P⟩ := PvsNP.Units.m2_exp_not_in_p
  have hy : ∃ y : List Bool, y ∈ L₂ := by
    by_contra h
    push Not at h
    have hempty : L₂ = (∅ : Set (List Bool)) := by
      ext x
      exact ⟨fun hx => absurd hx (h x), fun hx => (hx : False).elim⟩
    rw [hempty] at hL₂_not_P
    exact hL₂_not_P PvsNP.Units.m2_p_trivial.1
  have hz : ∃ z : List Bool, z ∉ L₂ := by
    by_contra h
    push Not at h
    have huniv : L₂ = (Set.univ : Set (List Bool)) := by
      ext x
      exact ⟨fun _ => trivial, fun _ => h x⟩
    rw [huniv] at hL₂_not_P
    exact hL₂_not_P PvsNP.Units.m2_p_trivial.2
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  let L₁ : Language Bool := {x : List Bool | x = [true]}
  have hL₁_P : L₁ ∈ PvsNP.P := by
    have hg := PvsNP.Units.m2_polytime_finite_patch (fun _ => [false])
      (fun x => [decide (x = [true])]) {[true]}
      (PvsNP.Units.m2_const_polytime [false])
      (fun x hx => by simp only [Finset.mem_singleton] at hx; simp [hx])
    obtain ⟨cg⟩ := hg
    refine ⟨fun x => decide (x = [true]),
      ⟨{ tm := cg.tm, inputAlphabet := cg.inputAlphabet, outputAlphabet := cg.outputAlphabet,
         time := cg.time, outputsFun := cg.outputsFun }⟩,
      fun x => by change x = [true] ↔ decide (x = [true]) = true; simp⟩
  let g : List Bool → List Bool := fun w => if w = [true] then y else z
  have hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g :=
    PvsNP.Units.m2_polytime_finite_patch (fun _ => z) g {[true]}
      (PvsNP.Units.m2_const_polytime z)
      (fun w hw => by simp only [Finset.mem_singleton] at hw; simp [g, hw])
  refine ⟨L₁, L₂, ⟨[true], rfl⟩, ⟨[], fun h => by cases h⟩, ⟨g, hg, fun x => ?_⟩, fun hred => ?_⟩
  · change x = [true] ↔ g x ∈ L₂
    by_cases hx : x = [true]
    · simp [g, hx, hy]
    · simp [g, hx, hz]
  · exact hL₂_not_P (PvsNP.Units.m2_p_down_closed L₂ L₁ hred hL₁_P)
