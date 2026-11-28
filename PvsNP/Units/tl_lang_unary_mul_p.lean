import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_unary_add_p

namespace PvsNP.Units.tl_lang_unary_mul_p

open PvsNP.Units.tl_lang_unary_add_p
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Copy the true bits that occur after exactly the selected number of separators. -/
private def copyField (which q : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  (nxt q b, if b && decide (q = which) then some true else none)

private def word (a b c : ℕ) : List Bool :=
  List.replicate a true ++ (false :: (List.replicate b true ++
    (false :: (List.replicate c true ++ []))))

private theorem fields (a b c : ℕ) :
    run (copyField 0) 0 (word a b c) = List.replicate a true ∧
    run (copyField 1) 0 (word a b c) = List.replicate b true := by
  unfold word
  constructor
  · rw [run_rep_some (copyField 0) 0 true rfl, run, show copyField 0 0 false = (1, none) from rfl,
      run_rep_none (copyField 0) 1 rfl, run, show copyField 0 1 false = (2, none) from rfl,
      run_rep_none (copyField 0) 2 rfl]
    simp [run]
  · rw [run_rep_none (copyField 1) 0 rfl, run, show copyField 1 0 false = (1, none) from rfl,
      run_rep_some (copyField 1) 1 true rfl, run, show copyField 1 1 false = (2, none) from rfl,
      run_rep_none (copyField 1) 2 rfl]
    simp [run]

private def productField (x : List Bool) := mulU (run (copyField 0) 0 x) (run (copyField 1) 0 x)

private theorem contents (a b c : ℕ) :
    productField (word a b c) = run δB 0 (word a b c) ↔ a * b = c := by
  obtain ⟨h₀,h₁⟩ := fields a b c
  rw [productField, h₀, h₁, show run δB 0 (word a b c) = List.replicate c true from runB_val a b c]
  constructor
  · intro h
    simpa [mulU, un] using congrArg List.length h
  · intro h
    simp [mulU, un, h]

private def accepts (x : List Bool) := shapeOk x && decide (productField x = run δB 0 x)

private theorem cost : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer accepts := by
  have shapeCost := cpt_eq_fun (run δC 0) (fun _ => [true,true]) (cpt_run δC 0)
    (PvsNP.Units.m2_const_polytime [true,true])
  have productCost : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString productField :=
    cpt_mulU2 (cpt_run (copyField 0) 0) (cpt_run (copyField 1) 0)
  exact PvsNP.Units.m2_bool_combine_polytime (· && ·) shapeOk _ shapeCost
    (cpt_eq_fun productField (run δB 0) productCost (cpt_run δB 0))

end PvsNP.Units.tl_lang_unary_mul_p

open PvsNP.Units.tl_lang_unary_add_p PvsNP.Units.tl_lang_unary_mul_p in
theorem PvsNP.Units.tl_lang_unary_mul_p :
    ({x : List Bool | ∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++
      false :: List.replicate (a * b) true} : Language Bool) ∈ PvsNP.P := by
  refine ⟨accepts, cost, ?_⟩
  intro x
  change (∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++
    false :: List.replicate (a * b) true) ↔ accepts x = true
  simp only [accepts, shapeOk, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hx⟩
    have w : x = word a b (a*b) := hx.trans (nf a b (a*b))
    rw [w]
    exact ⟨by rw [runC_eq]; simp [word, List.count_replicate], (contents a b (a*b)).2 rfl⟩
  · rintro ⟨shape, product⟩
    rw [runC_eq] at shape
    have count : x.count false = 2 := by simpa using congrArg List.length shape
    obtain ⟨a, y, hx, hy⟩ := count_succ 1 x count
    obtain ⟨b, z, hy', hz⟩ := count_succ 0 y hy
    have w : x = word a b z.length := by
      unfold word
      rw [hx, hy', ← count_zero z hz]
      simp
    rw [w] at product
    have eqn := (contents a b z.length).1 product
    exact ⟨a, b, w.trans ((congrArg (word a b) eqn.symm).trans (nf a b (a*b)).symm)⟩
