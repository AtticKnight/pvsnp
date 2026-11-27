import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_poly_clock
import PvsNP.Units.tl_lang_val_pow_p

namespace PvsNP.Units.m2_z_padded_conp_back

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.tl_lang_val_pow_p

theorem pad_inj : ∀ (n n' : ℕ) (x x' : List Bool),
    List.replicate n true ++ false :: x = List.replicate n' true ++ false :: x' → x = x'
  | 0, 0, x, x', h => by simpa using h
  | 0, n' + 1, x, x', h => by simp [List.replicate_succ] at h
  | n + 1, 0, x, x', h => by simp [List.replicate_succ] at h
  | n + 1, n' + 1, x, x', h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    exact pad_inj n n' x x' h

theorem pad_poly (k : ℕ) : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length ^ k) true ++ false :: x) := by
  have hc := PvsNP.Units.m2_poly_clock ((Polynomial.X : Polynomial ℕ) ^ k)
  have h := cpt_app2 (toCpt hc) (cpt_cons1 false cpt_id)
  have e : (fun s : List Bool =>
      List.replicate (((Polynomial.X : Polynomial ℕ) ^ k).eval s.length) true ++ false :: s) =
      (fun x : List Bool => List.replicate (x.length ^ k) true ++ false :: x) := by
    funext s
    simp
  rw [e] at h
  rw [encodeString_eq]
  exact h

end PvsNP.Units.m2_z_padded_conp_back

theorem PvsNP.Units.m2_z_padded_conp_back : ∀ (L : Language Bool) (k : ℕ), ({s : List Bool | ∃ x : List Bool, x ∈ L ∧ s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.coNP → L ∈ PvsNP.coNP := by
  intro L k h
  refine PvsNP.Units.m2_conp_down_closed L _ ⟨_, PvsNP.Units.m2_z_padded_conp_back.pad_poly k, ?_⟩ h
  intro x
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', e⟩
    have := PvsNP.Units.m2_z_padded_conp_back.pad_inj _ _ _ _ e
    rw [this]
    exact hx'
