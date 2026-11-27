import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_ino_trans :
    ∀ f g h : ℕ → ℕ, inO f g → inO g h → inO f h := by
  rintro f g h ⟨c1, n1, h1⟩ ⟨c2, n2, h2⟩
  refine ⟨c1 * c2, max n1 n2, fun n hn => ?_⟩
  have hfg := h1 n (le_trans (le_max_left n1 n2) hn)
  have hgh := h2 n (le_trans (le_max_right n1 n2) hn)
  calc f n ≤ c1 * g n := hfg
    _ ≤ c1 * (c2 * h n) := Nat.mul_le_mul_left c1 hgh
    _ = c1 * c2 * h n := (Nat.mul_assoc c1 c2 (h n)).symm
