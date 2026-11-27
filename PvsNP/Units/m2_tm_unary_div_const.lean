import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_const_polytime

theorem PvsNP.Units.m2_tm_unary_div_const : ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length / k) true) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    simpa using PvsNP.Units.m2_const_polytime []
  · have hk1 : 0 < k := Nat.pos_of_ne_zero hk
    have h := PvsNP.Units.m2_transducer_polytime (Fin k)
      (fun q _ => (⟨(q.val + 1) % k, Nat.mod_lt _ hk1⟩, if q.val + 1 = k then some true else none))
      (fun _ => none)
      (fun q x => List.replicate ((x.length + q.val) / k) true)
      (by
        intro q
        simp [Nat.div_eq_of_lt q.isLt])
      (by
        intro q b x
        by_cases hq : q.val + 1 = k
        · have e1 : (x.length + 1 + q.val) / k = x.length / k + 1 := by
            have : x.length + 1 + q.val = x.length + k := by omega
            rw [this, Nat.add_div_right _ hk1]
          have e2 : (q.val + 1) % k = 0 := by rw [hq]; exact Nat.mod_self k
          simp [hq, e1, e2, List.length_cons, List.replicate_succ]
        · have e2 : (q.val + 1) % k = q.val + 1 := Nat.mod_eq_of_lt (by omega)
          have e3 : x.length + 1 + q.val = x.length + (q.val + 1) := by omega
          simp [hq, e2, e3, List.length_cons])
      ⟨0, hk1⟩
    simpa using h
