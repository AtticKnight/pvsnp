import Mathlib
import PvsNP.Defs
import CookLevin

/-- Each sublist is paired with the list obtained by adjoining the distinguished entry;
exactly one member of each pair has even length, including when entries repeat. -/
theorem PvsNP.Units.m3_xor_encoding_size :
    ∀ (x : var) (vs : List var),
      ((x :: vs).sublists.filter (fun T => decide (T.length % 2 = 0))).length =
        2 ^ vs.length := by
  intro x vs
  have hpair (s : List var) :
      (([s, x :: s] : List (List var)).filter
        (fun T => decide (T.length % 2 = 0))).length = 1 := by
    by_cases h : s.length % 2 = 0
    · have hn : (s.length + 1) % 2 ≠ 0 := by omega
      simp [h, hn]
    · have he : (s.length + 1) % 2 = 0 := by omega
      simp [h, he]
  have hlen (ss : List (List var)) :
      ((ss.flatMap (fun s => [s, x :: s])).filter
        (fun T => decide (T.length % 2 = 0))).length = ss.length := by
    induction ss with
    | nil => rfl
    | cons s ss ih =>
        rw [List.flatMap_cons, List.filter_append, List.length_append, hpair, ih]
        simp [Nat.add_comm]
  rw [List.sublists_cons, List.bind_eq_flatMap, hlen, List.length_sublists]
