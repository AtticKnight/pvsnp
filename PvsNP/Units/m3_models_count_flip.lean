import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_models_count_flip

def tog (n : ℕ) (v : var) (a : assgn) : assgn :=
  (List.range n).filter (fun x => if x = v then decide (v ∉ a) else decide (x ∈ a))

theorem mem_tog (n : ℕ) (v : var) (a : assgn) (x : ℕ) :
    x ∈ tog n v a ↔ x < n ∧ (if x = v then v ∉ a else x ∈ a) := by
  unfold tog
  by_cases h : x = v <;> simp [h]

theorem sub_eq {n : ℕ} {a b : List ℕ} (ha : a.Sublist (List.range n)) (hb : b.Sublist (List.range n))
    (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  have sa : a.Pairwise (· < ·) := List.pairwise_lt_range.sublist ha
  have sb : b.Pairwise (· < ·) := List.pairwise_lt_range.sublist hb
  have na : a.Nodup := List.nodup_range.sublist ha
  have nb : b.Nodup := List.nodup_range.sublist hb
  exact ((List.perm_ext_iff_of_nodup na nb).mpr h).eq_of_pairwise
    (fun x y _ _ h1 h2 => absurd h1 (Nat.lt_asymm h2)) sa sb

theorem tog_sub (n : ℕ) (v : var) (a : assgn) : (tog n v a).Sublist (List.range n) :=
  List.filter_sublist

theorem tog_tog {n : ℕ} {v : var} (hv : v < n) {a : assgn} (ha : a.Sublist (List.range n)) :
    tog n v (tog n v a) = a := by
  apply sub_eq (tog_sub _ _ _) ha
  intro x
  have hx : x ∈ a → x < n := fun h => List.mem_range.mp (ha.subset h)
  rw [mem_tog]
  by_cases h : x = v
  · subst h
    simp only [ite_true, mem_tog]
    constructor
    · rintro ⟨_, h2⟩
      by_contra hc
      exact h2 ⟨hv, hc⟩
    · intro h1
      exact ⟨hv, fun h2 => h2.2 h1⟩
  · simp only [h, ite_false, mem_tog]
    constructor
    · rintro ⟨_, _, h2⟩
      exact h2
    · intro h1
      exact ⟨hx h1, hx h1, h1⟩

theorem lit {n : ℕ} {v : var} (hv : v < n) {a : assgn} (ha : a.Sublist (List.range n)) (l : literal) :
    evalLiteral (tog n v a) l = evalLiteral a (if l.2 = v then (!l.1, l.2) else l) := by
  rcases l with ⟨s, x⟩
  have hx : x ∈ a → x < n := fun h => List.mem_range.mp (ha.subset h)
  by_cases h : x = v
  · subst h
    simp only [ite_true, evalLiteral, evalVar, mem_tog, hv, true_and]
    by_cases hm : x ∈ a <;> cases s <;> simp [hm]
  · simp only [h, ite_false, evalLiteral, evalVar, mem_tog]
    by_cases hm : x ∈ a
    · simp [hm, hx hm]
    · simp [hm]

theorem cl {n : ℕ} {v : var} (hv : v < n) {a : assgn} (ha : a.Sublist (List.range n)) : ∀ C : clause,
    evalClause a (C.map (fun l => if l.2 = v then (!l.1, l.2) else l)) = evalClause (tog n v a) C
  | [] => rfl
  | l :: C => by
    have ih := cl hv ha C
    simp only [evalClause] at ih
    simp only [evalClause, List.map_cons, List.any_cons, ih, lit hv ha]

theorem ev {n : ℕ} {v : var} (hv : v < n) {a : assgn} (ha : a.Sublist (List.range n)) : ∀ N : cnf,
    evalCnf a (N.map (fun C => C.map (fun l => if l.2 = v then (!l.1, l.2) else l))) =
      evalCnf (tog n v a) N
  | [] => rfl
  | C :: N => by
    have ih := ev hv ha N
    simp only [evalCnf] at ih
    simp only [evalCnf, List.map_cons, List.all_cons, ih, cl hv ha]

end PvsNP.Units.m3_models_count_flip

theorem PvsNP.Units.m3_models_count_flip : ∀ (n : ℕ) (N : cnf) (v : var), v < n →
  ((List.range n).sublists.filter
      (fun a => evalCnf a (N.map (fun C => C.map (fun l => if l.2 = v then (!l.1, l.2) else l))))).length =
    ((List.range n).sublists.filter (fun a => evalCnf a N)).length := by
  intro n N v hv
  have hmem : ∀ a, a ∈ (List.range n).sublists ↔ a.Sublist (List.range n) := fun a => List.mem_sublists
  have hperm : ((List.range n).sublists.map (PvsNP.Units.m3_models_count_flip.tog n v)).Perm
      (List.range n).sublists := by
    apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_sublists.mpr List.nodup_range)).mpr
    · intro b
      simp only [List.mem_map, hmem]
      constructor
      · rintro ⟨a, _, rfl⟩
        exact PvsNP.Units.m3_models_count_flip.tog_sub _ _ _
      · intro hb
        exact ⟨_, PvsNP.Units.m3_models_count_flip.tog_sub n v b,
          PvsNP.Units.m3_models_count_flip.tog_tog hv hb⟩
    · apply List.Nodup.map_on ?_ (List.nodup_sublists.mpr List.nodup_range)
      intro a ha b hb hab
      rw [← PvsNP.Units.m3_models_count_flip.tog_tog hv ((hmem a).mp ha),
        ← PvsNP.Units.m3_models_count_flip.tog_tog hv ((hmem b).mp hb), hab]
  have h1 : (List.range n).sublists.filter
      (fun a => evalCnf a (N.map (fun C => C.map (fun l => if l.2 = v then (!l.1, l.2) else l)))) =
      (List.range n).sublists.filter
        ((fun a => evalCnf a N) ∘ PvsNP.Units.m3_models_count_flip.tog n v) := by
    apply List.filter_congr
    intro a ha
    exact PvsNP.Units.m3_models_count_flip.ev hv ((hmem a).mp ha) N
  rw [h1, ← List.length_map (f := PvsNP.Units.m3_models_count_flip.tog n v), ← List.filter_map]
  exact (hperm.filter _).length_eq
