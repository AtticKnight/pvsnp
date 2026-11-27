import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_p_subset_np_conp
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_np_conp_one_inclusion

set_option autoImplicit false

namespace PvsNP.Units.m2_np_eq_conp_iff_conp_projection

def encPair (p : List Bool × List Bool) : List Bool :=
  List.replicate p.1.length true ++ false :: (p.1 ++ p.2)

def decPair (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem takeWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, List.takeWhile_cons, id_eq, ↓reduceIte, ih]

theorem dropWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, List.dropWhile_cons, id_eq, ↓reduceIte, ih]

theorem decPair_encPair (u v : List Bool) : decPair (encPair (u, v)) = (u, v) := by
  simp only [decPair, encPair, takeWhile_rep_false, dropWhile_rep_false, List.tail_cons,
    List.length_replicate, List.take_left, List.drop_left]

end PvsNP.Units.m2_np_eq_conp_iff_conp_projection

/-- `NP = coNP` iff `coNP` is closed under bounded existential projection (TM2): forward by
`m2_np_projection`, backward by encoding `(x, c)` with `m2_tm_self_delimiting_pair` so any NP
verifier language becomes a P (hence coNP) language projected existentially, giving `NP ⊆ coNP`
and hence `NP = coNP` via `m2_np_conp_one_inclusion`. -/
theorem PvsNP.Units.m2_np_eq_conp_iff_conp_projection :
    PvsNP.NP = PvsNP.coNP ↔ ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.coNP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) ∈ PvsNP.coNP := by
  constructor
  · intro h E g p hE hg
    rw [← h] at hE ⊢
    exact PvsNP.Units.m2_np_projection E g p hE hg
  · intro hProj
    refine PvsNP.Units.m2_np_conp_one_inclusion.1.1 fun L hL => ?_
    obtain ⟨V, p, hV, hiff⟩ := hL
    let E : Language Bool := {s : List Bool | (V ∘ PvsNP.Units.m2_np_eq_conp_iff_conp_projection.decPair) s = true}
    have hEP : E ∈ PvsNP.P :=
      ⟨V ∘ PvsNP.Units.m2_np_eq_conp_iff_conp_projection.decPair,
        PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
          PvsNP.Units.m2_np_eq_conp_iff_conp_projection.decPair V
          PvsNP.Units.m2_tm_self_delimiting_pair.2 hV,
        fun _ => Iff.rfl⟩
    have hEcoNP : E ∈ PvsNP.coNP := (PvsNP.Units.m2_p_subset_np_conp hEP).2
    have hres := hProj E PvsNP.Units.m2_np_eq_conp_iff_conp_projection.encPair p hEcoNP
      PvsNP.Units.m2_tm_self_delimiting_pair.1
    have heq : ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧
        PvsNP.Units.m2_np_eq_conp_iff_conp_projection.encPair (x, c) ∈ E} : Language Bool) = L := by
      ext x
      change (∃ c : List Bool, c.length ≤ p.eval x.length ∧
        V (PvsNP.Units.m2_np_eq_conp_iff_conp_projection.decPair
          (PvsNP.Units.m2_np_eq_conp_iff_conp_projection.encPair (x, c))) = true) ↔ x ∈ L
      simp only [PvsNP.Units.m2_np_eq_conp_iff_conp_projection.decPair_encPair]
      exact (hiff x).symm
    rwa [heq] at hres
