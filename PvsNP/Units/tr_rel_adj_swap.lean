import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_tm_pair_zip_polytime

-- Built from the settled campaign units m2_tm_pair_zip_polytime, m2_p_finite (DFA), m2_len_le_polytime.

namespace PvsNP.Units.tr_rel_adj_swap

def Swap (xs ys : List Bool) : Prop :=
  ∃ (u v : List Bool) (a b : Bool), xs = u ++ a :: b :: v ∧ ys = u ++ b :: a :: v

theorem swap_len {xs ys : List Bool} (h : Swap xs ys) : xs.length = ys.length := by
  unfold Swap at h
  obtain ⟨u, v, a, b, h1, h2⟩ := h
  subst h1 h2
  simp

theorem not_swap_nil (ys : List Bool) : ¬ Swap [] ys := by
  unfold Swap
  rintro ⟨u, v, a, b, h, -⟩
  have := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

theorem not_swap_single (c : Bool) (ys : List Bool) : ¬ Swap [c] ys := by
  unfold Swap
  rintro ⟨u, v, a, b, h, -⟩
  have := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

theorem swap_cons (x y : Bool) (xs ys : List Bool) :
    Swap (x :: xs) (y :: ys) ↔ (x = y ∧ Swap xs ys) ∨ (∃ v, xs = y :: v ∧ ys = x :: v) := by
  unfold Swap
  constructor
  · rintro ⟨u, v, a, b, h1, h2⟩
    cases u with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inr ⟨v, rfl, rfl⟩
    | cons c u =>
      simp only [List.cons_append, List.cons.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨rfl, u, v, a, b, rfl, rfl⟩
  · rintro (⟨rfl, u, v, a, b, rfl, rfl⟩ | ⟨v, rfl, rfl⟩)
    · exact ⟨_ :: u, v, a, b, rfl, rfl⟩
    · exact ⟨[], v, _, _, rfl, rfl⟩

inductive PS where
  | init : PS
  | eq : Bool → Bool → PS
  | wait : Bool → PS
  | done : PS
  | rej : PS
  deriving DecidableEq

instance : Fintype PS :=
  Fintype.ofList [PS.init, PS.eq false false, PS.eq false true, PS.eq true false, PS.eq true true,
    PS.wait false, PS.wait true, PS.done, PS.rej]
    (by
      intro x
      cases x with
      | eq c f => cases c <;> cases f <;> simp
      | wait a => cases a <;> simp
      | _ => simp)

def stepP : PS → Bool → Bool → PS
  | PS.init, x, y => if x = y then PS.eq x false else PS.wait x
  | PS.eq c f, x, y => if x = y then PS.eq x (f || c == x) else PS.wait x
  | PS.wait a, x, y => if x = !a ∧ y = a then PS.done else PS.rej
  | PS.done, x, y => if x = y then PS.done else PS.rej
  | PS.rej, _, _ => PS.rej

def accP : PS → Bool
  | PS.init => false
  | PS.eq _ f => f
  | PS.wait _ => false
  | PS.done => true
  | PS.rej => false

def Lang : PS → List Bool → List Bool → Prop
  | PS.init, xs, ys => Swap xs ys
  | PS.eq c f, xs, ys => Swap (c :: xs) (c :: ys) ∨ (f = true ∧ xs = ys)
  | PS.wait a, xs, ys => ∃ v, xs = (!a) :: v ∧ ys = a :: v
  | PS.done, xs, ys => xs = ys
  | PS.rej, _, _ => False

def stepB : PS × Option Bool → Bool → PS × Option Bool
  | (q, none), x => (q, some x)
  | (q, some x), y => (stepP q x y, none)

def finB : PS × Option Bool → Bool
  | (q, none) => accP q
  | (_, some _) => false

theorem acc_lang (q : PS) : accP q = true ↔ Lang q [] [] := by
  cases q <;> simp [accP, Lang, not_swap_nil, not_swap_single]

theorem step_lang (q : PS) (x y : Bool) (xs ys : List Bool) :
    Lang q (x :: xs) (y :: ys) ↔ Lang (stepP q x y) xs ys := by
  cases q with
  | init => cases x <;> cases y <;> simp [Lang, stepP, swap_cons] <;> aesop
  | eq c f => cases c <;> cases f <;> cases x <;> cases y <;> simp [Lang, stepP, swap_cons] <;> aesop
  | wait a => cases a <;> cases x <;> cases y <;> simp [Lang, stepP] <;> aesop
  | done => cases x <;> cases y <;> simp [Lang, stepP] <;> aesop
  | rej => simp [Lang, stepP]

theorem zf_cons (x y : Bool) (xs ys : List Bool) :
    (List.zipWith (fun a b : Bool => [a, b]) (x :: xs) (y :: ys)).flatten =
      x :: y :: (List.zipWith (fun a b : Bool => [a, b]) xs ys).flatten := by
  simp

theorem run_main : ∀ (xs ys : List Bool) (q : PS), xs.length = ys.length →
    (finB ((List.zipWith (fun a b : Bool => [a, b]) xs ys).flatten.foldl stepB (q, none)) = true ↔
      Lang q xs ys) := by
  intro xs
  induction xs with
  | nil =>
    intro ys q h
    cases ys with
    | nil =>
      show accP q = true ↔ Lang q [] []
      exact acc_lang q
    | cons y ys => simp at h
  | cons x xs ih =>
    intro ys q h
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rw [zf_cons, List.foldl_cons, List.foldl_cons]
      have h' : xs.length = ys.length := by simpa using h
      exact (ih ys (stepP q x y) h').trans (step_lang q x y xs ys).symm

end PvsNP.Units.tr_rel_adj_swap

/-- Whether one string is another with two adjacent bits swapped is decidable in polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_adj_swap :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧ ∀ p : List Bool × List Bool, (∃ (u v : List Bool) (a b : Bool), p.1 = u ++ a :: b :: v ∧ p.2 = u ++ b :: a :: v) ↔ f p = true := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) :=
    PvsNP.Units.m2_len_le_polytime
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_tm_pair_swap_polytime.swap
      PvsNP.Units.m2_len_le_polytime
  have h3 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        PvsNP.Units.tr_rel_adj_swap.finB
          ((List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten.foldl
            PvsNP.Units.tr_rel_adj_swap.stepB (PvsNP.Units.tr_rel_adj_swap.PS.init, none))) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (f := fun p : List Bool × List Bool => (List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten)
      (g := fun x : List Bool =>
        PvsNP.Units.tr_rel_adj_swap.finB (x.foldl PvsNP.Units.tr_rel_adj_swap.stepB (PvsNP.Units.tr_rel_adj_swap.PS.init, none)))
      PvsNP.Units.m2_tm_pair_zip_polytime
      (PvsNP.Units.m2_p_finite.dfa_comp (PvsNP.Units.tr_rel_adj_swap.PS × Option Bool)
        PvsNP.Units.tr_rel_adj_swap.stepB (PvsNP.Units.tr_rel_adj_swap.PS.init, none) PvsNP.Units.tr_rel_adj_swap.finB)
  have heqLen := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ h1 h2
  have hall := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ heqLen h3
  refine ⟨_, hall, fun p => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    have hl := PvsNP.Units.tr_rel_adj_swap.swap_len h
    exact ⟨⟨by omega, by omega⟩, (PvsNP.Units.tr_rel_adj_swap.run_main p.1 p.2 PvsNP.Units.tr_rel_adj_swap.PS.init hl).2 h⟩
  · rintro ⟨⟨hl1, hl2⟩, h3⟩
    exact (PvsNP.Units.tr_rel_adj_swap.run_main p.1 p.2 PvsNP.Units.tr_rel_adj_swap.PS.init (by omega)).1 h3
