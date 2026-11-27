import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-! A finite language is accepted by the automaton whose states are the sets of suffixes of its
words; the automaton is run as a transducer that writes only its final answer, the three-stack
machine `trM` of the settled unit `fr_ladner`
(`PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime`), used as is. -/

namespace PvsNP.Units.m2_p_finite

theorem dfa_run (Q : Type) (δ : Q → Bool → Q) (F : Q → Bool) :
    ∀ (x : List Bool) (q : Q), PvsNP.encodeAnswer (F (x.foldl δ q)) =
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun
        (fun q b => (δ q b, (none : Option Bool))) (fun q => some (F q)) q x := by
  intro x
  induction x with
  | nil => intro q; rfl
  | cons b x ih => intro q; exact ih (δ q b)

theorem dfa_comp (Q : Type) [Fintype Q] (δ : Q → Bool → Q) (q₀ : Q) (F : Q → Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => F (x.foldl δ q₀)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime
    PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => F (x.foldl δ q₀))
    (fun q b => (δ q b, (none : Option Bool))) (fun q => some (F q)) q₀
    (fun a => dfa_run Q δ F a q₀)

/-- All suffixes of the words of `S`. -/
def U (S : Finset (List Bool)) : Finset (List Bool) := S.biUnion (fun w => w.tails.toFinset)

theorem tail_mem (S : Finset (List Bool)) (t : List Bool) (ht : t ∈ U S) : t.tail ∈ U S := by
  simp only [U, Finset.mem_biUnion, List.mem_toFinset, List.mem_tails] at ht ⊢
  obtain ⟨w, hw, hs⟩ := ht
  exact ⟨w, hw, (List.tail_suffix t).trans hs⟩

theorem self_mem (S : Finset (List Bool)) (w : List Bool) (hw : w ∈ S) : w ∈ U S := by
  simp only [U, Finset.mem_biUnion, List.mem_toFinset, List.mem_tails]
  exact ⟨w, hw, List.suffix_refl w⟩

/-- Automaton states: sets of suffixes of the words of `S`. -/
abbrev St (S : Finset (List Bool)) : Type := {T : Finset (List Bool) // T ∈ (U S).powerset}

def step (S : Finset (List Bool)) (T : St S) (b : Bool) : St S :=
  ⟨(T.1.filter (fun s => s.head? = some b)).image List.tail, by
    rw [Finset.mem_powerset]
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [Finset.mem_filter] at ht
    exact tail_mem S t (Finset.mem_powerset.1 T.2 ht.1)⟩

def start (S : Finset (List Bool)) : St S :=
  ⟨S, Finset.mem_powerset.2 (fun w hw => self_mem S w hw)⟩

theorem run_correct (S : Finset (List Bool)) :
    ∀ (x : List Bool) (T : St S), [] ∈ (x.foldl (step S) T).1 ↔ x ∈ T.1 := by
  intro x
  induction x with
  | nil => intro T; exact Iff.rfl
  | cons b x ih =>
    intro T
    rw [List.foldl_cons, ih]
    simp only [step, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨s, ⟨hs, hh⟩, hx⟩
      cases s with
      | nil => simp at hh
      | cons c s =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        simp only [List.tail_cons] at hx
        subst hh
        subst hx
        exact hs
    · intro h
      exact ⟨b :: x, ⟨h, rfl⟩, rfl⟩

end PvsNP.Units.m2_p_finite

theorem PvsNP.Units.m2_p_finite :
∀ S : Finset (List Bool), ({x : List Bool | x ∈ S} : Language Bool) ∈ PvsNP.P := by
  intro S
  exact ⟨fun x => decide ([] ∈ (x.foldl (PvsNP.Units.m2_p_finite.step S)
      (PvsNP.Units.m2_p_finite.start S)).1),
    PvsNP.Units.m2_p_finite.dfa_comp (PvsNP.Units.m2_p_finite.St S)
      (PvsNP.Units.m2_p_finite.step S) (PvsNP.Units.m2_p_finite.start S)
      (fun T => decide ([] ∈ T.1)),
    fun x => by
      rw [decide_eq_true_iff, PvsNP.Units.m2_p_finite.run_correct]
      exact Iff.rfl⟩
