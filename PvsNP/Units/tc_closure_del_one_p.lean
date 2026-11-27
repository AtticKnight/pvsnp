import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_p_union

namespace PvsNP.Units.tc_closure_del_one_p

/-- The identity, as a one-state transducer. -/
def idF : Unit → List Bool → List Bool := fun _ x => x

theorem cpt_id : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x) :=
  PvsNP.Units.m2_transducer_polytime Unit (fun _ b => ((), some b)) (fun _ => none) idF
    (fun _ => rfl) (fun _ _ _ => rfl) ()

/-- `c ↦ 1 ^ |c| 0`, as a one-state transducer: a `true` for every bit, a `false` at the end. -/
def markF : Unit → List Bool → List Bool := fun _ x => List.replicate x.length true ++ [false]

theorem cpt_mark : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate x.length true ++ [false]) :=
  PvsNP.Units.m2_transducer_polytime Unit (fun _ _ => ((), some true)) (fun _ => some false) markF
    (fun _ => rfl) (fun _ _ _ => rfl) ()

/-- `x ↦ b :: x`, as a transducer writing each bit one step late. -/
def shδ (b : Bool) : Option Bool → Bool → Option Bool × Option Bool
  | none, c => (some c, some b)
  | some a, c => (some c, some a)

def shFin (b : Bool) : Option Bool → Option Bool
  | none => some b
  | some a => some a

def shF (b : Bool) : Option Bool → List Bool → List Bool
  | none, x => b :: x
  | some a, x => a :: x

theorem cpt_cons (b : Bool) : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => b :: x) :=
  PvsNP.Units.m2_transducer_polytime (Option Bool) (shδ b) (shFin b) (shF b)
    (fun q => by cases q <;> rfl) (fun q _ _ => by cases q <;> rfl) none

theorem takeWhile_mark (n : ℕ) (x : List Bool) :
    (List.replicate n true ++ [false] ++ x).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, List.takeWhile_cons_of_pos rfl]
    exact congrArg (List.cons true) ih

theorem dropWhile_mark (n : ℕ) (x : List Bool) :
    (List.replicate n true ++ [false] ++ x).dropWhile id = false :: x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, List.dropWhile_cons_of_pos rfl]
    exact ih

/-- The insertion of `b` into `x` at the position `|c|`, from the pair `(x, c)`. -/
def ins (b : Bool) (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.length ++ b :: p.1.drop p.2.length

/-- The insertion is polynomial-time: swap the pair, mark `c` as `1 ^ |c| 0` in front of `x`,
read the result back as the split of `x` at `|c|` (settled `m2_tm_self_delimiting_pair`), put `b` in
front of the second part and join the two parts. -/
theorem cpt_ins (b : Bool) : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (ins b) := by
  have h1 := PvsNP.Units.m2_tm_pair_swap_polytime
  have h2 := PvsNP.Units.m2_prod_map_polytime _ _ cpt_mark cpt_id
  have h3 := PvsNP.Units.m2_pair_split_polytime.2.2
  have h4 := PvsNP.Units.m2_tm_self_delimiting_pair.2
  have h5 := PvsNP.Units.m2_prod_map_polytime _ _ cpt_id (cpt_cons b)
  have h6 := PvsNP.Units.m2_pair_split_polytime.2.2
  have c12 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ h1 h2
  have c13 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ c12 h3
  have c14 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ c13 h4
  have c15 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ c14 h5
  have c16 := PvsNP.Units.m2_polytime_comp _ _ _ _ _ c15 h6
  convert c16 using 1
  funext p
  obtain ⟨x, c⟩ := p
  simp only [Function.comp]
  rw [takeWhile_mark, dropWhile_mark, List.length_replicate, List.tail_cons]
  rfl

/-- Deleting one `b` gives `x`, for `L` decided by `f`, exactly when the bounded search over the
insertion positions `i ≤ |x|` finds one whose insertion `f` accepts. -/
theorem del_iff (L : Language Bool) (f : List Bool → Bool) (hf : ∀ x, x ∈ L ↔ f x = true)
    (b : Bool) (x : List Bool) :
    (∃ u v : List Bool, x = u ++ v ∧ u ++ b :: v ∈ L) ↔
      (List.range (x.length + 1)).any (fun i => (f ∘ ins b) (x, List.replicate i true)) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, v, rfl, h⟩
    refine ⟨u.length, List.mem_range.2 (by simp), ?_⟩
    show f ((u ++ v).take (List.replicate u.length true).length ++
      b :: (u ++ v).drop (List.replicate u.length true).length) = true
    rw [List.length_replicate, List.take_left' rfl, List.drop_left' rfl]
    exact (hf _).1 h
  · rintro ⟨i, -, h⟩
    refine ⟨x.take i, x.drop i, (List.take_append_drop _ _).symm, (hf _).2 ?_⟩
    have := h
    simp only [Function.comp, ins, List.length_replicate] at this
    exact this

end PvsNP.Units.tc_closure_del_one_p

/-- P is closed under deleting one bit (TM2): deleting `b` gives `x` exactly when inserting `b`
into `x` at some position `i ≤ |x|` gives a string of `L`; the insertion is polynomial-time, so the
bounded search over `i` (settled `m2_bounded_unary_search_polytime`) decides it, and the two bits
are joined by the settled `m2_p_union`. -/
theorem PvsNP.Units.tc_closure_del_one_p :
    ∀ L : Language Bool, L ∈ PvsNP.P → ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  obtain ⟨f, hfp, hf⟩ := hL
  have hb : ∀ b : Bool,
      ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ b :: v ∈ L} : Language Bool) ∈ PvsNP.P := by
    intro b
    have hV := PvsNP.Units.m2_polytime_comp _ _ _ _ _ (PvsNP.Units.tc_closure_del_one_p.cpt_ins b) hfp
    exact ⟨_, PvsNP.Units.m2_bounded_unary_search_polytime _ hV,
      fun x => PvsNP.Units.tc_closure_del_one_p.del_iff L f hf b x⟩
  have hU := PvsNP.Units.m2_p_union _ _ (hb false) (hb true)
  have e : ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L} : Language Bool) =
      ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ false :: v ∈ L} : Language Bool) ⊔
        ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ true :: v ∈ L} : Language Bool) := by
    ext x
    show (∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L) ↔
      (∃ u v : List Bool, x = u ++ v ∧ u ++ false :: v ∈ L) ∨
        (∃ u v : List Bool, x = u ++ v ∧ u ++ true :: v ∈ L)
    constructor
    · rintro ⟨u, v, b, h1, h2⟩
      cases b
      · exact Or.inl ⟨u, v, h1, h2⟩
      · exact Or.inr ⟨u, v, h1, h2⟩
    · rintro (⟨u, v, h1, h2⟩ | ⟨u, v, h1, h2⟩)
      · exact ⟨u, v, false, h1, h2⟩
      · exact ⟨u, v, true, h1, h2⟩
  exact (congrArg (fun S : Language Bool => S ∈ PvsNP.P) e).mpr hU
