import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_rotate_conp
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_conp_union
import PvsNP.Units.m2_conp_inter
import PvsNP.Units.m2_p_subset_np_conp
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_flatmap_all

/-
Original proof of `PvsNP.Units.tc_closure_del_one_conp`, from the settled units it imports.
Write each bit `b` of `x` as the block `[true, b]` (`enc`) and append the marker `[false, false]`:
`T x = enc x ++ [false, false]`. Rotating `T x` by `2 * u.length`, where `x = u ++ v`, gives
`enc v ++ [false, false] ++ enc u`; conversely every rotation of `T x` of that shape comes from a
split `x = u ++ v` (the even positions of `enc` hold `true`, so the only two consecutive `false`s
in the right places are the marker's). A finite automaton recognises the strings of that shape
(`m2_dfa_in_p`), and two transducers (`m2_transducer_polytime`) with `m2_pair_build_polytime`,
`m2_pair_split_polytime` and `m2_polytime_comp` turn `enc v ++ [false, false] ++ enc u` into
`u ++ b :: v` in polynomial time. So `x` is in the language exactly when some rotation of `T x`
lies in the coNP language `M` (`m2_conp_down_closed`, `m2_conp_inter`, `m2_conp_union`,
`m2_p_subset_np_conp`), and `tc_closure_rotate_conp` with `m2_conp_down_closed` closes the proof.
-/

namespace PvsNP.Units.tc_closure_del_one_conp

/-! ### The block encoding -/

/-- Each bit `b` becomes the block `[true, b]`. -/
def enc : List Bool → List Bool
  | [] => []
  | b :: y => true :: b :: enc y

theorem enc_eq_flatMap (y : List Bool) : enc y = y.flatMap (fun b => [true, b]) := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [enc, ih]

theorem enc_append (u v : List Bool) : enc (u ++ v) = enc u ++ enc v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [enc, ih]

theorem length_enc (y : List Bool) : (enc y).length = 2 * y.length := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [enc, ih]; omega

theorem enc_injective : ∀ y z : List Bool, enc y = enc z → y = z
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [enc] at h
  | _ :: _, [], h => by simp [enc] at h
  | b :: y, c :: z, h => by
    simp only [enc, List.cons.injEq, true_and] at h
    rw [h.1, enc_injective y z h.2]

theorem enc_even : ∀ (y : List Bool) (i : ℕ), i < y.length → (enc y)[2 * i]? = some true
  | [], i, h => by simp at h
  | b :: y, 0, _ => rfl
  | b :: y, i + 1, h => by
    have h' : i < y.length := by simp at h; omega
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    simp only [enc, List.getElem?_cons_succ]
    exact enc_even y i h'

/-- The string the reduction rotates. -/
def T (x : List Bool) : List Bool := enc x ++ [false, false]

/-- A rotation of `enc y ++ [false, false]` of that same shape is the string itself. -/
theorem rot_enc (y z : List Bool) (m : ℕ)
    (h : (enc y ++ [false, false]).rotate m = enc z ++ [false, false]) : y = z := by
  set s := enc y ++ [false, false] with hs
  have hN : s.length = 2 * y.length + 2 := by simp [hs, length_enc]
  have hz : z.length = y.length := by
    have := congrArg List.length h
    rw [List.length_rotate, hN, List.length_append, length_enc] at this
    simp at this
    omega
  rcases Nat.eq_zero_or_pos y.length with hn | hn
  · rw [List.length_eq_zero_iff.mp hn, List.length_eq_zero_iff.mp (hz.trans hn)]
  -- positions of `s` and of the right-hand side
  have sEven : ∀ i, i < y.length → s[2 * i]? = some true := by
    intro i hi
    rw [hs, List.getElem?_append_left (by rw [length_enc]; omega)]
    exact enc_even y i hi
  have sLast : s[2 * y.length + 1]? = some false := by
    rw [hs, List.getElem?_append_right (by rw [length_enc]; omega), length_enc]
    simp
  set t := enc z ++ [false, false] with ht
  have tFirst : t[0]? = some true := by
    rw [ht, List.getElem?_append_left (by rw [length_enc]; omega)]
    exact enc_even z 0 (by omega)
  have tLast1 : t[2 * y.length + 1]? = some false := by
    rw [ht, List.getElem?_append_right (by rw [length_enc]; omega), length_enc, hz]
    simp
  have tLast2 : t[2 * y.length]? = some false := by
    rw [ht, List.getElem?_append_right (by rw [length_enc]; omega), length_enc, hz]
    simp
  have hrot : ∀ k, k < s.length → t[k]? = s[(k + m) % s.length]? := by
    intro k hk
    rw [← h]
    exact List.getElem?_rotate hk
  set r := m % s.length with hr
  have hrlt : r < s.length := Nat.mod_lt _ (by omega)
  have e0 : s[r]? = some true := by
    have := hrot 0 (by omega); rw [Nat.zero_add] at this; rw [← this]; exact tFirst
  have e1 : s[(2 * y.length + 1 + m) % s.length]? = some false := by
    rw [← hrot _ (by omega)]; exact tLast1
  have e2 : s[(2 * y.length + m) % s.length]? = some false := by
    rw [← hrot _ (by omega)]; exact tLast2
  have hmod1 : (2 * y.length + 1 + m) % s.length = (2 * y.length + 1 + r) % s.length := by
    rw [hr, Nat.add_mod_mod]
  have hmod2 : (2 * y.length + m) % s.length = (2 * y.length + r) % s.length := by
    rw [hr, Nat.add_mod_mod]
  rw [hmod1] at e1
  rw [hmod2] at e2
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · interval_cases r
    · -- no rotation at all
      have h0 : s.rotate m = s := by rw [← List.rotate_mod, ← hr, List.rotate_zero]
      rw [h0, hs] at h
      exact enc_injective _ _ (List.append_cancel_right h)
    · -- index `0` would be a `false`
      rw [show 2 * y.length + 1 + 1 = s.length by omega, Nat.mod_self] at e1
      have := sEven 0 hn
      rw [Nat.mul_zero] at this
      rw [this] at e1
      exact absurd e1 (by simp)
  · rw [show 2 * y.length + 1 + r = (r - 1) + s.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at e1
    rw [show 2 * y.length + r = (r - 2) + s.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at e2
    rcases Nat.even_or_odd r with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- `r - 2` is even and below `2 * y.length`
      have := sEven (i - 1) (by omega)
      rw [show 2 * (i - 1) = r - 2 by omega, e2] at this
      exact absurd this (by simp)
    · -- `r - 1` is even
      by_cases hbig : r - 1 < 2 * y.length
      · have := sEven i (by omega)
        rw [show 2 * i = r - 1 by omega, e1] at this
        exact absurd this (by simp)
      · rw [show r = 2 * y.length + 1 by omega, sLast] at e0
        exact absurd e0 (by simp)

/-- A rotation of `T x` of the shape `enc v ++ [false, false] ++ enc u` splits `x` as `u ++ v`. -/
theorem rot_split (x u v : List Bool) (k : ℕ)
    (h : (T x).rotate k = enc v ++ [false, false] ++ enc u) : x = u ++ v := by
  have h2 : (T x).rotate (k + (enc v ++ [false, false]).length) =
      enc (u ++ v) ++ [false, false] := by
    rw [← List.rotate_rotate, h, List.rotate_append_length_eq, enc_append, List.append_assoc]
  exact rot_enc x (u ++ v) _ h2

/-! ### Recognising the shape `enc v ++ [false, false] ++ enc u` -/

/-- Automaton states. -/
inductive St | A0 | A1 | AM | B0 | B1 | D
  deriving DecidableEq

instance : Fintype St :=
  ⟨{.A0, .A1, .AM, .B0, .B1, .D}, fun q => by cases q <;> simp⟩

def δ : St → Bool → St
  | .A0, true => .A1
  | .A0, false => .AM
  | .A1, _ => .A0
  | .AM, false => .B0
  | .AM, true => .D
  | .B0, true => .B1
  | .B0, false => .D
  | .B1, _ => .B0
  | .D, _ => .D

theorem foldl_D : ∀ r : List Bool, r.foldl δ .D = .D := by
  intro r; induction r with
  | nil => rfl
  | cons b r ih => cases b <;> exact ih

theorem enc_ne_false_cons (u w : List Bool) : enc u ≠ false :: w := by
  cases u <;> simp [enc]

theorem accB : ∀ r : List Bool,
    (r.foldl δ .B0 = .B0 ↔ ∃ u, r = enc u) ∧ (r.foldl δ .B1 = .B0 ↔ ∃ b u, r = b :: enc u) := by
  intro r
  induction r with
  | nil =>
    refine ⟨⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · cases h
    · obtain ⟨_, _, h⟩ := h
      cases h
  | cons c r ih =>
    refine ⟨?_, ?_⟩
    · cases c
      · show r.foldl δ .D = .B0 ↔ _
        rw [foldl_D]
        constructor
        · intro h; cases h
        · rintro ⟨u, hu⟩; exact absurd hu.symm (enc_ne_false_cons u r)
      · show r.foldl δ .B1 = .B0 ↔ _
        rw [ih.2]
        constructor
        · rintro ⟨b, u, rfl⟩; exact ⟨b :: u, rfl⟩
        · rintro ⟨u, hu⟩
          rcases u with _ | ⟨b, u⟩
          · cases hu
          · simp only [enc, List.cons.injEq, true_and] at hu
            exact ⟨b, u, hu⟩
    · show r.foldl δ .B0 = .B0 ↔ _
      rw [ih.1]
      constructor
      · rintro ⟨u, rfl⟩; exact ⟨c, u, rfl⟩
      · rintro ⟨b, u, hu⟩
        simp only [List.cons.injEq] at hu
        exact ⟨u, hu.2⟩

theorem accA : ∀ r : List Bool,
    (r.foldl δ .A0 = .B0 ↔ ∃ v u, r = enc v ++ [false, false] ++ enc u) ∧
    (r.foldl δ .A1 = .B0 ↔ ∃ b v u, r = b :: (enc v ++ [false, false] ++ enc u)) ∧
    (r.foldl δ .AM = .B0 ↔ ∃ u, r = false :: enc u) := by
  intro r
  induction r with
  | nil =>
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · cases h
    · obtain ⟨v, u, h⟩ := h
      have := congrArg List.length h
      simp at this
    · cases h
    · obtain ⟨_, _, _, h⟩ := h
      cases h
    · cases h
    · obtain ⟨_, h⟩ := h
      cases h
  | cons c r ih =>
    refine ⟨?_, ?_, ?_⟩
    · cases c
      · show r.foldl δ .AM = .B0 ↔ _
        rw [ih.2.2]
        constructor
        · rintro ⟨u, rfl⟩; exact ⟨[], u, rfl⟩
        · rintro ⟨v, u, hvu⟩
          rcases v with _ | ⟨b, v⟩
          · simp only [enc, List.nil_append, List.cons_append, List.cons.injEq, true_and] at hvu
            exact ⟨u, hvu⟩
          · simp [enc] at hvu
      · show r.foldl δ .A1 = .B0 ↔ _
        rw [ih.2.1]
        constructor
        · rintro ⟨b, v, u, rfl⟩; exact ⟨b :: v, u, by simp [enc]⟩
        · rintro ⟨v, u, hvu⟩
          rcases v with _ | ⟨b, v⟩
          · simp [enc] at hvu
          · simp only [enc, List.cons_append, List.cons.injEq, true_and] at hvu
            exact ⟨b, v, u, by simpa using hvu⟩
    · show r.foldl δ .A0 = .B0 ↔ _
      rw [ih.1]
      constructor
      · rintro ⟨v, u, rfl⟩; exact ⟨c, v, u, rfl⟩
      · rintro ⟨b, v, u, h⟩
        simp only [List.cons.injEq] at h
        exact ⟨v, u, h.2⟩
    · cases c
      · show r.foldl δ .B0 = .B0 ↔ _
        rw [(accB r).1]
        constructor
        · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
        · rintro ⟨u, hu⟩; simp only [List.cons.injEq, true_and] at hu; exact ⟨u, hu⟩
      · show r.foldl δ .D = .B0 ↔ _
        rw [foldl_D]
        constructor
        · intro h; cases h
        · rintro ⟨u, hu⟩; simp at hu

/-- The strings of the shape `enc v ++ [false, false] ++ enc u`. -/
def WF : Language Bool := {r | ∃ v u, r = enc v ++ [false, false] ++ enc u}

theorem wf_in_p : WF ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_dfa_in_p St δ .A0 (fun q => decide (q = .B0))
  have e : WF = {r : List Bool | (fun q => decide (q = St.B0)) (r.foldl δ .A0) = true} := by
    ext r
    show (∃ v u, r = enc v ++ [false, false] ++ enc u) ↔ decide (r.foldl δ .A0 = .B0) = true
    rw [decide_eq_true_iff, (accA r).1]
  rw [e]
  exact h

/-! ### Transducers -/

/-- The output of a finite-state transducer. -/
def trun {Q : Type} (d : Q → Bool → Q × Option Bool) (fin : Q → Option Bool) :
    Q → List Bool → List Bool
  | q, [] => (fin q).toList
  | q, b :: x => (d q b).2.toList ++ trun d fin (d q b).1 x

theorem trun_polytime {Q : Type} [Fintype Q] (d : Q → Bool → Q × Option Bool)
    (fin : Q → Option Bool) (q₀ : Q) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (trun d fin q₀) :=
  PvsNP.Units.m2_transducer_polytime Q d fin (trun d fin) (fun _ => rfl) (fun _ _ _ => rfl) q₀

/-- Decode the blocks before the marker. States: `some false` between blocks, `some true` inside
a block, `none` after the marker. -/
def dPre : Option Bool → Bool → Option Bool × Option Bool
  | some false, true => (some true, none)
  | some false, false => (none, none)
  | some true, c => (some false, some c)
  | none, _ => (none, none)

theorem dPre_none : ∀ w : List Bool, trun dPre (fun _ => none) none w = [] := by
  intro w; induction w with
  | nil => rfl
  | cons c w ih => exact ih

theorem dPre_run : ∀ (v w : List Bool),
    trun dPre (fun _ => none) (some false) (enc v ++ false :: w) = v := by
  intro v w
  induction v with
  | nil => exact dPre_none w
  | cons b v ih =>
    show [] ++ ([b] ++ trun dPre (fun _ => none) (some false) (enc v ++ false :: w)) = b :: v
    rw [ih]; rfl

/-- Decode the blocks after the marker, then write `b`. States: `some (false, ·)` before the
marker (between blocks / inside a block), `none` inside the marker, `some (true, ·)` after it. -/
def dPost : Option (Bool × Bool) → Bool → Option (Bool × Bool) × Option Bool
  | some (false, false), true => (some (false, true), none)
  | some (false, false), false => (none, none)
  | some (false, true), _ => (some (false, false), none)
  | none, _ => (some (true, false), none)
  | some (true, false), _ => (some (true, true), none)
  | some (true, true), c => (some (true, false), some c)

theorem dPost_after (b : Bool) : ∀ u : List Bool,
    trun dPost (fun _ => some b) (some (true, false)) (enc u) = u ++ [b] := by
  intro u
  induction u with
  | nil => rfl
  | cons c u ih =>
    show [] ++ ([c] ++ trun dPost (fun _ => some b) (some (true, false)) (enc u)) = c :: u ++ [b]
    rw [ih]; rfl

theorem dPost_run (b : Bool) : ∀ (v u : List Bool),
    trun dPost (fun _ => some b) (some (false, false)) (enc v ++ [false, false] ++ enc u) =
      u ++ [b] := by
  intro v u
  induction v with
  | nil =>
    show [] ++ ([] ++ trun dPost (fun _ => some b) (some (true, false)) (enc u)) = u ++ [b]
    rw [dPost_after]; rfl
  | cons c v ih =>
    show [] ++ ([] ++ trun dPost (fun _ => some b) (some (false, false))
      (enc v ++ [false, false] ++ enc u)) = u ++ [b]
    rw [ih]; rfl

/-- The insertion the shape describes: `enc v ++ [false, false] ++ enc u ↦ u ++ b :: v`. -/
def W (b : Bool) (r : List Bool) : List Bool :=
  trun dPost (fun _ => some b) (some (false, false)) r ++ trun dPre (fun _ => none) (some false) r

theorem W_run (b : Bool) (v u : List Bool) :
    W b (enc v ++ [false, false] ++ enc u) = u ++ b :: v := by
  unfold W
  rw [dPost_run, show enc v ++ [false, false] ++ enc u = enc v ++ false :: (false :: enc u) by simp,
    dPre_run]
  simp

theorem W_polytime (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (W b) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun r => (trun dPost (fun _ => some b) (some (false, false)) r,
      trun dPre (fun _ => none) (some false) r))
    (fun p : List Bool × List Bool => p.1 ++ p.2)
    (PvsNP.Units.m2_pair_build_polytime _ _ (trun_polytime _ _ _) (trun_polytime _ _ _))
    PvsNP.Units.m2_pair_split_polytime.2.2

/-- Append one `false`. -/
def dApp : Unit → Bool → Unit × Option Bool := fun _ c => ((), some c)

theorem dApp_run : ∀ y : List Bool, trun dApp (fun _ => some false) () y = y ++ [false] := by
  intro y; induction y with
  | nil => rfl
  | cons c y ih =>
    show [c] ++ trun dApp (fun _ => some false) () y = c :: y ++ [false]
    rw [ih]; rfl

theorem T_polytime : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString T := by
  have h1 := PvsNP.Units.tf_fun_flatmap_all (fun b => [true, b])
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ h1 (trun_polytime dApp (fun _ => some false) ())
  have h3 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ h2 (trun_polytime dApp (fun _ => some false) ())
  have e : T = (trun dApp (fun _ => some false) ()) ∘ ((trun dApp (fun _ => some false) ()) ∘
      (fun x : List Bool => x.flatMap fun b => [true, b])) := by
    funext x
    simp only [Function.comp, dApp_run, T, enc_eq_flatMap, List.append_assoc]
    rfl
  rw [e]
  exact h3

/-- The coNP language the rotations of `T x` are tested against. -/
def M (L : Language Bool) : Language Bool :=
  (WF ⊓ {r | W false r ∈ L}) ⊔ (WF ⊓ {r | W true r ∈ L})

theorem M_conp (L : Language Bool) (hL : L ∈ PvsNP.coNP) : M L ∈ PvsNP.coNP := by
  have hWF : WF ∈ PvsNP.coNP := (PvsNP.Units.m2_p_subset_np_conp wf_in_p).2
  have hpre : ∀ b, ({r | W b r ∈ L} : Language Bool) ∈ PvsNP.coNP := fun b =>
    PvsNP.Units.m2_conp_down_closed _ L ⟨W b, W_polytime b, fun _ => Iff.rfl⟩ hL
  exact PvsNP.Units.m2_conp_union _ _ (PvsNP.Units.m2_conp_inter _ _ hWF (hpre false))
    (PvsNP.Units.m2_conp_inter _ _ hWF (hpre true))

theorem mem_iff (L : Language Bool) (x : List Bool) :
    (∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L) ↔
      ∃ k : ℕ, (T x).rotate k ∈ M L := by
  have hM : ∀ r, r ∈ M L ↔ ∃ b, r ∈ WF ∧ W b r ∈ L := by
    intro r
    show (r ∈ WF ∧ W false r ∈ L) ∨ (r ∈ WF ∧ W true r ∈ L) ↔ _
    constructor
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · rintro ⟨b, h⟩
      cases b
      · exact Or.inl h
      · exact Or.inr h
  constructor
  · rintro ⟨u, v, b, rfl, hins⟩
    refine ⟨(enc u).length, (hM _).mpr ⟨b, ?_, ?_⟩⟩
    · have : (T (u ++ v)).rotate (enc u).length = enc v ++ [false, false] ++ enc u := by
        rw [T, enc_append, List.append_assoc, List.rotate_append_length_eq, List.append_assoc]
      rw [this]
      exact ⟨v, u, rfl⟩
    · have : (T (u ++ v)).rotate (enc u).length = enc v ++ [false, false] ++ enc u := by
        rw [T, enc_append, List.append_assoc, List.rotate_append_length_eq, List.append_assoc]
      rw [this, W_run]
      exact hins
  · rintro ⟨k, hk⟩
    obtain ⟨b, ⟨v, u, hvu⟩, hW⟩ := (hM _).mp hk
    rw [hvu, W_run] at hW
    exact ⟨u, v, b, rot_split x u v k hvu, hW⟩

end PvsNP.Units.tc_closure_del_one_conp

theorem PvsNP.Units.tc_closure_del_one_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ v ∧ u ++ b :: v ∈ L} :
        Language Bool) ∈ PvsNP.coNP := by
  intro L hL
  have hN := PvsNP.Units.tc_closure_rotate_conp _ (PvsNP.Units.tc_closure_del_one_conp.M_conp L hL)
  exact PvsNP.Units.m2_conp_down_closed _ _
    ⟨PvsNP.Units.tc_closure_del_one_conp.T, PvsNP.Units.tc_closure_del_one_conp.T_polytime,
      fun x => PvsNP.Units.tc_closure_del_one_conp.mem_iff L x⟩ hN
