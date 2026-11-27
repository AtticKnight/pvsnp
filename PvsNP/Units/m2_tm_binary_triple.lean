import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_polytime_comp

import PvsNP.Units.m2_reverse_polytime

import PvsNP.Units.m2_transducer_polytime


namespace PvsNP.Units.m2_tm_binary_triple


/-- One pass of the tripling transducer: on bit `b` with carry `c` write
`(3b + c) % 2` (as `Nat.bodd`) and carry on with `(3b + c) / 2`. -/
def run : ℕ → List Bool → List Bool
  | _, [] => []
  | c, b :: x => Nat.bodd (3 * b.toNat + c) :: run ((3 * b.toNat + c) / 2) x

/-- The final carry of the tripling transducer. -/
def carry : ℕ → List Bool → ℕ
  | c, [] => c
  | c, b :: x => carry ((3 * b.toNat + c) / 2) x

theorem run_nil (c : ℕ) : run c [] = [] := by simp only [run]
theorem run_cons (c : ℕ) (b : Bool) (x : List Bool) :
    run c (b :: x) = Nat.bodd (3 * b.toNat + c) :: run ((3 * b.toNat + c) / 2) x := by
  simp only [run]
theorem carry_nil (c : ℕ) : carry c [] = c := by simp only [carry]
theorem carry_cons (c : ℕ) (b : Bool) (x : List Bool) :
    carry c (b :: x) = carry ((3 * b.toNat + c) / 2) x := by
  simp only [carry]

/-- The value of the transducer's output, with the final carry accounted at
the top: `value(out) + 2^|l| * carry = 3 * value(l) + c`. -/
theorem run_value : ∀ (l : List Bool) (c : ℕ),
    Nat.ofDigits 2 ((run c l).map Bool.toNat) + 2 ^ l.length * carry c l
      = 3 * Nat.ofDigits 2 (l.map Bool.toNat) + c := by
  intro l
  induction l with
  | nil =>
      intro c
      simp [run_nil, carry_nil]
  | cons b x ih =>
      intro c
      have hd : (Nat.bodd (3 * b.toNat + c)).toNat + 2 * ((3 * b.toNat + c) / 2)
          = 3 * b.toNat + c := by
        have h := Nat.mod_add_div (3 * b.toNat + c) 2
        rw [Nat.mod_two_of_bodd] at h
        omega
      have ih' := ih ((3 * b.toNat + c) / 2)
      simp only [run_cons, carry_cons, List.map_cons, Nat.ofDigits_cons,
        List.length_cons, pow_succ]
      calc (Nat.bodd (3 * b.toNat + c)).toNat
            + 2 * Nat.ofDigits 2 ((run ((3 * b.toNat + c) / 2) x).map Bool.toNat)
            + 2 ^ x.length * 2 * carry ((3 * b.toNat + c) / 2) x
          = (Nat.bodd (3 * b.toNat + c)).toNat
            + 2 * (Nat.ofDigits 2 ((run ((3 * b.toNat + c) / 2) x).map Bool.toNat)
              + 2 ^ x.length * carry ((3 * b.toNat + c) / 2) x) := by ring
        _ = (Nat.bodd (3 * b.toNat + c)).toNat
            + 2 * (3 * Nat.ofDigits 2 (x.map Bool.toNat) + (3 * b.toNat + c) / 2) := by
            rw [ih']
        _ = 3 * (b.toNat + 2 * Nat.ofDigits 2 (x.map Bool.toNat)) + c := by omega

/-- A carry that starts at most 2 stays at most 2. -/
theorem carry_le : ∀ (l : List Bool) (c : ℕ), c ≤ 2 → carry c l ≤ 2 := by
  intro l
  induction l with
  | nil => intro c hc; rwa [carry_nil]
  | cons b x ih =>
      intro c hc
      rw [carry_cons]
      apply ih
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      omega

theorem carry_append : ∀ (l l' : List Bool) (c : ℕ),
    carry c (l ++ l') = carry (carry c l) l' := by
  intro l
  induction l with
  | nil => intro l' c; simp [carry_nil]
  | cons b x ih => intro l' c; simp only [List.cons_append, carry_cons, ih]

theorem run_append : ∀ (l l' : List Bool) (c : ℕ),
    run c (l ++ l') = run c l ++ run (carry c l) l' := by
  intro l
  induction l with
  | nil => intro l' c; simp [run_nil, carry_nil]
  | cons b x ih =>
      intro l' c
      simp only [List.cons_append, run_cons, carry_cons, ih]

/-- Two appended falses flush any carry ≤ 2 to 0. -/
theorem carry_two_falses (c : ℕ) (hc : c ≤ 2) : carry c [false, false] = 0 := by
  have e1 : carry c [false, false]
      = carry ((3 * (false : Bool).toNat + c) / 2) [false] := carry_cons c false [false]
  have e2 : carry ((3 * (false : Bool).toNat + c) / 2) [false]
      = carry ((3 * (false : Bool).toNat + (3 * (false : Bool).toNat + c) / 2) / 2) [] :=
    carry_cons _ false []
  rw [e1, e2, carry_nil]
  have hf : (false : Bool).toNat = 0 := rfl
  rw [hf]
  omega

theorem carry_zero_append (x : List Bool) : carry 0 (x ++ [false, false]) = 0 := by
  rw [carry_append]
  exact carry_two_falses _ (carry_le x 0 (by omega))

/-- After appending two falses, the transducer's output has value exactly
three times the input's value. -/
theorem run_triple_value (x : List Bool) :
    Nat.ofDigits 2 ((run 0 (x ++ [false, false])).map Bool.toNat)
      = 3 * Nat.ofDigits 2 (x.map Bool.toNat) := by
  have h := run_value (x ++ [false, false]) 0
  rw [carry_zero_append, List.length_append] at h
  have hmap : (x ++ [false, false]).map Bool.toNat = x.map Bool.toNat ++ [0, 0] := by
    simp [List.map_append]
  have h00 : Nat.ofDigits 2 [0, 0] = 0 := by decide
  rw [hmap, Nat.ofDigits_append, h00] at h
  omega

theorem ofDigits_eq_zero {l : List Bool} (h : Nat.ofDigits 2 (l.map Bool.toNat) = 0) :
    ∀ b ∈ l, b = false := by
  induction l with
  | nil => intro b hb; simp at hb
  | cons a x ih =>
      rw [List.map_cons, Nat.ofDigits_cons] at h
      have ha : a.toNat = 0 := by omega
      have hx : Nat.ofDigits 2 (x.map Bool.toNat) = 0 := by omega
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb'
      · rw [hba]
        cases a with
        | false => rfl
        | true => exact absurd ha (by decide)
      · exact ih hx b hb'

theorem ofDigits_eq_zero_of_all_false {l : List Bool} (h : ∀ b ∈ l, b = false) :
    Nat.ofDigits 2 (l.map Bool.toNat) = 0 := by
  induction l with
  | nil => rfl
  | cons a x ih =>
      rw [List.map_cons, Nat.ofDigits_cons, h a List.mem_cons_self,
        ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))]
      decide

/-- Uniqueness of the canonical binary form: a bit list with value `v` that
is empty or ends in `true` is `Nat.bits v`. (Strong induction on `v`,
packaged as induction on a bound.) -/
theorem bits_unique_aux : ∀ (N v : ℕ) (l : List Bool), v < N →
    Nat.ofDigits 2 (l.map Bool.toNat) = v →
    (l = [] ∨ ∃ l', l = l' ++ [true]) → l = Nat.bits v := by
  intro N
  induction N with
  | zero => intro v l hlt; exact absurd hlt (Nat.not_lt_zero v)
  | succ N ih =>
      intro v l hlt hv hl
      cases l with
      | nil =>
          have hv0 : v = 0 := by
            have h0 : Nat.ofDigits 2 (List.map Bool.toNat ([] : List Bool)) = 0 :=
              Nat.ofDigits_nil
            omega
          rw [hv0, Nat.zero_bits]
      | cons b x =>
          rw [List.map_cons, Nat.ofDigits_cons] at hv
          have hx : x = [] ∨ ∃ l', x = l' ++ [true] := by
            rcases hl with h | ⟨l', hl'⟩
            · simp at h
            · cases l' with
              | nil =>
                  left
                  have h2 : b :: x = [true] := hl'
                  simp only [List.cons.injEq] at h2
                  exact h2.2
              | cons a l'' =>
                  right
                  refine ⟨l'', ?_⟩
                  simp only [List.cons_append, List.cons.injEq] at hl'
                  exact hl'.2
          cases b with
          | true =>
              have ht : (true : Bool).toNat = 1 := rfl
              rw [ht] at hv
              have ihx := ih (Nat.ofDigits 2 (x.map Bool.toNat)) x (by omega) rfl hx
              have hv2 : v = 2 * Nat.ofDigits 2 (x.map Bool.toNat) + 1 := by omega
              rw [hv2, Nat.bit1_bits, ← ihx]
          | false =>
              have hf : (false : Bool).toNat = 0 := rfl
              rw [hf] at hv
              by_cases hw : Nat.ofDigits 2 (x.map Bool.toNat) = 0
              · exfalso
                rcases hl with h | ⟨l', hl'⟩
                · simp at h
                · cases l' with
                  | nil =>
                      have h2 : (false : Bool) :: x = [true] := hl'
                      simp only [List.cons.injEq] at h2
                      exact Bool.noConfusion h2.1
                  | cons a l'' =>
                      have hxx : x = l'' ++ [true] := by
                        have h2 : (false : Bool) :: x = a :: (l'' ++ [true]) := hl'
                        simp only [List.cons.injEq] at h2
                        exact h2.2
                      have hmem : true ∈ x := by rw [hxx]; simp
                      have htf : (true : Bool) = false := ofDigits_eq_zero hw true hmem
                      exact Bool.noConfusion htf
              · have ihx := ih (Nat.ofDigits 2 (x.map Bool.toNat)) x (by omega) rfl hx
                have hv2 : v = 2 * Nat.ofDigits 2 (x.map Bool.toNat) := by omega
                rw [hv2, Nat.bit0_bits _ hw, ← ihx]

theorem bits_unique (v : ℕ) (l : List Bool)
    (hv : Nat.ofDigits 2 (l.map Bool.toNat) = v)
    (hl : l = [] ∨ ∃ l', l = l' ++ [true]) : l = Nat.bits v :=
  bits_unique_aux (v + 1) v l (by omega) hv hl

/-- Dropping the leading falses of the reversed list (the high zeros) does
not change the value. -/
theorem strip_value (y : List Bool) :
    Nat.ofDigits 2 ((y.reverse.dropWhile (fun b => !b)).reverse.map Bool.toNat)
      = Nat.ofDigits 2 (y.map Bool.toNat) := by
  have hdecomp := List.takeWhile_append_dropWhile (p := fun b => !b) (l := y.reverse)
  have hmap : y.map Bool.toNat
      = ((y.reverse.dropWhile (fun b => !b)).reverse.map Bool.toNat)
        ++ ((y.reverse.takeWhile (fun b => !b)).reverse.map Bool.toNat) := by
    conv_lhs => rw [← List.reverse_reverse y, ← hdecomp, List.reverse_append,
      List.map_append]
  rw [hmap, Nat.ofDigits_append]
  have hw0 : Nat.ofDigits 2 ((y.reverse.takeWhile (fun b => !b)).reverse.map Bool.toNat) = 0 := by
    apply ofDigits_eq_zero_of_all_false
    intro b hb
    rw [List.mem_reverse] at hb
    have hp := List.mem_takeWhile_imp hb
    cases b <;> simp at hp ⊢
  rw [hw0, mul_zero, add_zero]

/-- The stripped list is empty or ends in `true`. -/
theorem strip_last (y : List Bool) :
    (y.reverse.dropWhile (fun b => !b)).reverse = []
      ∨ ∃ l', (y.reverse.dropWhile (fun b => !b)).reverse = l' ++ [true] := by
  by_cases hz : y.reverse.dropWhile (fun b => !b) = []
  · left; rw [hz]; rfl
  · right
    obtain ⟨c, t, hct⟩ : ∃ c t, y.reverse.dropWhile (fun b => !b) = c :: t := by
      cases h : y.reverse.dropWhile (fun b => !b) with
      | nil => exact absurd h hz
      | cons c t => exact ⟨c, t, rfl⟩
    have hc : c = true := by
      have hmem : ∀ (z : List Bool) (c : Bool) (t : List Bool),
          z.dropWhile (fun b => !b) = c :: t → c = true := by
        intro z
        induction z with
        | nil =>
            intro c t h
            simp [List.dropWhile] at h
        | cons a x ih =>
            intro c t h
            by_cases ha : a = false
            · subst ha
              rw [List.dropWhile_cons] at h
              split at h
              · exact ih c t h
              · rename_i hcond
                simp at hcond
            · have ha' : a = true := by cases a <;> simp_all
              subst ha'
              rw [List.dropWhile_cons] at h
              split at h
              · rename_i hcond
                simp at hcond
              · simp only [List.cons.injEq] at h
                exact h.1.symm
      exact hmem _ c t hct
    exact ⟨t.reverse, by rw [hct, List.reverse_cons, hc]⟩

theorem strip_eq_bits (y : List Bool) :
    (y.reverse.dropWhile (fun b => !b)).reverse
      = Nat.bits (Nat.ofDigits 2 (y.map Bool.toNat)) :=
  bits_unique _ _ (strip_value y) (strip_last y)

/-- The whole pipeline on paper: append two falses, triple with carry,
strip the high zeros — the result is the canonical bits of three times
the input's value. -/
theorem triple_eq (x : List Bool) :
    ((run 0 (x ++ [false, false])).reverse.dropWhile (fun b => !b)).reverse
      = Nat.bits (3 * Nat.ofDigits 2 (x.map Bool.toNat)) := by
  rw [strip_eq_bits, run_triple_value]

/-- Drop the leading falses of a list (the high zeros, once the list is
reversed). -/
def dropF (l : List Bool) : List Bool := l.dropWhile (fun b => !b)

/-- The tripling transducer's transition on `Fin 3` carries: on bit `b`
with carry `c`, write `(3b + c) % 2` and carry `(3b + c) / 2`. -/
def tripleδ (c : Fin 3) (b : Bool) : Fin 3 × Option Bool :=
  (⟨(3 * b.toNat + c.val) / 2, by
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    have hc : c.val < 3 := c.isLt
    omega⟩, some (Nat.bodd (3 * b.toNat + c.val)))

/-- Appending one `false` is polynomial-time (a copy transducer whose
final output is one extra bit). -/
theorem app1_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun l : List Bool => l ++ [false]) := by
  refine PvsNP.Units.m2_transducer_polytime (Q := Unit)
    (δ := fun _ b => ((), some b)) (fin := fun _ => some false)
    (F := fun _ l => l ++ [false]) ?_ ?_ ()
  · intro q; rfl
  · intro q b x; rfl

/-- Appending two `false`s is polynomial-time. -/
theorem app2_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun l : List Bool => l ++ [false, false]) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun l : List Bool => l ++ [false])
    (fun l : List Bool => l ++ [false]) app1_poly app1_poly
  have hfun : (fun l : List Bool => l ++ [false]) ∘ (fun l : List Bool => l ++ [false])
      = (fun l : List Bool => l ++ [false, false]) := by
    funext l
    simp [Function.comp_apply, List.append_assoc]
  rwa [hfun] at h

/-- The tripling transducer pass is polynomial-time. -/
theorem run_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (run 0) := by
  have h := PvsNP.Units.m2_transducer_polytime (Fin 3) tripleδ (fun _ => none)
    (fun c l => run c.val l) (by intro q; rfl) (by
      intro q b x
      have e1 : (tripleδ q b).2 = some (Nat.bodd (3 * b.toNat + q.val)) := rfl
      have e2 : (tripleδ q b).1.val = (3 * b.toNat + q.val) / 2 := rfl
      simp only [run_cons, e1, e2, Option.toList_some, List.singleton_append]) 0
  exact h

/-- Dropping leading falses is polynomial-time (a two-state transducer:
drop falses until the first `true`, then copy). -/
theorem dropF_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    dropF := by
  refine PvsNP.Units.m2_transducer_polytime (Q := Bool)
    (δ := fun q b => if q then (true, some b)
      else if b then (true, some true) else (false, none))
    (fin := fun _ => none)
    (F := fun q l => if q then l else dropF l) ?_ ?_ false
  · intro q; cases q <;> rfl
  · intro q b x; cases q <;> cases b <;> simp [dropF]

/-- Stripping the high zeros (reverse, drop leading falses, reverse) is
polynomial-time. -/
theorem norm_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun l : List Bool => (dropF l.reverse).reverse) := by
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun l : List Bool => l.reverse) dropF
    PvsNP.Units.m2_reverse_polytime dropF_poly
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (dropF ∘ fun l : List Bool => l.reverse)
    (fun l : List Bool => l.reverse) h1 PvsNP.Units.m2_reverse_polytime
  have hfun : (fun l : List Bool => l.reverse) ∘ (dropF ∘ fun l : List Bool => l.reverse)
      = (fun l : List Bool => (dropF l.reverse).reverse) := by
    funext l; rfl
  rwa [hfun] at h2

/-- The whole pipeline is polynomial-time, and by `triple_eq` it computes
the canonical bits of three times the input's value. -/
theorem pipeline_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => Nat.bits (3 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))) := by
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun l : List Bool => l ++ [false, false]) (run 0)
    app2_poly run_poly
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (run 0 ∘ fun l : List Bool => l ++ [false, false])
    (fun l : List Bool => (dropF l.reverse).reverse) h1 norm_poly
  have hfun : (fun l : List Bool => (dropF l.reverse).reverse)
        ∘ (run 0 ∘ fun l : List Bool => l ++ [false, false])
      = (fun x : List Bool => Nat.bits (3 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))) := by
    funext x
    show (dropF (run 0 (x ++ [false, false])).reverse).reverse
      = Nat.bits (3 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))
    show ((run 0 (x ++ [false, false])).reverse.dropWhile (fun b => !b)).reverse
      = Nat.bits (3 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))
    exact triple_eq x
  rwa [hfun] at h2


end PvsNP.Units.m2_tm_binary_triple


theorem PvsNP.Units.m2_tm_binary_triple :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (3 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))) :=
  PvsNP.Units.m2_tm_binary_triple.pipeline_poly
