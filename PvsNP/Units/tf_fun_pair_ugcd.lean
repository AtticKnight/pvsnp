import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tf_fun_pair_ugcd

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem unpairB_len_le (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  unfold unpairB
  dsimp only
  cases hd0 : s.dropWhile id with
  | nil =>
    simp
  | cons b t =>
    rw [hd0] at hsplit
    have htake : (t.take (s.takeWhile id).length).length ≤ (s.takeWhile id).length :=
      List.length_take_le _ _
    have htd : (t.take (s.takeWhile id).length).length +
        (t.drop (s.takeWhile id).length).length = t.length := by
      rw [← List.length_append, List.take_append_drop]
    simp only [List.tail_cons, List.length_cons] at hsplit ⊢
    omega

private theorem iter_tail_len_le (k : ℕ) (l : List Bool) :
    (List.tail^[k] l).length ≤ l.length := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have ht : l.tail.length ≤ l.length := by simp
    exact (ih l.tail).trans ht

private theorem iter_tail_replicate (k m : ℕ) :
    List.tail^[k] (List.replicate m true) = List.replicate (m - k) true := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases m with
    | zero =>
      simpa using ih 0
    | succ m =>
      rw [List.replicate_succ, List.tail_cons, ih m]
      congr 1
      omega

def gcdStep (s : List Bool) : List Bool :=
  let u := (unpairB s).1
  let v := (unpairB s).2
  let fLe := if decide (u.length ≤ v.length) then [true] else []
  let subUV := pairB (List.tail^[v.length] u) v
  let subVU := pairB u (List.tail^[u.length] v)
  sel u (pairB u v) (sel v (pairB u v) (sel fLe subUV subVU))

private theorem gcdStep_len_le (s : List Bool) : (gcdStep s).length ≤ s.length + 1 := by
  have hs := unpairB_len_le s
  have h1 := iter_tail_len_le (unpairB s).2.length (unpairB s).1
  have h2 := iter_tail_len_le (unpairB s).1.length (unpairB s).2
  unfold gcdStep
  dsimp only
  cases hu : (unpairB s).1 with
  | nil =>
    rw [hu] at hs
    simp [sel, pairB_length]
    omega
  | cons bu us =>
    cases hv : (unpairB s).2 with
    | nil =>
      rw [hu, hv] at hs
      simp [sel, pairB_length]
      omega
    | cons bv vs =>
      rw [hu, hv] at hs h1 h2
      by_cases hle : (bu :: us).length ≤ (bv :: vs).length
      · simp only [sel, hle, decide_true, ↓reduceIte, List.cons_ne_nil, pairB_length]
        omega
      · simp only [sel, hle, decide_false, Bool.false_eq_true, ↓reduceIte, List.cons_ne_nil,
          pairB_length]
        omega

private theorem cpt_gcdStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gcdStep := by
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hV : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hFLe := cpt_bitFlag (cpt_comp (cpt_pair hV hU) LenCmp.lenLE_polyTime)
  have hSubUV := cpt_pairB2 (cpt_iterLen cpt_tail (fun l => by simp) hV hU) hV
  have hSubVU := cpt_pairB2 hU (cpt_iterLen cpt_tail (fun l => by simp) hU hV)
  have hPair := cpt_pairB2 hU hV
  exact cptp (cpt_sel hU hPair (cpt_sel hV hPair (cpt_sel hFLe hSubUV hSubVU))) (fun _ => rfl)

private theorem gcdStep_zero_left (b n : ℕ) :
    gcdStep^[n] (pairB [] (List.replicate b true)) = pairB [] (List.replicate b true) :=
  Function.iterate_fixed (by simp [gcdStep, unpairB_pairB, sel]) n

private theorem gcdStep_zero_right (a n : ℕ) :
    gcdStep^[n] (pairB (List.replicate a true) []) = pairB (List.replicate a true) [] :=
  Function.iterate_fixed (by cases a <;> simp [gcdStep, unpairB_pairB, sel]) n

private theorem gcdStep_iter : ∀ (n a b : ℕ), a + b ≤ n →
    ∃ a' b' : ℕ,
      gcdStep^[n] (pairB (List.replicate a true) (List.replicate b true)) =
        pairB (List.replicate a' true) (List.replicate b' true) ∧
      (a' = 0 ∨ b' = 0) ∧
      Nat.gcd a' b' = Nat.gcd a b
  | 0, a, b, hab => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    exact ⟨0, 0, rfl, Or.inl rfl, rfl⟩
  | n + 1, 0, b, _ =>
    ⟨0, b, gcdStep_zero_left b (n + 1), Or.inl rfl, rfl⟩
  | n + 1, a + 1, 0, _ =>
    ⟨a + 1, 0, gcdStep_zero_right (a + 1) (n + 1), Or.inr rfl, rfl⟩
  | n + 1, a + 1, b + 1, hab => by
    rw [Function.iterate_succ_apply]
    have ha_ne : List.replicate (a + 1) true ≠ [] := by simp
    have hb_ne : List.replicate (b + 1) true ≠ [] := by simp
    by_cases hle : a + 1 ≤ b + 1
    · have hstep : gcdStep (pairB (List.replicate (a + 1) true) (List.replicate (b + 1) true)) =
          pairB (List.replicate (a + 1) true) (List.replicate ((b + 1) - (a + 1)) true) := by
        simp only [gcdStep, unpairB_pairB, sel, ha_ne, hb_ne, ↓reduceIte, List.length_replicate,
          hle, decide_true, List.cons_ne_nil, iter_tail_replicate]
      rw [hstep]
      obtain ⟨a', b', h1, h2, h3⟩ := gcdStep_iter n (a + 1) ((b + 1) - (a + 1)) (by omega)
      exact ⟨a', b', h1, h2, h3.trans (Nat.gcd_sub_self_right hle)⟩
    · have hle' : b + 1 ≤ a + 1 := by omega
      have hstep : gcdStep (pairB (List.replicate (a + 1) true) (List.replicate (b + 1) true)) =
          pairB (List.replicate ((a + 1) - (b + 1)) true) (List.replicate (b + 1) true) := by
        simp only [gcdStep, unpairB_pairB, sel, ha_ne, hb_ne, ↓reduceIte, List.length_replicate,
          hle, decide_false, Bool.false_eq_true, iter_tail_replicate]
      rw [hstep]
      obtain ⟨a', b', h1, h2, h3⟩ := gcdStep_iter n ((a + 1) - (b + 1)) (b + 1) (by omega)
      exact ⟨a', b', h1, h2, h3.trans (Nat.gcd_sub_self_left hle')⟩

def toTrue (u : List Bool) : List Bool :=
  fstRun (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => none) () u

private theorem cpt_toTrue :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) toTrue :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => none) ()
    (fun _ => rfl)

private theorem toTrue_eq (u : List Bool) : toTrue u = List.replicate u.length true := by
  induction u with
  | nil => rfl
  | cons _ us ih =>
    change true :: toTrue us = List.replicate (us.length + 1) true
    rw [ih, List.replicate_succ]

def ugcdZ (z : List Bool) : List Bool :=
  let fin := gcdStep^[((unpairB z).1 ++ (unpairB z).2).length]
    (pairB (toTrue (unpairB z).1) (toTrue (unpairB z).2))
  (unpairB fin).1 ++ (unpairB fin).2

theorem cpt_ugcd :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (Nat.gcd p.1.length p.2.length) true) := by
  have henc : PvsNP.encodePair = encodePair := by
    funext ⟨_, _⟩
    rfl
  have hInit := cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_toTrue) (cpt_comp cpt_unpairB2 cpt_toTrue)
  have hCnt := cpt_app2 cpt_unpairB1 cpt_unpairB2
  have hFin := cpt_iterGrow cpt_gcdStep 1 gcdStep_len_le hCnt hInit
  have hZ : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) ugcdZ :=
    cptp (cpt_app2 (cpt_comp hFin cpt_unpairB1) (cpt_comp hFin cpt_unpairB2)) (fun _ => rfl)
  change ComputableInPolyTime PvsNP.encodePair (fun x : List Bool => x)
    (fun p : List Bool × List Bool => List.replicate (Nat.gcd p.1.length p.2.length) true)
  rw [henc]
  refine cptp (cpt_comp cpt_pairB hZ) (fun q => ?_)
  rcases q with ⟨a, b⟩
  unfold ugcdZ
  dsimp only
  simp only [unpairB_pairB, toTrue_eq, List.length_append]
  obtain ⟨a', b', hfin, hz, hgcd⟩ :=
    gcdStep_iter (a.length + b.length) a.length b.length (le_refl _)
  rw [hfin]
  simp only [unpairB_pairB]
  rcases hz with rfl | rfl
  · simp only [List.replicate_zero, List.nil_append, ← hgcd, Nat.gcd_zero_left]
  · simp only [List.replicate_zero, List.append_nil, ← hgcd, Nat.gcd_zero_right]

end PvsNP.Units.tf_fun_pair_ugcd

theorem PvsNP.Units.tf_fun_pair_ugcd :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (Nat.gcd p.1.length p.2.length) true) :=
  PvsNP.Units.tf_fun_pair_ugcd.cpt_ugcd
