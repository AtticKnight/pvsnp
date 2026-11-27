import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_unary_div_const_time_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem clocked {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Bool)
    (f : Q → List Bool → List Bool) (nil : ∀ q, f q [] = [])
    (cons : ∀ q b x, f q (b :: x) = (δ q b).2.toList ++ f (δ q b).1 x) (initial : Q) :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (f initial),
      ∀ n, M.time n ≤ 2 * n + 3 := by
  let step := fun q b => ((δ q b).1, (δ q b).2, (none : Option Bool))
  let fin := fun _ : Q => (none : Option Bool)
  have run (q : Q) (x : List Bool) : fstRun2 step fin q x = f q x := by
    induction x generalizing q with
    | nil => exact (nil q).symm
    | cons b x ih => simp only [fstRun2, step, Option.toList_none, List.append_nil, cons, ih]
  refine ⟨{ tm := trM step fin initial (some false), inputAlphabet := Equiv.refl _,
            outputAlphabet := Equiv.refl _, time := fun n => 2 * n + 3,
            outputsFun := fun x => ?_ }, fun _ => le_rfl⟩
  refine { steps := x.length + 1 + 1 + (x.length + 1), evals_in_steps := ?_, steps_le_m := ?_ }
  · have identity (s : List Bool) : s.map (Equiv.refl Bool).invFun = s := by simp
    let M := trM step fin initial (some false)
    change (flip bind (Turing.TM2.step (trProg step fin initial (some false))))^[_]
      (some (Turing.initList M (x.map (Equiv.refl Bool).invFun))) =
      some (Turing.haltList M ((f initial x).map (Equiv.refl Bool).invFun))
    exact (congrArg (fun s : List (Bool) => (flip bind (Turing.TM2.step (trProg step fin initial (some false))))^[x.length + 1 + 1 + (x.length + 1)]
        (some (Turing.initList M s))) (identity (x))).trans
      ((trM_run step fin initial (some false) (by simp) x).trans (congrArg (fun s : List Bool => some (Turing.haltList M s))
        ((run initial x).trans ((identity (f initial x)).symm))))
  · change x.length + 1 + 1 + (x.length + 1) ≤ 2 * x.length + 3
    omega

end PvsNP.Units.m2_tm_unary_div_const_time_aux

open PvsNP.Units.m2_tm_unary_div_const_time_aux in
theorem PvsNP.Units.m2_tm_unary_div_const_time :
∀ k : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length / k) true), ∀ n : ℕ, M.time n ≤ 2 * n + 3 := by
  intro k
  cases k with
  | zero =>
    have constant := clocked (Q := Unit) (fun _ _ => ((), none)) (fun _ _ => [])
      (fun _ => rfl) (fun _ _ _ => rfl) ()
    have empty : (fun x : List Bool => List.replicate (x.length / 0) true) =
        (fun _ : List Bool => []) := by funext x; simp only [Nat.div_zero, List.replicate_zero]
    rw [empty]
    exact constant
  | succ d =>
    let modulus := d + 1
    have positive : 0 < modulus := Nat.succ_pos d
    let update := fun (q : Fin modulus) (_ : Bool) =>
      ((⟨(q.val + 1) % modulus, Nat.mod_lt _ positive⟩ : Fin modulus),
       if q.val + 1 = modulus then some true else none)
    let out := fun (q : Fin modulus) (x : List Bool) => List.replicate ((x.length + q.val) / modulus) true
    have machine := clocked update out
      (by intro q; simp [out, Nat.div_eq_of_lt q.isLt])
      (by
        intro q b x
        by_cases last : q.val + 1 = modulus
        · have advance : x.length + 1 + q.val = x.length + modulus := by omega
          simp [update, out, last, advance, Nat.add_div_right _ positive, List.replicate_succ]
        · have residue : (q.val + 1) % modulus = q.val + 1 := Nat.mod_eq_of_lt (by have := q.isLt; omega)
          have sum : x.length + 1 + q.val = x.length + (q.val + 1) := by omega
          simp [update, out, last, residue, sum])
      (⟨0, positive⟩ : Fin modulus)
    simpa [out, modulus] using machine
