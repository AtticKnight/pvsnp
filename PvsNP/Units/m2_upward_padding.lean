import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_unary_pad_np

namespace PvsNP.Units.m2_upward_padding_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner
open PvsNP.Units.m2_unary_pad_np

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neU :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neU_true, Computability.encodeBool])

def pow2Cap (k : ℕ) (s : List Bool) : List Bool :=
  tpw [true, true] (List.replicate ((dropN s).length ^ k) true) (hd s)

theorem pow2Cap_length (k : ℕ) (s : List Bool) :
    (pow2Cap k s).length = min (2 ^ ((dropN s).length ^ k)) ((hd s).length + 1) := by
  have h := tpw_length [true, true] (List.replicate ((dropN s).length ^ k) true) (hd s) (by simp)
  simpa [pow2Cap] using h

theorem cpt_pow2Cap (k : ℕ) : CPT (pow2Cap k) := by
  have hpow : CPT (fun s : List Bool => List.replicate ((dropN s).length ^ k) true) := by
    have h1 := L055 (Polynomial.X ^ k)
    have h2 : CPT (fun s : List Bool => List.replicate ((Polynomial.X ^ k).eval (dropN s).length) true) :=
      cpt_comp (cpt_dropN1 cpt_id) h1
    exact cptU h2 (fun s => by simp)
  exact cpt_tpw (cpt_const [true, true]) hpow (cpt_hd1 cpt_id)

def padDec (k : ℕ) (c : Code) (d : ℕ) (s : List Bool) : Bool :=
  !(upPadA s).isEmpty &&
    (decide ((pow2Cap k s ++ un k).length ≤ (hd s).length) &&
      (decide ((hd s).length ≤ (pow2Cap k s ++ un k).length) &&
        V (pairB (encCode c) (pairB (dropN s) (List.replicate (d * (hd s).length + d) true)), [])))

private theorem comb4 (A : List Bool) (a b c : Bool) :
    (!(sel A [] (sel (if a then [true] else []) []
      (sel (if b then [true] else []) []
        (sel (if c then [true] else []) [] [true])))).isEmpty) =
      (!A.isEmpty && (a && (b && c))) := by
  cases A <;> cases a <;> cases b <;> cases c <;> simp [sel]

theorem cpt_padDec (k : ℕ) (c : Code) (d : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool (padDec k c d) := by
  have fA : CPT upPadA := cpt_upPadA
  have hLHS : CPT (fun s : List Bool => pow2Cap k s ++ un k) :=
    cpt_app2 (cpt_pow2Cap k) (cpt_const (un k))
  have hRHS : CPT (fun s : List Bool => hd s) := cpt_hd1 cpt_id
  have f1 := cpt_le hLHS hRHS
  have f2 := cpt_le hRHS hLHS
  have hclk : CPT (fun s : List Bool => List.replicate (d * (hd s).length + d) true) := by
    have h1 := L055 (Polynomial.C d * Polynomial.X + Polynomial.C d)
    have h2 : CPT (fun s : List Bool =>
        List.replicate ((Polynomial.C d * Polynomial.X + Polynomial.C d).eval (hd s).length) true) :=
      cpt_comp hRHS h1
    exact cptU h2 (fun s => by simp)
  have f3 := cpt_Vflag (cpt_pairB2 (cpt_const (encCode c)) (cpt_pairB2 (cpt_dropN1 cpt_id) hclk)) (cpt_const [])
  have all := cpt_sel fA (cpt_const []) (cpt_sel f1 (cpt_const [])
    (cpt_sel f2 (cpt_const []) (cpt_sel f3 (cpt_const []) (cpt_const [true]))))
  exact cptU (cpt_comp all cpt_neU) (fun s => comb4 _ _ _ _)

theorem upward_padding_in_P (L : Language Bool) (k : ℕ)
    (f : List Bool → Bool)
    (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f)
    (hf : ∀ x : List Bool, x ∈ L ↔ f x = true)
    (htime : ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
        s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈
      PvsNP.P := by
  obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
  refine (PvsNP.Units.fr_ladner.P_iff _).mpr ⟨padDec k c d, fun s => ?_, cpt_padDec k c d⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    set t := 2 ^ (x.length ^ k) + k
    have hhd : hd (List.replicate t true ++ false :: x) = un t := hd_un t x
    have hdrop : dropN (List.replicate t true ++ false :: x) = x := dropN_un t x
    have hpadA : upPadA (List.replicate t true ++ false :: x) = x ++ [false] := by
      have e : (List.replicate t true ++ false :: x) ++ [false] =
          un t ++ false :: (x ++ [false]) := by simp [un]
      rw [upPadA, e, dropN_un]
    have hpow : (pow2Cap k (List.replicate t true ++ false :: x)).length + k = t := by
      rw [pow2Cap_length, hhd, hdrop, un_length]
      have hmin : min (2 ^ (x.length ^ k)) (t + 1) = 2 ^ (x.length ^ k) :=
        min_eq_left (by omega)
      rw [hmin]
    have hfx : f x = true := (hf x).mp hx
    have hev : (flip bind (Turing.TM2.step M.tm.m))^[((M.outputsFun x).steps)]
        (some (Turing.initList M.tm (x.map M.inputAlphabet.invFun))) =
        some (Turing.haltList M.tm [M.outputAlphabet.invFun (f x)]) :=
      (M.outputsFun x).evals_in_steps
    have hsteps : (M.outputsFun x).steps ≤ t := by
      have h1 : (M.outputsFun x).steps ≤ M.time x.length :=
        (M.outputsFun x).steps_le_m
      exact h1.trans (htime x.length)
    have hcw := hc x (f x) (M.outputsFun x).steps hev
    have hle_steps : d * (M.outputsFun x).steps + d ≤ d * t + d := by
      have := Nat.mul_le_mul_left d hsteps
      omega
    have hcw' : c.outputsWithin (x.map (fun b => cond b 1 0)) (d * t + d) [bitCode (f x)] :=
      Code.outputsWithin_mono c _ hle_steps _ hcw
    rw [hfx] at hcw'
    have hcw'' : c.outputsWithin (x.map (fun b => cond b 1 0)) (d * t + d) [1] := by
      simpa [bitCode] using hcw'
    have hV : V (pairB (encCode c) (pairB x (un (d * t + d))), []) = true := by
      rw [V_spec]
      refine ⟨by simp, ?_⟩
      simpa using hcw''
    simp only [padDec, hpadA, hdrop, hhd, un_length, List.length_append, hpow, le_refl,
      decide_true, Bool.true_and]
    have hun : List.replicate (d * t + d) true = un (d * t + d) := rfl
    rw [hun, hV]
    simp
  · intro hs
    simp only [padDec, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hs
    obtain ⟨hA, hle1, hle2, hV⟩ := hs
    have hA' : upPadA s ≠ [] := by
      intro h
      rw [h] at hA
      simp at hA
    have hsplit := (up_hd_split s).resolve_left hA'
    have hlen : (pow2Cap k s).length + k = (hd s).length := by
      simp only [List.length_append, un_length] at hle1 hle2
      omega
    rw [pow2Cap_length] at hlen
    have hmin : min (2 ^ ((dropN s).length ^ k)) ((hd s).length + 1) = 2 ^ ((dropN s).length ^ k) := by
      rcases min_cases (2 ^ ((dropN s).length ^ k)) ((hd s).length + 1) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · omega
    rw [hmin] at hlen
    set t := (hd s).length
    set x := dropN s
    have hV' : V (pairB (encCode c) (pairB x (un (d * t + d))), []) = true := hV
    rw [V_spec] at hV'
    have hcw1 : c.outputsWithin (x.map (fun b => cond b 1 0)) (d * t + d) [1] := by
      simpa using hV'.2
    have hev : (flip bind (Turing.TM2.step M.tm.m))^[((M.outputsFun x).steps)]
        (some (Turing.initList M.tm (x.map M.inputAlphabet.invFun))) =
        some (Turing.haltList M.tm [M.outputAlphabet.invFun (f x)]) :=
      (M.outputsFun x).evals_in_steps
    have hcw2 := hc x (f x) (M.outputsFun x).steps hev
    have hsteps : (M.outputsFun x).steps ≤ t := by
      have h1 : (M.outputsFun x).steps ≤ M.time x.length :=
        (M.outputsFun x).steps_le_m
      exact h1.trans ((htime x.length).trans (by omega))
    have hle_steps : d * (M.outputsFun x).steps + d ≤ d * t + d := by
      have := Nat.mul_le_mul_left d hsteps
      omega
    have hcw2' : c.outputsWithin (x.map (fun b => cond b 1 0)) (d * t + d) [bitCode (f x)] :=
      Code.outputsWithin_mono c _ hle_steps _ hcw2
    have heq : [1] = [bitCode (f x)] := hcw1.2.symm.trans hcw2'.2
    have hfx : f x = true := by
      cases hb : f x with
      | false =>
        rw [hb] at heq
        simp [bitCode] at heq
      | true => rfl
    refine ⟨x, (hf x).mpr hfx, ?_⟩
    have hu : hd s = List.replicate t true := up_hd_eq_un s
    rw [hlen, ← hu]
    exact hsplit

end PvsNP.Units.m2_upward_padding_aux

theorem PvsNP.Units.m2_upward_padding : ∀ (L : Language Bool) (k : ℕ),
  (∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
      s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈ PvsNP.P := by
  rintro L k ⟨f, M, hf, htime⟩
  exact PvsNP.Units.m2_upward_padding_aux.upward_padding_in_P L k f M hf htime
