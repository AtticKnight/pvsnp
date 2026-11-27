import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_time_hierarchy_gen_aux

open PvsNP.Units.fr_ladner
open Turing PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

def thQ (s : List Bool) : List Bool :=
  pairB (unpairB (unpairB s).2).1
    (pairB (unpairB s).2 (mulU (unpairB s).2 (unpairB s).1))

def thPost (s : List Bool) : Bool := !V (thQ s, [])

def thPostPair (p : List Bool × List Bool) : Bool := thPost (pairB p.1 p.2)

lemma cpt_thPostPair :
    ComputableInPolyTime PEqualNP.Library.encodePair Computability.encodeBool thPostPair := by
  have hz1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB (unpairB s).2).1) :=
    cpt_comp (g := fun s : List Bool => (unpairB s).1) cpt_unpairB2 cpt_unpairB1
  have hmul : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => mulU (unpairB s).2 (unpairB s).1) :=
    cpt_mulU2 cpt_unpairB2 cpt_unpairB1
  have hq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) thQ :=
    cpt_pairB2 hz1 (cpt_pairB2 cpt_unpairB2 hmul)
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V (thQ s, [])) :=
    cpt_comp (cpt_pair hq (cpt_const [])) (cpt_V cpt_sstep)
  have hnot : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime Computability.encodeBool Computability.encodeBool (fun b => !b)
      (fun b => some (!b)) (fun b => by cases b <;> rfl)
  have hpost : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool thPost :=
    cpt_comp (g := fun b : Bool => !b) hV hnot
  exact cpt_comp (g := thPost) cpt_pairB hpost

lemma dup_bound : ∃ p : Polynomial ℕ,
    ComputableInTime (fun x : List Bool => x) PEqualNP.Library.encodePair
      (fun x : List Bool => (x, x)) (fun n => p.eval n) :=
  time_of_polyTime cpt_dup

lemma thPostPair_bound : ∃ p : Polynomial ℕ,
    ComputableInTime PEqualNP.Library.encodePair Computability.encodeBool
      thPostPair (fun n => p.eval n) :=
  time_of_polyTime cpt_thPostPair

noncomputable def kDup : ℕ :=
  Classical.choose (PEqualNP.Library.Helpers.polynomial_le_pow_add (Classical.choose dup_bound))

lemma kDup_spec : ∀ n : ℕ, (Classical.choose dup_bound).eval n ≤ n ^ kDup + kDup :=
  Classical.choose_spec (PEqualNP.Library.Helpers.polynomial_le_pow_add (Classical.choose dup_bound))

noncomputable def kPost : ℕ :=
  Classical.choose (PEqualNP.Library.Helpers.polynomial_le_pow_add (Classical.choose thPostPair_bound))

lemma kPost_spec : ∀ n : ℕ, (Classical.choose thPostPair_bound).eval n ≤ n ^ kPost + kPost :=
  Classical.choose_spec
    (PEqualNP.Library.Helpers.polynomial_le_pow_add (Classical.choose thPostPair_bound))

noncomputable def kUniv : ℕ := max kDup (max kPost 1)

lemma th_pair_time (t : ℕ → ℕ) (c_t : ℕ)
    (M_t : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (t x.length) true))
    (hMt : ∀ n : ℕ, M_t.time n ≤ c_t * t n + c_t) :
    ComputableInTime (fun x : List Bool => x) PEqualNP.Library.encodePair
      (fun x : List Bool => (List.replicate (t x.length) true, x))
      (fun n => (Classical.choose dup_bound).eval n + (2 * (2 * n) + 2) +
        (c_t * t n + c_t + 2 * n + 2 * n + 2 * t n + 5)) := by
  classical
  obtain ⟨c1, hc1⟩ := Classical.choose_spec dup_bound
  let e₀ : Bool → M_t.tm.Γ M_t.tm.k₀ := M_t.inputAlphabet.invFun
  let e₁ : M_t.tm.Γ M_t.tm.k₁ → Bool := M_t.outputAlphabet
  let c2 : FinTM2 := firstM M_t.tm e₀ e₁
  let φ : c1.tm.Γ c1.tm.k₁ → c2.Γ c2.k₀ :=
    fun x => (Equiv.refl (Bool ⊕ Bool)).invFun (c1.outputAlphabet x)
  let d : Option (c2.Γ c2.k₀) :=
    if h : Nonempty (c2.Γ c2.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.Γ c2.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.Γ c2.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : ℕ → ℕ := fun n =>
    (Classical.choose dup_bound).eval n + (2 * (2 * n) + 2) +
      (c_t * t n + c_t + 2 * n + 2 * n + 2 * t n + 5)
  let ft : List Bool → List Bool := fun x => List.replicate (t x.length) true
  have key : ∀ x : List Bool, ∃ n, n ≤ T x.length ∧
      (flip bind (TM2.step (prog c1.tm c2 φ d)))^[n]
          (some (initList (comp c1.tm c2 φ d) (List.map c1.inputAlphabet.invFun x))) =
        some (haltList (comp c1.tm c2 φ d)
          (List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PEqualNP.Library.encodePair (ft x, x)))) := by
    intro x
    have r1 := c1.outputsFun x
    have hs : (flip bind (TM2.step M_t.tm.m))^[(M_t.outputsFun x).steps]
        (some (initList M_t.tm (x.map e₀))) =
        some (haltList M_t.tm (List.map M_t.outputAlphabet.invFun (ft x))) :=
      (M_t.outputsFun x).evals_in_steps
    obtain ⟨n2, hn2, hrun2⟩ :=
      first_run (M := M_t.tm) e₀ e₁ x x (List.map M_t.outputAlphabet.invFun (ft x))
        (M_t.outputsFun x).steps hs
    have hm : (List.map M_t.outputAlphabet.invFun (ft x)).map e₁ = ft x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (ft x)]
      exact List.map_congr_left fun y _ => M_t.outputAlphabet.right_inv y
    rw [hm] at hrun2
    have hφ : (List.map c1.outputAlphabet.invFun (PEqualNP.Library.encodePair (x, x))).map φ =
        PEqualNP.Library.encodePair (x, x) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (PEqualNP.Library.encodePair (x, x))]
      exact List.map_congr_left fun y _ => c1.outputAlphabet.right_inv y
    have hrun2' : (flip bind (TM2.step c2.m))^[n2]
        (some (initList c2 ((List.map c1.outputAlphabet.invFun
          (PEqualNP.Library.encodePair (x, x))).map φ))) =
        some (haltList c2 (List.map (Equiv.refl (Bool ⊕ Bool)).invFun
          (PEqualNP.Library.encodePair (ft x, x)))) := by
      have hid : List.map (Equiv.refl (Bool ⊕ Bool)).invFun
          (PEqualNP.Library.encodePair (ft x, x)) = PEqualNP.Library.encodePair (ft x, x) := by
        simp
      exact (congrArg (fun l : List (c2.Γ c2.k₀) =>
        (flip bind (TM2.step c2.m))^[n2] (some (initList c2 l))) hφ).trans
        (hrun2.trans (congrArg (fun l : List (c2.Γ c2.k₁) =>
          some (haltList c2 l)) hid.symm))
    obtain ⟨n, hn, -, hrun⟩ :=
      comp_run (M1 := c1.tm) (M2 := c2) φ d hd _ _ _ r1.steps n2 r1.evals_in_steps hrun2'
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ (Classical.choose dup_bound).eval x.length :=
      r1.steps_le_m.trans (hc1 x.length)
    have b_s : (M_t.outputsFun x).steps ≤ c_t * t x.length + c_t :=
      (M_t.outputsFun x).steps_le_m.trans (hMt x.length)
    have b_len : (List.map M_t.outputAlphabet.invFun (ft x)).length = t x.length := by
      simp [ft]
    have b2 : n2 ≤ c_t * t x.length + c_t + 2 * x.length + 2 * x.length + 2 * t x.length + 5 := by
      rw [b_len] at hn2
      omega
    have b_enc : (PEqualNP.Library.encodePair (x, x)).length = 2 * x.length := by
      simp [PEqualNP.Library.encodePair]
      omega
    simp only [T, List.length_map, b_enc]
    omega
  exact ⟨{
    tm := comp c1.tm c2 φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun x =>
      ⟨⟨Classical.choose (key x), (Classical.choose_spec (key x)).2⟩,
        (Classical.choose_spec (key x)).1⟩ }, fun _ => le_rfl⟩

lemma pow_le_pow_add_one (a j k : ℕ) (hjk : j ≤ k) : a ^ j ≤ a ^ k + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · cases j <;> simp
  · exact (Nat.pow_le_pow_right ha hjk).trans (Nat.le_add_right _ _)

lemma lin_le_pow (a k : ℕ) (hk : 1 ≤ k) : a ≤ a ^ k := by
  calc a = a ^ 1 := (pow_one a).symm
    _ ≤ a ^ k := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · cases k <;> simp at hk ⊢
      · exact Nat.pow_le_pow_right ha hk

end PvsNP.Units.m2_time_hierarchy_gen_aux

theorem PvsNP.Units.m2_time_hierarchy_gen : ∃ k : ℕ, ∀ t : ℕ → ℕ, (∀ n : ℕ, n ≤ t n) →
  (∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (t x.length) true)), ∀ n : ℕ, M.time n ≤ c * t n + c) →
  ∃ L : Language Bool,
    (∃ c : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ c * t n ^ k + c) ∧
    ¬ ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ t n := by
  open PvsNP.Units.m2_time_hierarchy_gen_aux PvsNP.Units.fr_ladner PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
  refine ⟨kUniv, fun t ht ⟨c_t, M_t, hMt⟩ => ?_⟩
  let g : List Bool → Bool := fun z =>
    thPostPair (List.replicate (t z.length) true, z)
  let L : Language Bool := { z : List Bool | g z = true }
  refine ⟨L, ?_, ?_⟩
  · have h1 := th_pair_time t c_t M_t hMt
    have h2_pf := Classical.choose_spec thPostPair_bound
    have hcomp := comp_time (fun x : List Bool => x) PEqualNP.Library.encodePair
      Computability.encodeBool (fun x : List Bool => (List.replicate (t x.length) true, x))
      thPostPair _ (fun n => (Classical.choose thPostPair_bound).eval n) (fun n => 2 * t n)
      h1 h2_pf (fun _ _ hxy => eval_mono _ hxy) (fun x => by
        simp only [PEqualNP.Library.encodePair, List.length_append, List.length_map,
          List.length_replicate]
        have := ht x.length
        omega)
    obtain ⟨M_g, hMg⟩ := hcomp
    let k := kUniv
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have hkDup : kDup ≤ k := le_max_left _ _
    have hkPost : kPost ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    let C : ℕ := 1 + c_t + 14 + 2 ^ kPost + kDup + c_t + 2 ^ kPost + kPost
    refine ⟨C, g, M_g, fun _ => Iff.rfl, fun n => ?_⟩
    have b0 := hMg n
    dsimp only at b0
    have b1 := kDup_spec n
    have b2 := kPost_spec (2 * t n)
    have b3 : n ^ kDup ≤ (t n) ^ k + 1 :=
      (Nat.pow_le_pow_left (ht n) kDup).trans (pow_le_pow_add_one (t n) kDup k hkDup)
    have b4 : (2 * t n) ^ kPost ≤ 2 ^ kPost * ((t n) ^ k + 1) := by
      rw [Nat.mul_pow]
      exact Nat.mul_le_mul_left _ (pow_le_pow_add_one (t n) kPost k hkPost)
    have b5 : t n ≤ (t n) ^ k := lin_le_pow (t n) k hk1
    have b6 : n ≤ (t n) ^ k := (ht n).trans b5
    have b7 : c_t * t n ≤ c_t * (t n) ^ k := Nat.mul_le_mul_left c_t b5
    have b8 : 2 ^ kPost * ((t n) ^ k + 1) = 2 ^ kPost * (t n) ^ k + 2 ^ kPost := by ring
    change M_g.time n ≤ C * (t n) ^ k + C
    have b10 : (t n) ^ k + c_t * (t n) ^ k + 14 * (t n) ^ k + 2 ^ kPost * (t n) ^ k ≤
        C * (t n) ^ k := by
      have hC : 1 + c_t + 14 + 2 ^ kPost ≤ C := by
        dsimp only [C]
        linarith [Nat.zero_le kDup, Nat.zero_le c_t, Nat.zero_le (2 ^ kPost), Nat.zero_le kPost]
      have hm := Nat.mul_le_mul_right ((t n) ^ k) hC
      linarith
    have b11 : 1 + kDup + 2 + c_t + 5 + 2 + 2 ^ kPost + kPost ≤ C := by
      dsimp only [C]
      linarith [Nat.zero_le kDup, Nat.zero_le c_t, Nat.zero_le (2 ^ kPost), Nat.zero_le kPost]
    linarith [b0, b1, b2, b3, b4, b5, b6, b7, b8, b10, b11]
  · rintro ⟨f, M, hf, hM⟩
    obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
    have hrun : ∀ z : List Bool, ∃ n, n ≤ t z.length ∧
        c.outputsWithin (z.map (fun b => cond b 1 0)) (d * n + d) [bitCode (f z)] := by
      intro z
      obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ t z.length ∧
          (flip bind (Turing.TM2.step M.tm.m))^[n]
            (some (Turing.initList M.tm (z.map M.inputAlphabet.invFun))) =
          some (Turing.haltList M.tm [M.outputAlphabet.invFun (f z)]) :=
        ⟨(M.outputsFun z).steps, (M.outputsFun z).steps_le_m.trans (hM z.length),
          (M.outputsFun z).evals_in_steps⟩
      exact ⟨n, hn, hc z (f z) n hev⟩
    let m : ℕ := max (2 * (encCode c).length + 1) (2 * d + 1)
    let z : List Bool := pairB (encCode c) (un (m - (2 * (encCode c).length + 1)))
    have hzl : z.length = m := by
      simp only [z, pairB_length, un, List.length_replicate]
      omega
    have hm1 : 1 ≤ t m := le_trans (by omega) (ht m)
    obtain ⟨n, hn, ho⟩ := hrun z
    have hle : d * n + d ≤ m * t m := by
      rw [hzl] at hn
      have h1 : d * n ≤ d * t m := Nat.mul_le_mul_left d hn
      have h2 : d ≤ d * t m := Nat.le_mul_of_pos_right d hm1
      have h3 : d * t m + d * t m ≤ m * t m := by
        have h3' : 2 * d * t m ≤ m * t m := Nat.mul_le_mul_right (t m) (by omega)
        linarith
      omega
    have ho' := Code.outputsWithin_mono c _ hle _ ho
    have hq : thQ (pairB (List.replicate (t z.length) true) z) =
        pairB (encCode c) (pairB z (un (m * t m))) := by
      simp only [thQ, unpairB_pairB, mulU, List.length_replicate, hzl]
      simp only [z, unpairB_pairB]
    have hV : V (thQ (pairB (List.replicate (t z.length) true) z), []) = true ↔
        c.outputsWithin (z.map (fun b => cond b 1 0)) (m * t m) [1] := by
      rw [hq, V_spec]
      simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
    have hiff : V (thQ (pairB (List.replicate (t z.length) true) z), []) = true ↔ f z = true := by
      rw [hV]
      constructor
      · intro h1
        have heq : [1] = [bitCode (f z)] := h1.2.symm.trans ho'.2
        cases hb : f z with
        | true => rfl
        | false => rw [hb] at heq; simp [bitCode] at heq
      · intro hb
        rw [hb] at ho'
        exact ho'
    have hneg : z ∈ L ↔ V (thQ (pairB (List.replicate (t z.length) true) z), []) = false := by
      change g z = true ↔ _
      simp only [g, thPostPair, thPost, Bool.not_eq_true']
    have hcontra : V (thQ (pairB (List.replicate (t z.length) true) z), []) = true ↔
        V (thQ (pairB (List.replicate (t z.length) true) z), []) = false :=
      hiff.trans ((hf z).symm.trans hneg)
    cases hv : V (thQ (pairB (List.replicate (t z.length) true) z), []) with
    | true => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.1 rfl)
    | false => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.2 rfl)
