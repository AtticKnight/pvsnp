import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m1_st_np_to_flat_np_aux

open CookLevin

/-! ## Polynomial bounds -/

lemma poly_eval_le (p : Polynomial ℕ) :
    ∃ A K B : ℕ, ∀ n : ℕ, p.eval n ≤ A * n ^ K + B := by
  refine ⟨p.sum (fun _ c => c), p.natDegree, p.coeff 0, ?_⟩
  intro n
  cases n with
  | zero =>
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      exact Nat.le_add_left _ _
  | succ m =>
      have hpos : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
      calc
        ∑ i ∈ p.support, p.coeff i * (m + 1) ^ i
            ≤ ∑ i ∈ p.support, p.coeff i * (m + 1) ^ p.natDegree := by
              apply Finset.sum_le_sum
              intro i hi
              apply Nat.mul_le_mul_left
              exact Nat.pow_le_pow_right hpos (Polynomial.le_natDegree_of_mem_supp i hi)
        _ = (∑ i ∈ p.support, p.coeff i) * (m + 1) ^ p.natDegree := by
              rw [← Finset.sum_mul]
        _ ≤ (∑ i ∈ p.support, p.coeff i) * (m + 1) ^ p.natDegree + p.coeff 0 :=
              Nat.le_add_right _ _

lemma inOPoly_of_le_poly {f : ℕ → ℕ} {A K B : ℕ} (h : ∀ n, f n ≤ A * n ^ K + B) :
    inOPoly f := by
  refine ⟨K, A + B, 1, ?_⟩
  intro n hn
  have h1 : 1 ≤ n ^ K := Nat.one_le_pow K n hn
  calc
    f n ≤ A * n ^ K + B := h n
    _ ≤ A * n ^ K + B * n ^ K := by
          apply Nat.add_le_add_left
          simpa using Nat.mul_le_mul_left B h1
    _ = (A + B) * n ^ K := by rw [Nat.add_mul]

lemma inOPoly_le {f g : ℕ → ℕ} (hle : ∀ n, f n ≤ g n) (hg : inOPoly g) : inOPoly f := by
  rcases hg with ⟨k, c, n0, h⟩
  exact ⟨k, c, n0, fun n hn => le_trans (hle n) (h n hn)⟩

/-! ## General FlatTM helpers & ExactRun -/

def mk1 (src : ℕ) (rd : Option ℕ) (dst : ℕ) (wr : Option ℕ) (mv : TMMove) : FlatTMTransEntry :=
  { src_state := src
    src_tape_vals := [rd]
    dst_state := dst
    dst_write_vals := [wr]
    move_dirs := [mv] }

def shiftEntry (offset : ℕ) (e : FlatTMTransEntry) : FlatTMTransEntry :=
  { e with src_state := e.src_state + offset, dst_state := e.dst_state + offset }

def shiftCfg (offset : ℕ) (cfg : FlatTMConfig) : FlatTMConfig :=
  { cfg with state_idx := cfg.state_idx + offset }

lemma find_entry_unique (entries : List FlatTMTransEntry) (e : FlatTMTransEntry)
    (cfg : FlatTMConfig)
    (hmem : e ∈ entries)
    (hmatch : entryMatchesConfig e cfg = true)
    (huniq : ∀ e' ∈ entries, entryMatchesConfig e' cfg = true → e' = e) :
    entries.find? (fun x => entryMatchesConfig x cfg) = some e := by
  induction entries with
  | nil => cases hmem
  | cons hd tl ih =>
      simp only [List.find?]
      by_cases hhd : entryMatchesConfig hd cfg = true
      · simp only [hhd]
        exact congrArg some (huniq hd (List.mem_cons_self ..) hhd)
      · have hhd_f : entryMatchesConfig hd cfg = false := by
          cases hv : entryMatchesConfig hd cfg <;> simp_all
        simp only [hhd_f]
        have hmem_tl : e ∈ tl := by
          rcases List.mem_cons.mp hmem with rfl | htl
          · exact absurd hmatch hhd
          · exact htl
        exact ih hmem_tl (fun e' he' hm => huniq e' (List.mem_cons_of_mem hd he') hm)

lemma stepFlatTM_of_unique (M : FlatTM) (e : FlatTMTransEntry) (cfg : FlatTMConfig)
    (hmem : e ∈ M.trans)
    (hmatch : entryMatchesConfig e cfg = true)
    (huniq : ∀ e' ∈ M.trans, entryMatchesConfig e' cfg = true → e' = e) :
    stepFlatTM M cfg = applyTransitionEntry cfg e := by
  simp only [stepFlatTM, Option.bind_eq_bind]
  rw [find_entry_unique M.trans e cfg hmem hmatch huniq]
  rfl

lemma runFlatTM_step_one (M : FlatTM) (cfg cfg' : FlatTMConfig)
    (hnh : haltingStateReached M cfg = false)
    (hstep : stepFlatTM M cfg = some cfg') :
    runFlatTM 1 M cfg = some cfg' := by
  show (if haltingStateReached M cfg = true then some cfg
        else match stepFlatTM M cfg with
          | none => some cfg
          | some c => runFlatTM 0 M c) = some cfg'
  rw [hnh]
  simp [hstep, runFlatTM]

/-- An exact non-halting trajectory of `t` steps from `cfg` to `cfg_out`. -/
def ExactRun (N : FlatTM) (cfg cfg_out : FlatTMConfig) (t : ℕ) : Prop :=
  runFlatTM t N cfg = some cfg_out ∧
  ∀ k < t, ∀ ck, runFlatTM k N cfg = some ck → haltingStateReached N ck = false

lemma ExactRun.zero (N : FlatTM) (cfg : FlatTMConfig) : ExactRun N cfg cfg 0 :=
  ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

lemma ExactRun.step1 (N : FlatTM) (cfg cfg' : FlatTMConfig)
    (hnh : haltingStateReached N cfg = false)
    (hstep : stepFlatTM N cfg = some cfg') :
    ExactRun N cfg cfg' 1 := by
  refine ⟨runFlatTM_step_one N cfg cfg' hnh hstep, ?_⟩
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  have heq : cfg = ck := Option.some.inj hck
  subst heq; exact hnh

lemma ExactRun.trans {N : FlatTM} {c0 c1 c2 : FlatTMConfig} {t1 t2 : ℕ}
    (h1 : ExactRun N c0 c1 t1) (h2 : ExactRun N c1 c2 t2) :
    ExactRun N c0 c2 (t1 + t2) := by
  refine ⟨by rw [runFlatTM_compose N t1 t2 c0 c1 h1.1, h2.1], ?_⟩
  intro k hk ck hck
  by_cases hlt : k < t1
  · exact h1.2 k hlt ck hck
  · have hge : t1 ≤ k := Nat.le_of_not_lt hlt
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [runFlatTM_compose N t1 j c0 c1 h1.1] at hck
    exact h2.2 j (by omega) ck hck

lemma ExactRun.state_lt {N : FlatTM} {c0 c1 : FlatTMConfig} {t : ℕ}
    (hv : validFlatTM N) (h0 : c0.state_idx < N.states) (hrun : runFlatTM t N c0 = some c1) :
    c1.state_idx < N.states := by
  induction t generalizing c0 with
  | zero =>
      have : c0 = c1 := Option.some.inj hrun
      subst this; exact h0
  | succ n ih =>
      change (if haltingStateReached N c0 = true then some c0
              else match stepFlatTM N c0 with
                | none => some c0
                | some cm => runFlatTM n N cm) = some c1 at hrun
      by_cases hh : haltingStateReached N c0 = true
      · rw [if_pos hh] at hrun
        have : c0 = c1 := Option.some.inj hrun
        subst this; exact h0
      · rw [if_neg hh] at hrun
        cases hs : stepFlatTM N c0 with
        | none =>
            rw [hs] at hrun
            have : c0 = c1 := Option.some.inj hrun
            subst this; exact h0
        | some cm =>
            rw [hs] at hrun
            have hcm : cm.state_idx < N.states := by
              unfold stepFlatTM at hs
              simp only [Option.bind_eq_bind] at hs
              cases hf : N.trans.find? (fun e => entryMatchesConfig e c0) with
              | none => rw [hf] at hs; cases hs
              | some e =>
                  rw [hf] at hs
                  have hmem : e ∈ N.trans := List.mem_of_find?_eq_some hf
                  have hev := hv.2.2 e hmem
                  simp only [Option.bind_some, applyTransitionEntry] at hs
                  split_ifs at hs
                  have hcm_eq := Option.some.inj hs
                  rw [← hcm_eq]
                  exact hev.2.1
            exact ih hcm hrun

lemma ExactRun.step_of_lt {N : FlatTM} {c0 c1 : FlatTMConfig} {t : ℕ}
    (h : ExactRun N c0 c1 t) (k : ℕ) (hk : k < t) :
    ∃ ck, runFlatTM k N c0 = some ck ∧ haltingStateReached N ck = false := by
  have hex : ∀ m cfg, ∃ cm, runFlatTM m N cfg = some cm := by
    intro m
    induction m with
    | zero => intro cfg; exact ⟨cfg, rfl⟩
    | succ m ih =>
        intro cfg
        show ∃ cm, (if haltingStateReached N cfg = true then some cfg
              else match stepFlatTM N cfg with
                | none => some cfg
                | some cfg' => runFlatTM m N cfg') = some cm
        split_ifs
        · exact ⟨cfg, rfl⟩
        · cases stepFlatTM N cfg with
          | none => exact ⟨cfg, rfl⟩
          | some cfg' => exact ih cfg'
  obtain ⟨ck, hck⟩ := hex k c0
  exact ⟨ck, hck, h.2 k hk ck hck⟩

lemma list_find?_append_left {α : Type*} (p : α → Bool) (l₁ l₂ : List α)
    (h : ∀ x ∈ l₁, p x = false) :
    (l₁ ++ l₂).find? p = l₂.find? p := by
  induction l₁ with
  | nil => rfl
  | cons a tl ih =>
      simp only [List.cons_append, List.find?, h a (List.mem_cons_self ..)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

lemma list_find?_append_some {α : Type*} (p : α → Bool) (l₁ l₂ : List α) {a : α}
    (h : l₁.find? p = some a) :
    (l₁ ++ l₂).find? p = some a := by
  induction l₁ with
  | nil => simp [List.find?] at h
  | cons hd tl ih =>
      simp only [List.cons_append, List.find?] at h ⊢
      cases hp : p hd with
      | true => rw [hp] at h; exact h
      | false => rw [hp] at h; exact ih h

lemma list_find?_map_shift (off : ℕ) (entries : List FlatTMTransEntry) (cfg : FlatTMConfig) :
    (entries.map (shiftEntry off)).find? (fun e => entryMatchesConfig e (shiftCfg off cfg)) =
      (entries.find? (fun e => entryMatchesConfig e cfg)).map (shiftEntry off) := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.map_cons, List.find?]
      have hmatch : entryMatchesConfig (shiftEntry off hd) (shiftCfg off cfg) =
          entryMatchesConfig hd cfg := by
        unfold entryMatchesConfig shiftEntry shiftCfg
        have h1 : (hd.src_state + off == cfg.state_idx + off) = (hd.src_state == cfg.state_idx) := by
          apply Bool.eq_iff_iff.mpr; simp
        rw [h1]
      rw [hmatch]
      cases entryMatchesConfig hd cfg <;> simp [ih]

/-! ## Tape update helpers -/

lemma writeCurrentTapeSymbol_some_lt (head : ℕ) (right : List ℕ) (sym : ℕ) (h : head < right.length) :
    writeCurrentTapeSymbol ([], head, right) (some sym) =
      ([], head, right.take head ++ sym :: right.drop (head + 1)) := by
  simp [writeCurrentTapeSymbol, h]

lemma writeCurrentTapeSymbol_some_eq (right : List ℕ) (sym : ℕ) :
    writeCurrentTapeSymbol ([], right.length, right) (some sym) =
      ([], right.length, right ++ [sym]) := by
  simp [writeCurrentTapeSymbol]

lemma getElem?_update (right : List ℕ) (head sym : ℕ) (h : head < right.length) (i : ℕ) :
    (right.take head ++ sym :: right.drop (head + 1))[i]? =
      if i = head then some sym else right[i]? := by
  have htake : (right.take head).length = head := List.length_take_of_le (Nat.le_of_lt h)
  by_cases hi : i < head
  · have hne : i ≠ head := Nat.ne_of_lt hi
    rw [if_neg hne, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi]
  · by_cases heq : i = head
    · subst heq
      rw [if_pos rfl, List.getElem?_append_right (by omega)]
      simp [htake]
    · have hgt : head < i := by omega
      rw [if_neg heq, List.getElem?_append_right (by omega), htake]
      have hsub : i - head = (i - head - 1) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ, List.getElem?_drop]
      congr 1; omega

lemma length_update (right : List ℕ) (head sym : ℕ) (h : head < right.length) :
    (right.take head ++ sym :: right.drop (head + 1)).length = right.length := by
  simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

lemma currentTapeSymbol_at (pre : List ℕ) (sym : ℕ) (suf : List ℕ) :
    currentTapeSymbol ([], pre.length, pre ++ sym :: suf) = some sym := by
  unfold currentTapeSymbol
  have hlt : pre.length < (pre ++ sym :: suf).length := by simp
  rw [dif_pos hlt]; simp

lemma tapeStep_write_at (pre : List ℕ) (old sym : ℕ) (suf : List ℕ) (mv : TMMove) :
    tapeStep ([], pre.length, pre ++ old :: suf) (some sym) mv =
      moveTapeHead ([], pre.length, pre ++ sym :: suf) mv := by
  unfold tapeStep writeCurrentTapeSymbol
  dsimp only
  have hlt : pre.length < (pre ++ old :: suf).length := by simp
  rw [dif_pos hlt]
  congr 1
  simp [List.take_append_of_le_length, List.drop_append_of_le_length]

/-! ## Part 1: Folded two-track single-tape FlatTM simulating `M` -/

section Sim

variable (M : PvsNP.SingleTape.Machine (Bool ⊕ Bool) Bool)

noncomputable def G : ℕ := @Fintype.card M.Γ M.fintypeΓ
noncomputable def S : ℕ := @Fintype.card M.Λ M.fintypeΛ

lemma G_pos : 0 < G M :=
  @Fintype.card_pos M.Γ M.fintypeΓ ⟨M.blank.default⟩

lemma S_pos : 0 < S M :=
  @Fintype.card_pos M.Λ M.fintypeΛ ⟨M.start.default⟩

noncomputable def eΓ : M.Γ ≃ Fin (G M) := @Fintype.equivFin M.Γ M.fintypeΓ
noncomputable def eΛ : M.Λ ≃ Fin (S M) := @Fintype.equivFin M.Λ M.fintypeΛ

noncomputable def pairSym (a b : M.Γ) : ℕ :=
  4 + (eΓ M a).val * G M + (eΓ M b).val

lemma pairSym_ge (a b : M.Γ) : 4 ≤ pairSym M a b := by
  unfold pairSym; omega

lemma pairSym_lt (a b : M.Γ) : pairSym M a b < 4 + G M * G M := by
  unfold pairSym
  have ha : (eΓ M a).val < G M := (eΓ M a).isLt
  have hb : (eΓ M b).val < G M := (eΓ M b).isLt
  have h1 : (eΓ M a).val * G M + (eΓ M b).val < (eΓ M a).val * G M + G M :=
    Nat.add_lt_add_left hb _
  have h2 : (eΓ M a).val * G M + G M = ((eΓ M a).val + 1) * G M := by
    rw [Nat.add_mul, Nat.one_mul]
  have h3 : ((eΓ M a).val + 1) * G M ≤ G M * G M :=
    Nat.mul_le_mul_right _ ha
  omega

lemma pairSym_injective {a₁ b₁ a₂ b₂ : M.Γ} (h : pairSym M a₁ b₁ = pairSym M a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  unfold pairSym at h
  have hG : 0 < G M := G_pos M
  have hb₁ : (eΓ M b₁).val < G M := (eΓ M b₁).isLt
  have hb₂ : (eΓ M b₂).val < G M := (eΓ M b₂).isLt
  have hsum : (eΓ M a₁).val * G M + (eΓ M b₁).val = (eΓ M a₂).val * G M + (eΓ M b₂).val := by omega
  have hdiv : (G M * (eΓ M a₁).val + (eΓ M b₁).val) / G M =
      (G M * (eΓ M a₂).val + (eΓ M b₂).val) / G M := by
    rw [Nat.mul_comm (G M), Nat.mul_comm (G M), hsum]
  have hmod : (G M * (eΓ M a₁).val + (eΓ M b₁).val) % G M =
      (G M * (eΓ M a₂).val + (eΓ M b₂).val) % G M := by
    rw [Nat.mul_comm (G M), Nat.mul_comm (G M), hsum]
  rw [Nat.mul_add_div hG, Nat.mul_add_div hG, Nat.div_eq_of_lt hb₁, Nat.div_eq_of_lt hb₂] at hdiv
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] at hmod
  have ha : eΓ M a₁ = eΓ M a₂ := Fin.ext (by omega)
  have hb : eΓ M b₁ = eΓ M b₂ := Fin.ext hmod
  exact ⟨(eΓ M).injective ha, (eΓ M).injective hb⟩

noncomputable def blankSym : ℕ := pairSym M default default

noncomputable def decodePair (s : ℕ) : M.Γ × M.Γ :=
  if h : 4 ≤ s ∧ s < 4 + G M * G M then
    let k := s - 4
    have hG : 0 < G M := G_pos M
    have hq : k / G M < G M := Nat.div_lt_of_lt_mul (by omega)
    have hr : k % G M < G M := Nat.mod_lt k hG
    ((eΓ M).symm ⟨k / G M, hq⟩, (eΓ M).symm ⟨k % G M, hr⟩)
  else
    (default, default)

lemma decodePair_pairSym (a b : M.Γ) : decodePair M (pairSym M a b) = (a, b) := by
  have hge := pairSym_ge M a b
  have hlt := pairSym_lt M a b
  have hG : 0 < G M := G_pos M
  have hb : (eΓ M b).val < G M := (eΓ M b).isLt
  unfold decodePair
  rw [dif_pos ⟨hge, hlt⟩]
  have hk : pairSym M a b - 4 = G M * (eΓ M a).val + (eΓ M b).val := by
    unfold pairSym; rw [Nat.mul_comm]; omega
  have hq : (pairSym M a b - 4) / G M = (eΓ M a).val := by
    rw [hk, Nat.mul_add_div hG, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hr : (pairSym M a b - 4) % G M = (eΓ M b).val := by
    rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  refine Prod.ext ?_ ?_
  · apply (eΓ M).injective
    simp only [Equiv.apply_symm_apply]
    exact Fin.ext hq
  · apply (eΓ M).injective
    simp only [Equiv.apply_symm_apply]
    exact Fin.ext hr

def stStart : ℕ := 0
def stReadX : ℕ := 1
def stShiftCRead : ℕ := 2
def stShiftCWriteF : ℕ := 3
def stShiftCWriteT : ℕ := 4
def stShiftCStepR : ℕ := 5
def stClearEnd : ℕ := 6
def stRewind : ℕ := 7
def stAcc : ℕ := 8
def stRej : ℕ := 9

noncomputable def stSim (q : M.Λ) (pos : Bool) : ℕ :=
  10 + 4 * (eΛ M q).val + if pos then 0 else 1

noncomputable def stBounce (q : M.Λ) (pos : Bool) : ℕ :=
  10 + 4 * (eΛ M q).val + if pos then 2 else 3

noncomputable def numStates : ℕ := 10 + 4 * S M
noncomputable def sigSize : ℕ := 4 + G M * G M

lemma stSim_lt (q : M.Λ) (pos : Bool) : stSim M q pos < numStates M := by
  unfold stSim numStates; have hq := (eΛ M q).isLt; cases pos <;> simp <;> omega

lemma stBounce_lt (q : M.Λ) (pos : Bool) : stBounce M q pos < numStates M := by
  unfold stBounce numStates; have hq := (eΛ M q).isLt; cases pos <;> simp <;> omega

lemma stSim_inj {q₁ q₂ : M.Λ} {p₁ p₂ : Bool} (h : stSim M q₁ p₁ = stSim M q₂ p₂) :
    q₁ = q₂ ∧ p₁ = p₂ := by
  unfold stSim at h
  have hp : p₁ = p₂ := by cases p₁ <;> cases p₂ <;> simp at h ⊢ <;> omega
  subst hp
  have hq : (eΛ M q₁).val = (eΛ M q₂).val := by cases p₁ <;> simp at h <;> omega
  exact ⟨(eΛ M).injective (Fin.ext hq), rfl⟩

lemma stBounce_inj {q₁ q₂ : M.Λ} {p₁ p₂ : Bool} (h : stBounce M q₁ p₁ = stBounce M q₂ p₂) :
    q₁ = q₂ ∧ p₁ = p₂ := by
  unfold stBounce at h
  have hp : p₁ = p₂ := by cases p₁ <;> cases p₂ <;> simp at h ⊢ <;> omega
  subst hp
  have hq : (eΛ M q₁).val = (eΛ M q₂).val := by cases p₁ <;> simp at h <;> omega
  exact ⟨(eΛ M).injective (Fin.ext hq), rfl⟩

lemma stSim_ne_stBounce (q₁ q₂ : M.Λ) (p₁ p₂ : Bool) : stSim M q₁ p₁ ≠ stBounce M q₂ p₂ := by
  unfold stSim stBounce; cases p₁ <;> cases p₂ <;> simp <;> omega

noncomputable def allΓ : List M.Γ := (List.finRange (G M)).map (eΓ M).symm
noncomputable def allΛ : List M.Λ := (List.finRange (S M)).map (eΛ M).symm

lemma mem_allΓ (g : M.Γ) : g ∈ allΓ M := by
  unfold allΓ; rw [List.mem_map]
  exact ⟨eΓ M g, List.mem_finRange _, (eΓ M).symm_apply_apply g⟩

lemma mem_allΛ (q : M.Λ) : q ∈ allΛ M := by
  unfold allΛ; rw [List.mem_map]
  exact ⟨eΛ M q, List.mem_finRange _, (eΛ M).symm_apply_apply q⟩

noncomputable def allPairs : List (M.Γ × M.Γ) :=
  (allΓ M).flatMap (fun a => (allΓ M).map (fun b => (a, b)))

lemma mem_allPairs (a b : M.Γ) : (a, b) ∈ allPairs M := by
  unfold allPairs; rw [List.mem_flatMap]
  refine ⟨a, mem_allΓ M a, ?_⟩
  rw [List.mem_map]; exact ⟨b, mem_allΓ M b, rfl⟩

noncomputable def preTrans : List FlatTMTransEntry :=
  [ mk1 stStart (some 3) stReadX none .Rmove
  , mk1 stReadX (some 1) stReadX (some (pairSym M (M.inp (Sum.inl false)) default)) .Rmove
  , mk1 stReadX (some 2) stReadX (some (pairSym M (M.inp (Sum.inl true)) default)) .Rmove
  , mk1 stReadX (some 0) stShiftCRead (some (blankSym M)) .Rmove
  , mk1 stShiftCRead (some 1) stShiftCWriteF (some (blankSym M)) .Lmove
  , mk1 stShiftCRead (some 2) stShiftCWriteT (some (blankSym M)) .Lmove
  , mk1 stShiftCRead (some 0) stClearEnd (some (blankSym M)) .Rmove
  , mk1 stShiftCWriteF (some (blankSym M)) stShiftCStepR
      (some (pairSym M (M.inp (Sum.inr false)) default)) .Rmove
  , mk1 stShiftCWriteT (some (blankSym M)) stShiftCStepR
      (some (pairSym M (M.inp (Sum.inr true)) default)) .Rmove
  , mk1 stShiftCStepR (some (blankSym M)) stShiftCRead none .Rmove
  , mk1 stClearEnd (some 3) stRewind (some (blankSym M)) .Lmove
  , mk1 stRewind (some 3) (stSim M default true) none .Rmove
  ] ++
  (allPairs M).map (fun ab =>
    mk1 stRewind (some (pairSym M ab.1 ab.2)) stRewind none .Lmove)

noncomputable def simEntry (q : M.Λ) (pos : Bool) (cell : Option (M.Γ × M.Γ)) : FlatTMTransEntry :=
  let ab := cell.getD (default, default)
  let a := ab.1
  let b := ab.2
  let sym := if pos then a else b
  let rd : Option ℕ := cell.map (fun p => pairSym M p.1 p.2)
  match M.δ q sym with
  | none =>
      let dst := if @decide (sym = M.out true) (Classical.propDecidable _) then stAcc else stRej
      mk1 (stSim M q pos) rd dst none .Nmove
  | some (q', .write w) =>
      let wr := if pos then pairSym M w b else pairSym M a w
      mk1 (stSim M q pos) rd (stSim M q' pos) (some wr) .Nmove
  | some (q', .move dir) =>
      let outward : Bool := (pos && (dir == Turing.Dir.right)) || ((!pos) && (dir == Turing.Dir.left))
      if outward then
        mk1 (stSim M q pos) rd (stSim M q' pos) (some (pairSym M a b)) .Rmove
      else
        mk1 (stSim M q pos) rd (stBounce M q' pos) (some (pairSym M a b)) .Lmove

noncomputable def simTrans : List FlatTMTransEntry :=
  (allΛ M).flatMap (fun q =>
    [true, false].flatMap (fun pos =>
      simEntry M q pos none ::
      (allPairs M).map (fun ab => simEntry M q pos (some ab))))

noncomputable def bounceTrans : List FlatTMTransEntry :=
  (allΛ M).flatMap (fun q =>
    [true, false].flatMap (fun pos =>
      mk1 (stBounce M q pos) (some 3) (stSim M q (!pos)) none .Rmove ::
      (allPairs M).map (fun ab =>
        mk1 (stBounce M q pos) (some (pairSym M ab.1 ab.2)) (stSim M q pos) none .Nmove)))

noncomputable def simFlatTM : FlatTM where
  sig := sigSize M
  tapes := 1
  states := numStates M
  trans := preTrans M ++ simTrans M ++ bounceTrans M
  start := stStart
  halt := List.ofFn (fun i : Fin (numStates M) => i.val == stAcc || i.val == stRej)

lemma mk1_valid (src : ℕ) (rd : Option ℕ) (dst : ℕ) (wr : Option ℕ) (mv : TMMove)
    (hsrc : src < numStates M) (hdst : dst < numStates M)
    (hrd : match rd with | none => True | some v => v < sigSize M)
    (hwr : match wr with | none => True | some v => v < sigSize M) :
    flatTMTransEntryValid (simFlatTM M) (mk1 src rd dst wr mv) := by
  refine ⟨hsrc, hdst, rfl, rfl, rfl, ?_, ?_⟩
  · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hrd
  · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hwr

lemma valid_simFlatTM : validFlatTM (simFlatTM M) := by
  have hS : 0 < S M := S_pos M
  have hG : 0 < G M := G_pos M
  have hsig3 : 3 < sigSize M := by unfold sigSize; nlinarith
  have hsig2 : 2 < sigSize M := by omega
  have hsig1 : 1 < sigSize M := by omega
  have hsig0 : 0 < sigSize M := by omega
  have hst : ∀ n, n < 10 → n < numStates M := by intro n hn; unfold numStates; omega
  refine ⟨hst 0 (by omega), by simp [simFlatTM], ?_⟩
  intro e he
  simp only [simFlatTM, List.mem_append] at he
  rcases he with (hpre | hsim) | hbn
  · unfold preTrans at hpre
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hpre
    rcases hpre with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨ab, _, rfl⟩
    · exact mk1_valid M _ _ _ _ _ (hst 0 (by omega)) (hst 1 (by omega)) hsig3 trivial
    · exact mk1_valid M _ _ _ _ _ (hst 1 (by omega)) (hst 1 (by omega)) hsig1 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 1 (by omega)) (hst 1 (by omega)) hsig2 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 1 (by omega)) (hst 2 (by omega)) hsig0 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 2 (by omega)) (hst 3 (by omega)) hsig1 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 2 (by omega)) (hst 4 (by omega)) hsig2 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 2 (by omega)) (hst 6 (by omega)) hsig0 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 3 (by omega)) (hst 5 (by omega)) (pairSym_lt M _ _) (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 4 (by omega)) (hst 5 (by omega)) (pairSym_lt M _ _) (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 5 (by omega)) (hst 2 (by omega)) (pairSym_lt M _ _) trivial
    · exact mk1_valid M _ _ _ _ _ (hst 6 (by omega)) (hst 7 (by omega)) hsig3 (pairSym_lt M _ _)
    · exact mk1_valid M _ _ _ _ _ (hst 7 (by omega)) (stSim_lt M _ _) hsig3 trivial
    · exact mk1_valid M _ _ _ _ _ (hst 7 (by omega)) (hst 7 (by omega)) (pairSym_lt M _ _) trivial
  · unfold simTrans at hsim
    rw [List.mem_flatMap] at hsim; rcases hsim with ⟨q, _, hsim⟩
    rw [List.mem_flatMap] at hsim; rcases hsim with ⟨pos, _, hsim⟩
    have hcell : ∃ cell : Option (M.Γ × M.Γ), e = simEntry M q pos cell := by
      rcases List.mem_cons.mp hsim with rfl | hmap
      · exact ⟨none, rfl⟩
      · rw [List.mem_map] at hmap; rcases hmap with ⟨ab, _, rfl⟩; exact ⟨some ab, rfl⟩
    rcases hcell with ⟨cell, rfl⟩
    unfold simEntry
    have hrd : match cell.map (fun p => pairSym M p.1 p.2) with
        | none => True | some v => v < sigSize M := by
      cases cell with
      | none => trivial
      | some ab => exact pairSym_lt M ab.1 ab.2
    cases hδ : M.δ q (if pos then (cell.getD (default, default)).1
                      else (cell.getD (default, default)).2) with
    | none =>
        dsimp only [simEntry]
        rw [hδ]
        dsimp only
        exact mk1_valid M _ _ _ _ _ (stSim_lt M q pos)
          (by
            by_cases hc : (@decide ((if pos then (cell.getD (default, default)).1 else (cell.getD (default, default)).2) = M.out true) (Classical.propDecidable _)) = true
            · simp only [hc, ↓reduceIte]; exact hst 8 (by omega)
            · simp only [hc, ↓reduceIte]; exact hst 9 (by omega)) hrd trivial
    | some p =>
        rcases p with ⟨q', stmt⟩
        cases stmt with
        | write w =>
            dsimp only [simEntry]
            rw [hδ]
            dsimp only
            split_ifs
            · exact mk1_valid M _ _ _ _ _ (stSim_lt M q pos) (stSim_lt M q' pos) hrd (pairSym_lt M _ _)
            · exact mk1_valid M _ _ _ _ _ (stSim_lt M q pos) (stSim_lt M q' pos) hrd (pairSym_lt M _ _)
        | move dir =>
            dsimp only [simEntry]
            rw [hδ]
            dsimp only
            split_ifs
            · exact mk1_valid M _ _ _ _ _ (stSim_lt M q pos) (stSim_lt M q' pos) hrd (pairSym_lt M _ _)
            · exact mk1_valid M _ _ _ _ _ (stSim_lt M q pos) (stBounce_lt M q' pos) hrd (pairSym_lt M _ _)
  · unfold bounceTrans at hbn
    rw [List.mem_flatMap] at hbn; rcases hbn with ⟨q, _, hbn⟩
    rw [List.mem_flatMap] at hbn; rcases hbn with ⟨pos, _, hbn⟩
    rcases List.mem_cons.mp hbn with rfl | hmap
    · exact mk1_valid M _ _ _ _ _ (stBounce_lt M q pos) (stSim_lt M q (!pos)) hsig3 trivial
    · rw [List.mem_map] at hmap; rcases hmap with ⟨ab, _, rfl⟩
      exact mk1_valid M _ _ _ _ _ (stBounce_lt M q pos) (stSim_lt M q pos) (pairSym_lt M _ _) trivial

lemma simEntry_src (q : M.Λ) (pos : Bool) (cell : Option (M.Γ × M.Γ)) :
    (simEntry M q pos cell).src_state = stSim M q pos ∧
    (simEntry M q pos cell).src_tape_vals = [cell.map (fun p => pairSym M p.1 p.2)] := by
  dsimp only [simEntry]
  cases M.δ q (if pos then (cell.getD (default, default)).1 else (cell.getD (default, default)).2) with
  | none => exact ⟨rfl, rfl⟩
  | some p =>
      rcases p with ⟨q', stmt⟩
      cases stmt with
      | write w => exact ⟨rfl, rfl⟩
      | move dir => dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

lemma trans_key_unique {e₁ e₂ : FlatTMTransEntry}
    (h₁ : e₁ ∈ (simFlatTM M).trans) (h₂ : e₂ ∈ (simFlatTM M).trans)
    (hs : e₁.src_state = e₂.src_state) (ht : e₁.src_tape_vals = e₂.src_tape_vals) :
    e₁ = e₂ := by
  have hpre_lt : ∀ e ∈ preTrans M, e.src_state < 10 := by
    intro e he; unfold preTrans at he
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at he
    rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨ab, _, rfl⟩ <;>
      simp [mk1, stStart, stReadX, stShiftCRead, stShiftCWriteF, stShiftCWriteT, stShiftCStepR, stClearEnd, stRewind]
  have hsim_ge : ∀ e ∈ simTrans M, ∃ q pos cell, e = simEntry M q pos cell := by
    intro e he; unfold simTrans at he
    rw [List.mem_flatMap] at he; rcases he with ⟨q, _, he⟩
    rw [List.mem_flatMap] at he; rcases he with ⟨pos, _, he⟩
    rcases List.mem_cons.mp he with rfl | hmap
    · exact ⟨q, pos, none, rfl⟩
    · rw [List.mem_map] at hmap; rcases hmap with ⟨ab, _, rfl⟩; exact ⟨q, pos, some ab, rfl⟩
  have hbn_ge : ∀ e ∈ bounceTrans M, ∃ q pos,
      e = mk1 (stBounce M q pos) (some 3) (stSim M q (!pos)) none .Rmove ∨
      ∃ ab : M.Γ × M.Γ, e = mk1 (stBounce M q pos) (some (pairSym M ab.1 ab.2)) (stSim M q pos) none .Nmove := by
    intro e he; unfold bounceTrans at he
    rw [List.mem_flatMap] at he; rcases he with ⟨q, _, he⟩
    rw [List.mem_flatMap] at he; rcases he with ⟨pos, _, he⟩
    rcases List.mem_cons.mp he with rfl | hmap
    · exact ⟨q, pos, Or.inl rfl⟩
    · rw [List.mem_map] at hmap; rcases hmap with ⟨ab, _, rfl⟩; exact ⟨q, pos, Or.inr ⟨ab, rfl⟩⟩
  have hstSim_ge10 : ∀ q pos, 10 ≤ stSim M q pos := by intro q pos; unfold stSim; cases pos <;> simp <;> omega
  have hstBn_ge10 : ∀ q pos, 10 ≤ stBounce M q pos := by intro q pos; unfold stBounce; cases pos <;> simp <;> omega
  simp only [simFlatTM, List.mem_append] at h₁ h₂
  rcases h₁ with (hp₁ | hs₁) | hb₁ <;> rcases h₂ with (hp₂ | hs₂) | hb₂
  · have hge4 : ∀ a b, pairSym M a b ≠ 3 := by intro a b; have := pairSym_ge M a b; omega
    unfold preTrans at hp₁ hp₂
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp₁ hp₂
    rcases hp₁ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨ab₁, _, rfl⟩ <;>
    rcases hp₂ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨ab₂, _, rfl⟩ <;>
    simp [mk1, stStart, stReadX, stShiftCRead, stShiftCWriteF, stShiftCWriteT, stShiftCStepR, stClearEnd, stRewind] at hs ht ⊢
    · exact absurd ht.symm (hge4 _ _)
    · exact absurd ht (hge4 _ _)
    · exact ht
  · rcases hsim_ge e₂ hs₂ with ⟨q, pos, cell, rfl⟩
    have h1 := hpre_lt e₁ hp₁; have h2 := hstSim_ge10 q pos
    rw [(simEntry_src M q pos cell).1] at hs; omega
  · rcases hbn_ge e₂ hb₂ with ⟨q, pos, rfl | ⟨ab, rfl⟩⟩ <;>
      (have h1 := hpre_lt e₁ hp₁; have h2 := hstBn_ge10 q pos; simp [mk1] at hs; omega)
  · rcases hsim_ge e₁ hs₁ with ⟨q, pos, cell, rfl⟩
    have h1 := hpre_lt e₂ hp₂; have h2 := hstSim_ge10 q pos
    rw [(simEntry_src M q pos cell).1] at hs; omega
  · rcases hsim_ge e₁ hs₁ with ⟨q₁, p₁, c₁, rfl⟩
    rcases hsim_ge e₂ hs₂ with ⟨q₂, p₂, c₂, rfl⟩
    rw [(simEntry_src M q₁ p₁ c₁).1, (simEntry_src M q₂ p₂ c₂).1] at hs
    obtain ⟨rfl, rfl⟩ := stSim_inj M hs
    rw [(simEntry_src M q₁ p₁ c₁).2, (simEntry_src M q₁ p₁ c₂).2] at ht
    have hc : c₁ = c₂ := by
      cases c₁ <;> cases c₂ <;> simp at ht ⊢
      rcases pairSym_injective M ht with ⟨h1, h2⟩
      exact Prod.ext h1 h2
    subst hc; rfl
  · rcases hsim_ge e₁ hs₁ with ⟨q₁, p₁, c₁, rfl⟩
    rcases hbn_ge e₂ hb₂ with ⟨q₂, p₂, rfl | ⟨ab, rfl⟩⟩ <;>
      (rw [(simEntry_src M q₁ p₁ c₁).1] at hs; exact absurd hs (stSim_ne_stBounce M _ _ _ _))
  · rcases hbn_ge e₁ hb₁ with ⟨q, pos, rfl | ⟨ab, rfl⟩⟩ <;>
      (have h1 := hpre_lt e₂ hp₂; have h2 := hstBn_ge10 q pos; simp [mk1] at hs; omega)
  · rcases hbn_ge e₁ hb₁ with ⟨q₁, p₁, rfl | ⟨ab, rfl⟩⟩ <;>
      (rcases hsim_ge e₂ hs₂ with ⟨q₂, p₂, c₂, rfl⟩; rw [(simEntry_src M q₂ p₂ c₂).1] at hs;
       exact absurd hs.symm (stSim_ne_stBounce M _ _ _ _))
  · have hge4 : ∀ a b, pairSym M a b ≠ 3 := by intro a b; have := pairSym_ge M a b; omega
    rcases hbn_ge e₁ hb₁ with ⟨q₁, p₁, rfl | ⟨ab₁, rfl⟩⟩ <;>
    rcases hbn_ge e₂ hb₂ with ⟨q₂, p₂, rfl | ⟨ab₂, rfl⟩⟩
    · simp only [mk1] at hs; obtain ⟨rfl, rfl⟩ := stBounce_inj M hs; rfl
    · simp only [mk1] at ht; injection ht with ht'; injection ht' with ht''; exact absurd ht''.symm (hge4 _ _)
    · simp only [mk1] at ht; injection ht with ht'; injection ht' with ht''; exact absurd ht'' (hge4 _ _)
    · simp only [mk1] at hs ht; obtain ⟨rfl, rfl⟩ := stBounce_inj M hs
      injection ht with ht'; injection ht' with ht''; rw [ht'']

lemma step_of_mem (e : FlatTMTransEntry) (st head : ℕ) (right : List ℕ)
    (hmem : e ∈ (simFlatTM M).trans)
    (hst : e.src_state = st)
    (htp : e.src_tape_vals = [currentTapeSymbol ([], head, right)]) :
    stepFlatTM (simFlatTM M) ⟨st, [([], head, right)]⟩ =
      applyTransitionEntry ⟨st, [([], head, right)]⟩ e := by
  apply stepFlatTM_of_unique (simFlatTM M) e ⟨st, [([], head, right)]⟩ hmem
  · simp [entryMatchesConfig, hst, htp]
  · intro e' he' hm
    simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    exact trans_key_unique M he' hmem (hm.1.trans hst.symm) (hm.2.trans htp.symm)

lemma halting_iff (cfg : FlatTMConfig) :
    haltingStateReached (simFlatTM M) cfg = true ↔
      cfg.state_idx = stAcc ∨ cfg.state_idx = stRej := by
  have hacc : stAcc < numStates M := by unfold stAcc numStates; omega
  have hrej : stRej < numStates M := by unfold stRej numStates; omega
  unfold haltingStateReached simFlatTM
  by_cases hlt : cfg.state_idx < numStates M
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, stAcc, stRej]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt]; omega

lemma not_halting_of_ne (cfg : FlatTMConfig) (h1 : cfg.state_idx ≠ stAcc) (h2 : cfg.state_idx ≠ stRej) :
    haltingStateReached (simFlatTM M) cfg = false := by
  cases hv : haltingStateReached (simFlatTM M) cfg with
  | false => rfl
  | true =>
      rcases (halting_iff M cfg).mp hv with h | h
      · exact absurd h h1
      · exact absurd h h2

lemma step_mk1 (st dst head : ℕ) (right : List ℕ) (rd wr : Option ℕ) (mv : TMMove)
    (hmem : mk1 st rd dst wr mv ∈ (simFlatTM M).trans)
    (hrd : currentTapeSymbol ([], head, right) = rd)
    (h1 : st ≠ stAcc) (h2 : st ≠ stRej) :
    runFlatTM 1 (simFlatTM M) ⟨st, [([], head, right)]⟩ =
      some ⟨dst, [tapeStep ([], head, right) wr mv]⟩ := by
  apply runFlatTM_step_one
  · exact not_halting_of_ne M _ h1 h2
  · rw [step_of_mem M (mk1 st rd dst wr mv) st head right hmem rfl (by simp [mk1, hrd])]
    simp [applyTransitionEntry, mk1]

/-! ### Preprocessing `pairTape x c` inside `simFlatTM` -/

noncomputable def encodeInl (x : List Bool) : List ℕ :=
  x.map (fun b => pairSym M (M.inp (Sum.inl b)) default)

noncomputable def encodeInr (c : List Bool) : List ℕ :=
  c.map (fun b => pairSym M (M.inp (Sum.inr b)) default)

lemma run_readX (x : List Bool) (pre suf : List ℕ) :
    runFlatTM x.length (simFlatTM M)
      ⟨stReadX, [([], pre.length, pre ++ symbolsOf x ++ suf)]⟩ =
    some ⟨stReadX, [([], (pre ++ encodeInl M x).length, pre ++ encodeInl M x ++ suf)]⟩ := by
  induction x generalizing pre with
  | nil => simp [symbolsOf, encodeInl, runFlatTM]
  | cons b tl ih =>
      have hlen : (b :: tl).length = 1 + tl.length := by simp; omega
      rw [hlen]
      have hstep : runFlatTM 1 (simFlatTM M)
          ⟨stReadX, [([], pre.length, pre ++ symbolsOf (b :: tl) ++ suf)]⟩ =
          some ⟨stReadX, [([], (pre ++ [pairSym M (M.inp (Sum.inl b)) default]).length,
            (pre ++ [pairSym M (M.inp (Sum.inl b)) default]) ++ symbolsOf tl ++ suf)]⟩ := by
        cases b with
        | false =>
            have hmem : mk1 stReadX (some 1) stReadX
                (some (pairSym M (M.inp (Sum.inl false)) default)) .Rmove ∈ (simFlatTM M).trans := by
              simp [simFlatTM, preTrans]
            have hcfg : pre ++ symbolsOf (false :: tl) ++ suf = pre ++ 1 :: (symbolsOf tl ++ suf) := by
              simp [symbolsOf]
            rw [hcfg, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at pre 1 _) (by decide) (by decide),
                tapeStep_write_at]
            simp [moveTapeHead, List.append_assoc]
        | true =>
            have hmem : mk1 stReadX (some 2) stReadX
                (some (pairSym M (M.inp (Sum.inl true)) default)) .Rmove ∈ (simFlatTM M).trans := by
              simp [simFlatTM, preTrans]
            have hcfg : pre ++ symbolsOf (true :: tl) ++ suf = pre ++ 2 :: (symbolsOf tl ++ suf) := by
              simp [symbolsOf]
            rw [hcfg, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at pre 2 _) (by decide) (by decide),
                tapeStep_write_at]
            simp [moveTapeHead, List.append_assoc]
      rw [runFlatTM_compose (simFlatTM M) 1 tl.length _ _ hstep]
      simpa [encodeInl, List.append_assoc] using ih (pre ++ [pairSym M (M.inp (Sum.inl b)) default])

lemma run_shiftC (c : List Bool) (pre suf : List ℕ) :
    runFlatTM (3 * c.length) (simFlatTM M)
      ⟨stShiftCRead, [([], pre.length + 1, pre ++ blankSym M :: symbolsOf c ++ suf)]⟩ =
    some ⟨stShiftCRead,
      [([], (pre ++ encodeInr M c).length + 1,
        (pre ++ encodeInr M c) ++ blankSym M :: suf)]⟩ := by
  induction c generalizing pre with
  | nil => simp [symbolsOf, encodeInr, runFlatTM]
  | cons b tl ih =>
      have h3 : 3 * (b :: tl).length = 3 + 3 * tl.length := by simp; omega
      rw [h3]
      let pb := pairSym M (M.inp (Sum.inr b)) default
      let preB := pre ++ [blankSym M]
      have hpreB_len : preB.length = pre.length + 1 := by simp [preB]
      have h1 : runFlatTM 1 (simFlatTM M)
          ⟨stShiftCRead, [([], pre.length + 1, pre ++ blankSym M :: symbolsOf (b :: tl) ++ suf)]⟩ =
          some ⟨if b then stShiftCWriteT else stShiftCWriteF,
            [([], pre.length, pre ++ blankSym M :: blankSym M :: (symbolsOf tl ++ suf))]⟩ := by
        cases b with
        | false =>
            have hmem : mk1 stShiftCRead (some 1) stShiftCWriteF (some (blankSym M)) .Lmove ∈ (simFlatTM M).trans := by
              simp [simFlatTM, preTrans]
            have hcfg : pre ++ blankSym M :: symbolsOf (false :: tl) ++ suf =
                preB ++ 1 :: (symbolsOf tl ++ suf) := by simp [preB, symbolsOf, List.append_assoc]
            rw [hcfg, ← hpreB_len, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at preB 1 _) (by decide) (by decide),
                tapeStep_write_at]
            simp [moveTapeHead, preB, List.append_assoc]
        | true =>
            have hmem : mk1 stShiftCRead (some 2) stShiftCWriteT (some (blankSym M)) .Lmove ∈ (simFlatTM M).trans := by
              simp [simFlatTM, preTrans]
            have hcfg : pre ++ blankSym M :: symbolsOf (true :: tl) ++ suf =
                preB ++ 2 :: (symbolsOf tl ++ suf) := by simp [preB, symbolsOf, List.append_assoc]
            rw [hcfg, ← hpreB_len, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at preB 2 _) (by decide) (by decide),
                tapeStep_write_at]
            simp [moveTapeHead, preB, List.append_assoc]
      have h2 : runFlatTM 1 (simFlatTM M)
          ⟨if b then stShiftCWriteT else stShiftCWriteF,
            [([], pre.length, pre ++ blankSym M :: blankSym M :: (symbolsOf tl ++ suf))]⟩ =
          some ⟨stShiftCStepR,
            [([], pre.length + 1, pre ++ pb :: blankSym M :: (symbolsOf tl ++ suf))]⟩ := by
        cases b with
        | false =>
            have hmem : mk1 stShiftCWriteF (some (blankSym M)) stShiftCStepR (some pb) .Rmove ∈ (simFlatTM M).trans := by
              simp [simFlatTM, preTrans, pb]
            have hs := step_mk1 M stShiftCWriteF stShiftCStepR pre.length
              (pre ++ blankSym M :: blankSym M :: (symbolsOf tl ++ suf))
              (some (blankSym M)) (some pb) .Rmove hmem (currentTapeSymbol_at pre (blankSym M) _) (by decide) (by decide)
            rw [tapeStep_write_at] at hs
            simpa [moveTapeHead] using hs
        | true =>
            have hmem : mk1 stShiftCWriteT (some (blankSym M)) stShiftCStepR (some pb) .Rmove ∈ (simFlatTM M).trans := by
              simp [simFlatTM, preTrans, pb]
            have hs := step_mk1 M stShiftCWriteT stShiftCStepR pre.length
              (pre ++ blankSym M :: blankSym M :: (symbolsOf tl ++ suf))
              (some (blankSym M)) (some pb) .Rmove hmem (currentTapeSymbol_at pre (blankSym M) _) (by decide) (by decide)
            rw [tapeStep_write_at] at hs
            simpa [moveTapeHead] using hs
      have hstep3 : runFlatTM 1 (simFlatTM M)
          ⟨stShiftCStepR,
            [([], pre.length + 1, pre ++ pb :: blankSym M :: (symbolsOf tl ++ suf))]⟩ =
          some ⟨stShiftCRead,
            [([], (pre ++ [pb]).length + 1, (pre ++ [pb]) ++ blankSym M :: symbolsOf tl ++ suf)]⟩ := by
        have hmem : mk1 stShiftCStepR (some (blankSym M)) stShiftCRead none .Rmove ∈ (simFlatTM M).trans := by
          simp [simFlatTM, preTrans]
        have hcfg : pre ++ pb :: blankSym M :: (symbolsOf tl ++ suf) =
            (pre ++ [pb]) ++ blankSym M :: (symbolsOf tl ++ suf) := by simp [List.append_assoc]
        have hplen : (pre ++ [pb]).length = pre.length + 1 := by simp
        rw [hcfg, ← hplen, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at (pre ++ [pb]) (blankSym M) _) (by decide) (by decide)]
        simp [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc]
      have h123 : runFlatTM 3 (simFlatTM M)
          ⟨stShiftCRead, [([], pre.length + 1, pre ++ blankSym M :: symbolsOf (b :: tl) ++ suf)]⟩ =
          some ⟨stShiftCRead,
            [([], (pre ++ [pb]).length + 1, (pre ++ [pb]) ++ blankSym M :: symbolsOf tl ++ suf)]⟩ := by
        have h12 := runFlatTM_compose (simFlatTM M) 1 1 _ _ h1
        rw [h2] at h12
        have h123' := runFlatTM_compose (simFlatTM M) 2 1 _ _ h12
        rw [hstep3] at h123'
        exact h123'
      rw [runFlatTM_compose (simFlatTM M) 3 (3 * tl.length) _ _ h123]
      simpa [encodeInr, pb, List.append_assoc] using ih (pre ++ [pb])

lemma run_rewind (ps : List (M.Γ × M.Γ)) (suf : List ℕ) :
    runFlatTM ps.length (simFlatTM M)
      ⟨stRewind, [([], ps.length, 3 :: (ps.map (fun ab => pairSym M ab.1 ab.2) ++ suf))]⟩ =
    some ⟨stRewind, [([], 0, 3 :: (ps.map (fun ab => pairSym M ab.1 ab.2) ++ suf))]⟩ := by
  induction ps using List.reverseRecOn generalizing suf with
  | nil => simp [runFlatTM]
  | append_singleton init ab ih =>
      have hlen : (init ++ [ab]).length = 1 + init.length := by simp; omega
      let pSym := pairSym M ab.1 ab.2
      have hmem : mk1 stRewind (some pSym) stRewind none .Lmove ∈ (simFlatTM M).trans := by
        simp only [simFlatTM, List.mem_append, preTrans, List.mem_map]
        left; left; right
        exact ⟨ab, mem_allPairs M ab.1 ab.2, rfl⟩
      have hcfg : 3 :: ((init ++ [ab]).map (fun p => pairSym M p.1 p.2) ++ suf) =
          (3 :: init.map (fun p => pairSym M p.1 p.2)) ++ pSym :: suf := by
        simp [pSym, List.append_assoc]
      have hidx : (init ++ [ab]).length = (3 :: init.map (fun p => pairSym M p.1 p.2)).length := by simp
      have hstep : runFlatTM 1 (simFlatTM M)
          ⟨stRewind, [([], (init ++ [ab]).length, 3 :: ((init ++ [ab]).map (fun p => pairSym M p.1 p.2) ++ suf))]⟩ =
          some ⟨stRewind, [([], init.length, 3 :: (init.map (fun p => pairSym M p.1 p.2) ++ (pSym :: suf)))]⟩ := by
        rw [hcfg, hidx, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at _ pSym suf) (by decide) (by decide)]
        simp [tapeStep, writeCurrentTapeSymbol, moveTapeHead]
      have hcomp := runFlatTM_compose (simFlatTM M) 1 init.length _ _ hstep
      rw [← hlen] at hcomp
      rw [hcomp]
      simpa [pSym, List.append_assoc] using ih (pSym :: suf)

noncomputable def initPairs (x c : List Bool) : List (M.Γ × M.Γ) :=
  (x.map (fun b => (M.inp (Sum.inl b), default))) ++
  (c.map (fun b => (M.inp (Sum.inr b), default))) ++
  [(default, default), (default, default), (default, default)]

noncomputable def initTapeAfterPre (x c : List Bool) : List ℕ :=
  3 :: (initPairs M x c).map (fun ab => pairSym M ab.1 ab.2)

lemma run_preprocess (x c : List Bool) :
    runFlatTM (2 * x.length + 4 * c.length + 7) (simFlatTM M)
      (initFlatConfig (simFlatTM M) [pairTape x c]) =
    some ⟨stSim M default true, [([], 1, initTapeAfterPre M x c)]⟩ := by
  have h1 : runFlatTM 1 (simFlatTM M) (initFlatConfig (simFlatTM M) [pairTape x c]) =
      some ⟨stReadX, [([], 1, [3] ++ symbolsOf x ++ (0 :: symbolsOf c ++ [0, 3]))]⟩ := by
    have hmem : mk1 stStart (some 3) stReadX none .Rmove ∈ (simFlatTM M).trans := by
      simp [simFlatTM, preTrans]
    have hcur : currentTapeSymbol ([], 0, pairTape x c) = some 3 := by
      have := currentTapeSymbol_at [] 3 (symbolsOf x ++ [0] ++ symbolsOf c ++ [0, 3])
      simpa [pairTape] using this
    have hs := step_mk1 M stStart stReadX 0 (pairTape x c) (some 3) none .Rmove hmem hcur (by decide) (by decide)
    simpa [initFlatConfig, simFlatTM, pairTape, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
  have h2 := run_readX M x [3] (0 :: symbolsOf c ++ [0, 3])
  simp only [List.length_singleton] at h2
  let preX := [3] ++ encodeInl M x
  have h3 : runFlatTM 1 (simFlatTM M)
      ⟨stReadX, [([], preX.length, preX ++ (0 :: symbolsOf c ++ [0, 3]))]⟩ =
      some ⟨stShiftCRead, [([], preX.length + 1, preX ++ blankSym M :: symbolsOf c ++ [0, 3])]⟩ := by
    have hmem : mk1 stReadX (some 0) stShiftCRead (some (blankSym M)) .Rmove ∈ (simFlatTM M).trans := by
      simp [simFlatTM, preTrans]
    have hs := step_mk1 M stReadX stShiftCRead preX.length (preX ++ 0 :: (symbolsOf c ++ [0, 3]))
      (some 0) (some (blankSym M)) .Rmove hmem (currentTapeSymbol_at preX 0 _) (by decide) (by decide)
    rw [tapeStep_write_at] at hs
    simpa [moveTapeHead, List.append_assoc] using hs
  have h4 := run_shiftC M c preX [0, 3]
  let preXC := preX ++ encodeInr M c
  have h5 : runFlatTM 1 (simFlatTM M)
      ⟨stShiftCRead, [([], preXC.length + 1, preXC ++ blankSym M :: [0, 3])]⟩ =
      some ⟨stClearEnd, [([], (preXC ++ [blankSym M, blankSym M]).length,
        (preXC ++ [blankSym M, blankSym M]) ++ [3])]⟩ := by
    have hmem : mk1 stShiftCRead (some 0) stClearEnd (some (blankSym M)) .Rmove ∈ (simFlatTM M).trans := by
      simp [simFlatTM, preTrans]
    have hcfg : preXC ++ blankSym M :: [0, 3] = (preXC ++ [blankSym M]) ++ 0 :: [3] := by
      simp [List.append_assoc]
    have hidx : preXC.length + 1 = (preXC ++ [blankSym M]).length := by simp
    rw [hcfg, hidx, step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at _ 0 _) (by decide) (by decide), tapeStep_write_at]
    simp [moveTapeHead, List.append_assoc]
  have h6 : runFlatTM 1 (simFlatTM M)
      ⟨stClearEnd, [([], (preXC ++ [blankSym M, blankSym M]).length,
        (preXC ++ [blankSym M, blankSym M]) ++ [3])]⟩ =
      some ⟨stRewind, [([], (x.length + c.length + 2),
        3 :: ((x.map (fun b => (M.inp (Sum.inl b), (default : M.Γ))) ++
               c.map (fun b => (M.inp (Sum.inr b), (default : M.Γ))) ++
               [(default, default), (default, default)]).map
                 (fun ab : M.Γ × M.Γ => pairSym M ab.1 ab.2) ++ [blankSym M]))]⟩ := by
    have hmem : mk1 stClearEnd (some 3) stRewind (some (blankSym M)) .Lmove ∈ (simFlatTM M).trans := by
      simp [simFlatTM, preTrans]
    rw [step_mk1 M _ _ _ _ _ _ _ hmem (currentTapeSymbol_at _ 3 []) (by decide) (by decide), tapeStep_write_at]
    simp only [moveTapeHead, preXC, preX, encodeInl, encodeInr, blankSym,
      List.length_append, List.length_cons, List.length_nil, List.length_map,
      List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      List.append_assoc, List.cons_append, List.nil_append]
    congr 2
  let rewPs : List (M.Γ × M.Γ) :=
    x.map (fun b => (M.inp (Sum.inl b), default)) ++
    c.map (fun b => (M.inp (Sum.inr b), default)) ++
    [(default, default), (default, default)]
  have hrewLen : rewPs.length = x.length + c.length + 2 := by simp [rewPs]; omega
  have h7 := run_rewind M rewPs [blankSym M]
  rw [hrewLen] at h7
  have h8 : runFlatTM 1 (simFlatTM M)
      ⟨stRewind, [([], 0, 3 :: (rewPs.map (fun ab => pairSym M ab.1 ab.2) ++ [blankSym M]))]⟩ =
      some ⟨stSim M default true, [([], 1, initTapeAfterPre M x c)]⟩ := by
    have hmem : mk1 stRewind (some 3) (stSim M default true) none .Rmove ∈ (simFlatTM M).trans := by
      simp [simFlatTM, preTrans]
    have hs := step_mk1 M stRewind (stSim M default true) 0
      ([] ++ 3 :: (rewPs.map (fun ab => pairSym M ab.1 ab.2) ++ [blankSym M]))
      (some 3) none .Rmove hmem (currentTapeSymbol_at [] 3 _) (by decide) (by decide)
    simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, initTapeAfterPre, initPairs, rewPs, blankSym, List.append_assoc] using hs
  have htot : 2 * x.length + 4 * c.length + 7 =
      ((((((1 + x.length) + 1) + 3 * c.length) + 1) + 1) + (x.length + c.length + 2)) + 1 := by omega
  rw [htot]
  have s12 := runFlatTM_compose (simFlatTM M) 1 x.length _ _ h1; rw [h2] at s12
  have s13 := runFlatTM_compose (simFlatTM M) (1 + x.length) 1 _ _ s12; rw [h3] at s13
  have s14 := runFlatTM_compose (simFlatTM M) (1 + x.length + 1) (3 * c.length) _ _ s13; rw [h4] at s14
  have s15 := runFlatTM_compose (simFlatTM M) (1 + x.length + 1 + 3 * c.length) 1 _ _ s14; rw [h5] at s15
  have s16 := runFlatTM_compose (simFlatTM M) (1 + x.length + 1 + 3 * c.length + 1) 1 _ _ s15; rw [h6] at s16
  have s17 := runFlatTM_compose (simFlatTM M) (1 + x.length + 1 + 3 * c.length + 1 + 1) (x.length + c.length + 2) _ _ s16; rw [h7] at s17
  have s18 := runFlatTM_compose (simFlatTM M) (1 + x.length + 1 + 3 * c.length + 1 + 1 + (x.length + c.length + 2)) 1 _ _ s17; rw [h8] at s18
  exact s18

/-! ### Lockstep simulation invariant -/

noncomputable def tapeAt (right : List ℕ) : ℤ → M.Γ
  | Int.ofNat j => (decodePair M (right.getD (j + 1) (blankSym M))).1
  | Int.negSucc j => (decodePair M (right.getD (j + 1) (blankSym M))).2

def headZ (head : ℕ) (pos : Bool) : ℤ :=
  if pos then Int.ofNat (head - 1) else Int.negSucc (head - 1)

def TapeWF (right : List ℕ) : Prop :=
  right[0]? = some 3 ∧
  ∀ i : ℕ, 1 ≤ i → i < right.length → ∃ a b : M.Γ, right[i]? = some (pairSym M a b)

def SimRel (head : ℕ) (pos : Bool) (right : List ℕ) (t : Turing.Tape M.Γ) : Prop :=
  1 ≤ head ∧ head ≤ right.length ∧ TapeWF M right ∧
  t.head = tapeAt M right (headZ head pos) ∧
  (∀ i : ℕ, t.right.nth i = tapeAt M right (headZ head pos + (i + 1 : ℤ))) ∧
  (∀ i : ℕ, t.left.nth i = tapeAt M right (headZ head pos - (i + 1 : ℤ)))

lemma simRel_init (x c : List Bool) :
    SimRel M 1 true (initTapeAfterPre M x c) (M.init (PvsNP.encodePair (x, c))).Tape := by
  set s : List M.Γ := (PvsNP.encodePair (x, c)).map M.inp
  have hps : initPairs M x c = s.map (fun g => (g, default)) ++
      [(default, default), (default, default), (default, default)] := by
    simp [initPairs, s, PvsNP.encodePair, Computability.encodingProd, Computability.encodingList,
      List.map_append, List.map_map, Function.comp_def]
  have hrt : initTapeAfterPre M x c =
      3 :: (s.map (fun g => pairSym M g default) ++ [blankSym M, blankSym M, blankSym M]) := by
    simp [initTapeAfterPre, hps, blankSym, List.map_map, Function.comp_def]
  have hwf : TapeWF M (initTapeAfterPre M x c) := by
    refine ⟨by simp [hrt], ?_⟩
    intro i hi hlt
    rw [hrt] at hlt ⊢
    cases i with
    | zero => omega
    | succ j =>
        simp only [List.getElem?_cons_succ]
        by_cases hj : j < s.length
        · rw [List.getElem?_append_left (by simp [hj])]
          refine ⟨s[j], default, by simp [hj]⟩
        · rw [List.getElem?_append_right (by simp; omega)]
          simp only [List.length_map]
          have hrem : j - s.length < 3 := by
            simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] at hlt; omega
          refine ⟨default, default, ?_⟩
          match hk : j - s.length with
          | 0 => rfl
          | 1 => rfl
          | 2 => rfl
          | n + 3 => omega
  have hget : ∀ j : ℕ, (initTapeAfterPre M x c).getD (j + 1) (blankSym M) =
      pairSym M (s.getD j default) default := by
    intro j
    rw [List.getD_eq_getElem?_getD, hrt]
    simp only [List.getElem?_cons_succ]
    by_cases hj : j < s.length
    · rw [List.getElem?_append_left (by simp [hj])]; simp [hj, List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map]
      have hnone : s[j]? = none := List.getElem?_eq_none (by omega)
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
      by_cases hrem : j - s.length < 3
      · have h3 : [blankSym M, blankSym M, blankSym M][j - s.length]? = some (blankSym M) := by
          match hk : j - s.length with
          | 0 => rfl
          | 1 => rfl
          | 2 => rfl
          | n + 3 => omega
        rw [h3]; rfl
      · have hnone2 : [blankSym M, blankSym M, blankSym M][j - s.length]? = none :=
          List.getElem?_eq_none (by simp; omega)
        rw [hnone2]; rfl
  have hposAt : ∀ j : ℕ, tapeAt M (initTapeAfterPre M x c) (Int.ofNat j) = s.getD j default := by
    intro j; simp only [tapeAt]; rw [hget j, decodePair_pairSym]
  have hnegAt : ∀ j : ℕ, tapeAt M (initTapeAfterPre M x c) (Int.negSucc j) = default := by
    intro j; simp only [tapeAt]; rw [hget j, decodePair_pairSym]
  have hdef_nth : ∀ i : ℕ, (default : Turing.ListBlank M.Γ).nth i = default := by
    intro i
    change (Turing.ListBlank.mk ([] : List M.Γ)).nth i = default
    rw [Turing.ListBlank.nth_mk]; simp
  have hinit_tape : (M.init (PvsNP.encodePair (x, c))).Tape = Turing.Tape.mk₁ s := rfl
  rw [hinit_tape]
  refine ⟨by omega, by simp [hrt], hwf, ?_, ?_, ?_⟩
  · change (Turing.Tape.mk₁ s).head = tapeAt M (initTapeAfterPre M x c) (Int.ofNat 0)
    rw [hposAt 0]; cases s <;> rfl
  · intro i
    rw [show headZ 1 true + (i + 1 : ℤ) = Int.ofNat (i + 1) by simp [headZ]]
    rw [hposAt (i + 1)]
    cases s with
    | nil =>
        simp only [Turing.Tape.mk₁, Turing.Tape.mk', List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none]
        exact hdef_nth i
    | cons hd tl =>
        simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk',
          List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
        have htail : (Turing.ListBlank.mk (hd :: tl)).tail.nth i = (Turing.ListBlank.mk (hd :: tl)).nth (i + 1) := by
          simp [Turing.ListBlank.nth_succ]
        rw [htail, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
        simp
  · intro i
    rw [show headZ 1 true - (i + 1 : ℤ) = Int.negSucc i by simp [headZ]; omega]
    rw [hnegAt i]
    simp only [Turing.Tape.mk₁, Turing.Tape.mk']
    exact hdef_nth i

lemma tape_write_at_head_clean (head : ℕ) (pos : Bool) (right : List ℕ) (a b w : M.Γ)
    (h1 : 1 ≤ head) (hle : head ≤ right.length) (hwf : TapeWF M right)
    (hcur_ab : decodePair M (right.getD head (blankSym M)) = (a, b)) :
    let wr := if pos then pairSym M w b else pairSym M a w
    let right' := (writeCurrentTapeSymbol ([], head, right) (some wr)).2.2
    head ≤ right'.length ∧ TapeWF M right' ∧
    (∀ z : ℤ, tapeAt M right' z = if z = headZ head pos then w else tapeAt M right z) := by
  intro wr right'
  have hcell : ∀ i : ℕ, right'[i]? = if i = head then some wr else right[i]? := by
    intro i
    by_cases hlt : head < right.length
    · have hrt' : right' = right.take head ++ wr :: right.drop (head + 1) := by
        simp [right', writeCurrentTapeSymbol, hlt]
      rw [hrt']; exact getElem?_update right head wr hlt i
    · have heq : head = right.length := by omega
      have hrt' : right' = right ++ [wr] := by simp [right', writeCurrentTapeSymbol, heq]
      rw [hrt']
      by_cases hi : i < right.length
      · rw [if_neg (by omega), List.getElem?_append_left hi]
      · by_cases hieq : i = right.length
        · subst hieq; rw [if_pos heq.symm, List.getElem?_append_right (le_refl _)]; simp
        · rw [if_neg (by omega), List.getElem?_append_right (by omega),
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  have hlen' : right'.length = if head < right.length then right.length else right.length + 1 := by
    by_cases hlt : head < right.length
    · have hrt' : right' = right.take head ++ wr :: right.drop (head + 1) := by
        simp [right', writeCurrentTapeSymbol, hlt]
      rw [if_pos hlt, hrt', length_update right head wr hlt]
    · have heq : head = right.length := by omega
      have hrt' : right' = right ++ [wr] := by simp [right', writeCurrentTapeSymbol, heq]
      rw [if_neg hlt, hrt']; simp
  refine ⟨by split_ifs at hlen' <;> omega, ?_, ?_⟩
  · refine ⟨by rw [hcell 0, if_neg (by omega)]; exact hwf.1, ?_⟩
    intro i hi hilt
    rw [hcell i]
    by_cases hieq : i = head
    · rw [if_pos hieq]; cases pos <;> [exact ⟨a, w, rfl⟩; exact ⟨w, b, rfl⟩]
    · rw [if_neg hieq]; exact hwf.2 i hi (by split_ifs at hlen' <;> omega)
  · intro z
    cases z with
    | ofNat j =>
        by_cases hj : j + 1 = head
        · have hj' : j = head - 1 := by omega
          subst hj'
          cases pos with
          | true =>
              rw [if_pos (by simp [headZ])]
              have hh : head - 1 + 1 = head := by omega
              simp only [tapeAt, List.getD_eq_getElem?_getD, hh, hcell head, ite_true, ↓reduceIte,
                Option.getD_some, wr, decodePair_pairSym]
          | false =>
              have hne : (Int.ofNat (head - 1) : ℤ) ≠ headZ head false := by simp [headZ]
              rw [if_neg hne]
              have hh : head - 1 + 1 = head := by omega
              simp only [tapeAt, List.getD_eq_getElem?_getD, hh, hcell head, if_pos rfl,
                Option.getD_some, wr, Bool.false_eq_true, ↓reduceIte, decodePair_pairSym]
              have h1' : (decodePair M (right.getD head (blankSym M))).1 = a := by rw [hcur_ab]
              rw [← h1', List.getD_eq_getElem?_getD]
        · have hne : (Int.ofNat j : ℤ) ≠ headZ head pos := by
            unfold headZ; cases pos <;> simp <;> omega
          rw [if_neg hne]
          simp only [tapeAt, List.getD_eq_getElem?_getD, hcell (j + 1), if_neg hj]
    | negSucc j =>
        by_cases hj : j + 1 = head
        · have hj' : j = head - 1 := by omega
          subst hj'
          cases pos with
          | false =>
              rw [if_pos (by simp [headZ])]
              have hh : head - 1 + 1 = head := by omega
              simp only [tapeAt, List.getD_eq_getElem?_getD, hh, hcell head, if_pos rfl,
                Option.getD_some, wr, Bool.false_eq_true, ↓reduceIte, decodePair_pairSym]
          | true =>
              have hne : Int.negSucc (head - 1) ≠ headZ head true := by simp [headZ]
              rw [if_neg hne]
              have hh : head - 1 + 1 = head := by omega
              simp only [tapeAt, List.getD_eq_getElem?_getD, hh, hcell head, ite_true, ↓reduceIte,
                Option.getD_some, wr, decodePair_pairSym]
              have h2' : (decodePair M (right.getD head (blankSym M))).2 = b := by rw [hcur_ab]
              rw [← h2', List.getD_eq_getElem?_getD]
        · have hne : Int.negSucc j ≠ headZ head pos := by
            unfold headZ; cases pos <;> simp <;> omega
          rw [if_neg hne]
          simp only [tapeAt, List.getD_eq_getElem?_getD, hcell (j + 1), if_neg hj]

lemma tape_write_noop (head : ℕ) (pos : Bool) (right : List ℕ) (a b : M.Γ)
    (h1 : 1 ≤ head) (hle : head ≤ right.length) (hwf : TapeWF M right)
    (hcur_ab : decodePair M (right.getD head (blankSym M)) = (a, b)) :
    let right' := (writeCurrentTapeSymbol ([], head, right) (some (pairSym M a b))).2.2
    head < right'.length ∧ TapeWF M right' ∧
    (∀ z : ℤ, tapeAt M right' z = tapeAt M right z) := by
  have h := tape_write_at_head_clean M head pos right a b (if pos then a else b) h1 hle hwf hcur_ab
  have hwr_eq : (if pos then pairSym M (if pos then a else b) b else pairSym M a (if pos then a else b)) =
      pairSym M a b := by cases pos <;> rfl
  rw [hwr_eq] at h
  have hlen' : (writeCurrentTapeSymbol ([], head, right) (some (pairSym M a b))).2.2.length =
      if head < right.length then right.length else right.length + 1 := by
    by_cases hlt : head < right.length
    · rw [if_pos hlt, writeCurrentTapeSymbol_some_lt _ _ _ hlt, length_update _ _ _ hlt]
    · have heq : head = right.length := by omega
      rw [if_neg hlt, heq, writeCurrentTapeSymbol_some_eq]; simp
  refine ⟨by split_ifs at hlen' <;> omega, h.2.1, ?_⟩
  intro z; rw [h.2.2 z]
  by_cases hz : z = headZ head pos
  · rw [if_pos hz]; subst hz
    have hh : head - 1 + 1 = head := by omega
    cases pos with
    | true =>
        simp only [headZ, ↓reduceIte, tapeAt, hh]
        rw [hcur_ab]
    | false =>
        simp only [headZ, Bool.false_eq_true, ↓reduceIte, tapeAt, hh]
        rw [hcur_ab]
  · rw [if_neg hz]

lemma writeCurrentTapeSymbol_shape (head : ℕ) (right : List ℕ) (s : Option ℕ) :
    writeCurrentTapeSymbol ([], head, right) s = ([], head, (writeCurrentTapeSymbol ([], head, right) s).2.2) := by
  cases s with
  | none => rfl
  | some v =>
      unfold writeCurrentTapeSymbol; dsimp only
      split_ifs <;> rfl

lemma sim_one_step {q q' : M.Λ} {t t' : Turing.Tape M.Γ} {head : ℕ} {pos : Bool} {right : List ℕ}
    (hrel : SimRel M head pos right t)
    (hstep : M.step ⟨q, t⟩ = some ⟨q', t'⟩) :
    ∃ (k : ℕ) (head' : ℕ) (pos' : Bool) (right' : List ℕ),
      k ≤ 2 ∧
      runFlatTM k (simFlatTM M) ⟨stSim M q pos, [([], head, right)]⟩ =
        some ⟨stSim M q' pos', [([], head', right')]⟩ ∧
      SimRel M head' pos' right' t' := by
  obtain ⟨h1, hle, hwf, hhead, hright, hleft⟩ := hrel
  have hcell_ex : ∃ cell : Option (M.Γ × M.Γ),
      currentTapeSymbol ([], head, right) = cell.map (fun p => pairSym M p.1 p.2) ∧
      decodePair M (right.getD head (blankSym M)) = cell.getD (default, default) := by
    by_cases hlt : head < right.length
    · obtain ⟨a, b, hab⟩ := hwf.2 head h1 hlt
      refine ⟨some (a, b), ?_, ?_⟩
      · unfold currentTapeSymbol; rw [dif_pos hlt]
        have := List.getElem?_eq_getElem hlt; rw [hab] at this
        exact congrArg some (Option.some.inj this).symm
      · simp [List.getD_eq_getElem?_getD, hab, decodePair_pairSym]
    · refine ⟨none, ?_, ?_⟩
      · unfold currentTapeSymbol; rw [dif_neg hlt]; rfl
      · have hnone : right[head]? = none := List.getElem?_eq_none (by omega)
        simp [List.getD_eq_getElem?_getD, hnone, blankSym, decodePair_pairSym]
  rcases hcell_ex with ⟨cell, hcur_sym, hcur_ab⟩
  let ab := cell.getD (default, default)
  have hsym_eq : t.head = if pos then ab.1 else ab.2 := by
    rw [hhead]
    cases pos with
    | true => simp only [headZ, ↓reduceIte, tapeAt, show head - 1 + 1 = head by omega]; rw [hcur_ab]
    | false => simp only [headZ, Bool.false_eq_true, ↓reduceIte, tapeAt, show head - 1 + 1 = head by omega]; rw [hcur_ab]
  have hδ : ∃ stmt : Turing.TM0.Stmt M.Γ, M.δ q t.head = some (q', stmt) ∧
      t' = match stmt with | .move d => t.move d | .write w => t.write w := by
    dsimp only [PvsNP.SingleTape.Machine.step, Turing.TM0.step] at hstep
    cases h : M.δ q t.head with
    | none => rw [h] at hstep; cases hstep
    | some p =>
        rw [h] at hstep; rcases p with ⟨q'', stmt⟩
        cases stmt with
        | move d =>
            simp only [Option.map_some, Option.some.injEq, Turing.TM0.Cfg.mk.injEq] at hstep
            rcases hstep with ⟨rfl, rfl⟩; exact ⟨.move d, rfl, rfl⟩
        | write w =>
            simp only [Option.map_some, Option.some.injEq, Turing.TM0.Cfg.mk.injEq] at hstep
            rcases hstep with ⟨rfl, rfl⟩; exact ⟨.write w, rfl, rfl⟩
  rcases hδ with ⟨stmt, hδ_eq, rfl⟩
  have hmem_e : simEntry M q pos cell ∈ (simFlatTM M).trans := by
    simp only [simFlatTM, List.mem_append, simTrans, List.mem_flatMap]
    left; right
    refine ⟨q, mem_allΛ M q, pos, by cases pos <;> simp, ?_⟩
    cases cell with
    | none => exact List.mem_cons_self ..
    | some p => apply List.mem_cons_of_mem; rw [List.mem_map]; exact ⟨p, mem_allPairs M p.1 p.2, rfl⟩
  have hnh_sim : stSim M q pos ≠ stAcc ∧ stSim M q pos ≠ stRej := by
    unfold stSim stAcc stRej; cases pos <;> simp <;> omega
  cases stmt with
  | write w =>
      let wr := if pos then pairSym M w ab.2 else pairSym M ab.1 w
      have he_eq : simEntry M q pos cell =
          mk1 (stSim M q pos) (cell.map (fun p => pairSym M p.1 p.2)) (stSim M q' pos) (some wr) .Nmove := by
        unfold simEntry
        have hδ' : M.δ q (if pos then ab.1 else ab.2) = some (q', .write w) := by rw [← hsym_eq]; exact hδ_eq
        simp [ab, hδ', wr]
      rw [he_eq] at hmem_e
      have hrun1 := step_mk1 M _ _ head right _ _ _ hmem_e hcur_sym hnh_sim.1 hnh_sim.2
      let right' := (writeCurrentTapeSymbol ([], head, right) (some wr)).2.2
      have htap := tape_write_at_head_clean M head pos right ab.1 ab.2 w h1 hle hwf hcur_ab
      have hsh : tapeStep ([], head, right) (some wr) .Nmove = ([], head, right') := by
        unfold tapeStep moveTapeHead; exact writeCurrentTapeSymbol_shape head right (some wr)
      rw [hsh] at hrun1
      refine ⟨1, head, pos, right', by omega, hrun1, ?_⟩
      refine ⟨h1, htap.1, htap.2.1, ?_, ?_, ?_⟩
      · simp only [Turing.Tape.write]; rw [htap.2.2, if_pos rfl]
      · intro i; simp only [Turing.Tape.write]; rw [htap.2.2, if_neg (by omega)]; exact hright i
      · intro i; simp only [Turing.Tape.write]; rw [htap.2.2, if_neg (by omega)]; exact hleft i
  | move dir =>
      have hδ' : M.δ q (if pos then ab.1 else ab.2) = some (q', .move dir) := by rw [← hsym_eq]; exact hδ_eq
      have hnoop := tape_write_noop M head pos right ab.1 ab.2 h1 hle hwf hcur_ab
      let right' := (writeCurrentTapeSymbol ([], head, right) (some (pairSym M ab.1 ab.2))).2.2
      have hlt' : head < right'.length := hnoop.1
      have hwf' : TapeWF M right' := hnoop.2.1
      have hat' : ∀ z, tapeAt M right' z = tapeAt M right z := hnoop.2.2
      have hmove_rel : ∀ (dir' : Turing.Dir) (head' : ℕ) (pos' : Bool),
          1 ≤ head' → head' ≤ right'.length →
          headZ head' pos' = headZ head pos + (match dir' with | .right => 1 | .left => -1) →
          SimRel M head' pos' right' (t.move dir') := by
        intro dir' head' pos' h1' hle' hz'
        cases dir' with
        | right =>
            dsimp only at hz'
            refine ⟨h1', hle', hwf', ?_, ?_, ?_⟩
            · have : (t.move .right).head = t.right.nth 0 := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_zero]
              rw [this, hright 0, hat', hz']
              congr 1
            · intro i
              have : (t.move .right).right.nth i = t.right.nth (i + 1) := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_succ]
              rw [this, hright (i + 1), hat', hz']; congr 1; omega
            · intro i
              cases i with
              | zero =>
                  have : (t.move .right).left.nth 0 = t.head := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_zero]
                  rw [this, hhead, hat', hz']; congr 1; omega
              | succ j =>
                  have : (t.move .right).left.nth (j + 1) = t.left.nth j := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_succ]
                  rw [this, hleft j, hat', hz']; congr 1; omega
        | left =>
            dsimp only at hz'
            refine ⟨h1', hle', hwf', ?_, ?_, ?_⟩
            · have : (t.move .left).head = t.left.nth 0 := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_zero]
              rw [this, hleft 0, hat', hz']
              congr 1
            · intro i
              cases i with
              | zero =>
                  have : (t.move .left).right.nth 0 = t.head := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_zero]
                  rw [this, hhead, hat', hz']; congr 1; omega
              | succ j =>
                  have : (t.move .left).right.nth (j + 1) = t.right.nth j := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_succ]
                  rw [this, hright j, hat', hz']; congr 1; omega
            · intro i
              have : (t.move .left).left.nth i = t.left.nth (i + 1) := by cases t; simp [Turing.Tape.move, Turing.ListBlank.nth_succ]
              rw [this, hleft (i + 1), hat', hz']; congr 1; omega
      by_cases hout : ((pos && (dir == Turing.Dir.right)) || ((!pos) && (dir == Turing.Dir.left))) = true
      · have he_eq : simEntry M q pos cell =
            mk1 (stSim M q pos) (cell.map (fun p => pairSym M p.1 p.2))
              (stSim M q' pos) (some (pairSym M ab.1 ab.2)) .Rmove := by
          unfold simEntry; simp [ab, hδ', hout]
        rw [he_eq] at hmem_e
        have hrun1 := step_mk1 M _ _ head right _ _ _ hmem_e hcur_sym hnh_sim.1 hnh_sim.2
        have hsh : tapeStep ([], head, right) (some (pairSym M ab.1 ab.2)) .Rmove = ([], head + 1, right') := by
          unfold tapeStep; rw [writeCurrentTapeSymbol_shape]; rfl
        rw [hsh] at hrun1
        refine ⟨1, head + 1, pos, right', by omega, hrun1, ?_⟩
        apply hmove_rel dir (head + 1) pos (by omega) (by omega)
        cases pos <;> cases dir <;> simp [headZ, Int.negSucc_eq] at hout ⊢ <;> omega
      · have hout_f : ((pos && (dir == Turing.Dir.right)) || ((!pos) && (dir == Turing.Dir.left))) = false := by
          cases hv : ((pos && (dir == Turing.Dir.right)) || ((!pos) && (dir == Turing.Dir.left))) <;> simp_all
        have he_eq : simEntry M q pos cell =
            mk1 (stSim M q pos) (cell.map (fun p => pairSym M p.1 p.2))
              (stBounce M q' pos) (some (pairSym M ab.1 ab.2)) .Lmove := by
          unfold simEntry; simp [ab, hδ', hout_f]
        rw [he_eq] at hmem_e
        have hrun1 := step_mk1 M _ _ head right _ _ _ hmem_e hcur_sym hnh_sim.1 hnh_sim.2
        have hsh : tapeStep ([], head, right) (some (pairSym M ab.1 ab.2)) .Lmove = ([], head - 1, right') := by
          unfold tapeStep; rw [writeCurrentTapeSymbol_shape]; rfl
        rw [hsh] at hrun1
        have hnh_bn : stBounce M q' pos ≠ stAcc ∧ stBounce M q' pos ≠ stRej := by
          unfold stBounce stAcc stRej; cases pos <;> simp <;> omega
        by_cases hhead1 : head = 1
        · subst hhead1
          have hmem_bn : mk1 (stBounce M q' pos) (some 3) (stSim M q' (!pos)) none .Rmove ∈ (simFlatTM M).trans := by
            simp only [simFlatTM, List.mem_append, bounceTrans, List.mem_flatMap]
            right; refine ⟨q', mem_allΛ M q', pos, by cases pos <;> simp, List.mem_cons_self ..⟩
          have hcur0 : currentTapeSymbol ([], 0, right') = some 3 := by
            unfold currentTapeSymbol
            have h0lt : 0 < right'.length := by omega
            rw [dif_pos h0lt]
            have := List.getElem?_eq_getElem h0lt; rw [hwf'.1] at this
            exact congrArg some (Option.some.inj this).symm
          have hrun2 := step_mk1 M _ _ 0 right' _ _ _ hmem_bn hcur0 hnh_bn.1 hnh_bn.2
          have hcomp := runFlatTM_compose (simFlatTM M) 1 1 _ _ hrun1
          change runFlatTM 2 (simFlatTM M) ⟨stSim M q pos, [([], 1, right)]⟩ = _ at hcomp
          rw [hrun2] at hcomp
          refine ⟨2, 1, !pos, right', by omega, by simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead] using hcomp, ?_⟩
          apply hmove_rel dir 1 (!pos) (by omega) (by omega)
          cases pos <;> cases dir <;> simp [headZ, Int.negSucc_eq] at hout_f ⊢
        · have hm1_ge1 : 1 ≤ head - 1 := by omega
          have hm1_lt : head - 1 < right'.length := by omega
          obtain ⟨a', b', hab'⟩ := hwf'.2 (head - 1) hm1_ge1 hm1_lt
          have hmem_bn : mk1 (stBounce M q' pos) (some (pairSym M a' b')) (stSim M q' pos) none .Nmove ∈
              (simFlatTM M).trans := by
            simp only [simFlatTM, List.mem_append, bounceTrans, List.mem_flatMap]
            right; refine ⟨q', mem_allΛ M q', pos, by cases pos <;> simp, ?_⟩
            apply List.mem_cons_of_mem; rw [List.mem_map]; exact ⟨(a', b'), mem_allPairs M a' b', rfl⟩
          have hcur_m1 : currentTapeSymbol ([], head - 1, right') = some (pairSym M a' b') := by
            unfold currentTapeSymbol; rw [dif_pos hm1_lt]
            have := List.getElem?_eq_getElem hm1_lt; rw [hab'] at this
            exact congrArg some (Option.some.inj this).symm
          have hrun2 := step_mk1 M _ _ (head - 1) right' _ _ _ hmem_bn hcur_m1 hnh_bn.1 hnh_bn.2
          have hcomp := runFlatTM_compose (simFlatTM M) 1 1 _ _ hrun1
          change runFlatTM 2 (simFlatTM M) ⟨stSim M q pos, [([], head, right)]⟩ = _ at hcomp
          rw [hrun2] at hcomp
          refine ⟨2, head - 1, pos, right', by omega, by simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead] using hcomp, ?_⟩
          apply hmove_rel dir (head - 1) pos hm1_ge1 (by omega)
          cases pos <;> cases dir <;> simp [headZ, Int.negSucc_eq] at hout_f ⊢ <;> omega

lemma sim_halt_step {q : M.Λ} {t : Turing.Tape M.Γ} {head : ℕ} {pos : Bool} {right : List ℕ}
    (hrel : SimRel M head pos right t)
    (hhalt : M.step ⟨q, t⟩ = none) :
    ∃ cfg : FlatTMConfig,
      runFlatTM 1 (simFlatTM M) ⟨stSim M q pos, [([], head, right)]⟩ = some cfg ∧
      haltingStateReached (simFlatTM M) cfg = true ∧
      cfg.state_idx = if @decide (t.head = M.out true) (Classical.propDecidable _) then stAcc else stRej := by
  obtain ⟨h1, hle, hwf, hhead, _, _⟩ := hrel
  have hcell_ex : ∃ cell : Option (M.Γ × M.Γ),
      currentTapeSymbol ([], head, right) = cell.map (fun p => pairSym M p.1 p.2) ∧
      decodePair M (right.getD head (blankSym M)) = cell.getD (default, default) := by
    by_cases hlt : head < right.length
    · obtain ⟨a, b, hab⟩ := hwf.2 head h1 hlt
      refine ⟨some (a, b), ?_, ?_⟩
      · unfold currentTapeSymbol; rw [dif_pos hlt]
        have := List.getElem?_eq_getElem hlt; rw [hab] at this
        exact congrArg some (Option.some.inj this).symm
      · simp [List.getD_eq_getElem?_getD, hab, decodePair_pairSym]
    · refine ⟨none, ?_, ?_⟩
      · unfold currentTapeSymbol; rw [dif_neg hlt]; rfl
      · have hnone : right[head]? = none := List.getElem?_eq_none (by omega)
        simp [List.getD_eq_getElem?_getD, hnone, blankSym, decodePair_pairSym]
  rcases hcell_ex with ⟨cell, hcur_sym, hcur_ab⟩
  let ab := cell.getD (default, default)
  have hsym_eq : t.head = if pos then ab.1 else ab.2 := by
    rw [hhead]
    cases pos with
    | true => simp only [headZ, ↓reduceIte, tapeAt, show head - 1 + 1 = head by omega]; rw [hcur_ab]
    | false => simp only [headZ, Bool.false_eq_true, ↓reduceIte, tapeAt, show head - 1 + 1 = head by omega]; rw [hcur_ab]
  have hδ_none : M.δ q t.head = none := by
    dsimp only [PvsNP.SingleTape.Machine.step, Turing.TM0.step] at hhalt
    cases h : M.δ q t.head with
    | none => rfl
    | some p => rw [h] at hhalt; rcases p with ⟨q', stmt⟩; cases stmt <;> simp at hhalt
  have hmem_e : simEntry M q pos cell ∈ (simFlatTM M).trans := by
    simp only [simFlatTM, List.mem_append, simTrans, List.mem_flatMap]
    left; right
    refine ⟨q, mem_allΛ M q, pos, by cases pos <;> simp, ?_⟩
    cases cell with
    | none => exact List.mem_cons_self ..
    | some p => apply List.mem_cons_of_mem; rw [List.mem_map]; exact ⟨p, mem_allPairs M p.1 p.2, rfl⟩
  let dst := if @decide (t.head = M.out true) (Classical.propDecidable _) then stAcc else stRej
  have he_eq : simEntry M q pos cell =
      mk1 (stSim M q pos) (cell.map (fun p => pairSym M p.1 p.2)) dst none .Nmove := by
    dsimp only [simEntry]
    rw [show (if pos then (cell.getD (default, default)).1 else (cell.getD (default, default)).2) = t.head from hsym_eq.symm]
    rw [hδ_none]
  rw [he_eq] at hmem_e
  have hnh_sim : stSim M q pos ≠ stAcc ∧ stSim M q pos ≠ stRej := by
    unfold stSim stAcc stRej; cases pos <;> simp <;> omega
  have hrun1 := step_mk1 M _ _ head right _ _ _ hmem_e hcur_sym hnh_sim.1 hnh_sim.2
  refine ⟨⟨dst, [tapeStep ([], head, right) none .Nmove]⟩, hrun1, ?_, rfl⟩
  rw [halting_iff]; dsimp only [dst]; split_ifs <;> simp

lemma sim_iter {n : ℕ} {c₀ c_end : M.Cfg}
    (hiter : (flip bind M.step)^[n] (some c₀) = some c_end)
    {head : ℕ} {pos : Bool} {right : List ℕ}
    (hrel : SimRel M head pos right c₀.Tape) :
    ∃ (k : ℕ) (head' : ℕ) (pos' : Bool) (right' : List ℕ),
      k ≤ 2 * n ∧
      runFlatTM k (simFlatTM M) ⟨stSim M c₀.q pos, [([], head, right)]⟩ =
        some ⟨stSim M c_end.q pos', [([], head', right')]⟩ ∧
      SimRel M head' pos' right' c_end.Tape := by
  induction n generalizing c_end with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at hiter
      subst hiter
      exact ⟨0, head, pos, right, by omega, rfl, hrel⟩
  | succ m ih =>
      rw [Function.iterate_succ_apply'] at hiter
      cases hprev : (flip bind M.step)^[m] (some c₀) with
      | none =>
          rw [hprev] at hiter
          simp [flip] at hiter
      | some cm =>
          rw [hprev] at hiter
          have hstep : M.step cm = some c_end := by simpa [flip] using hiter
          obtain ⟨k₁, hd₁, p₁, rt₁, hk₁, hr₁, hrel₁⟩ := ih hprev
          rcases cm with ⟨qm, tm⟩
          rcases c_end with ⟨qe, te⟩
          obtain ⟨k₂, hd₂, p₂, rt₂, hk₂, hr₂, hrel₂⟩ := sim_one_step M hrel₁ hstep
          refine ⟨k₁ + k₂, hd₂, p₂, rt₂, by omega, ?_, hrel₂⟩
          rw [runFlatTM_compose (simFlatTM M) k₁ k₂ _ _ hr₁, hr₂]

lemma simFlatTM_decides_pair {V : List Bool × List Bool → Bool} {T : ℕ} {x c : List Bool}
    (hM : M.OutputsInTime (PvsNP.encodePair (x, c)) (PvsNP.encodeAnswer (V (x, c))) T) :
    ∃ (k : ℕ) (cfg : FlatTMConfig),
      k ≤ 2 * x.length + 4 * c.length + 8 + 2 * T ∧
      runFlatTM k (simFlatTM M) (initFlatConfig (simFlatTM M) [pairTape x c]) = some cfg ∧
      haltingStateReached (simFlatTM M) cfg = true ∧
      cfg.state_idx = if V (x, c) then stAcc else stRej := by
  rcases hM with ⟨c_end, ⟨heval⟩, hhalt, hshows⟩
  have hpre := run_preprocess M x c
  have hrel0 := simRel_init M x c
  have hq0 : (M.init (PvsNP.encodePair (x, c))).q = default := rfl
  obtain ⟨k₁, hd₁, p₁, rt₁, hk₁, hr₁, hrel₁⟩ := sim_iter M heval.toEvalsTo.evals_in_steps hrel0
  rw [hq0] at hr₁
  rcases c_end with ⟨qe, te⟩
  obtain ⟨cfg, hr₂, hcfghalt, hcfgst⟩ := sim_halt_step M hrel₁ hhalt
  have hhead_eq : te.head = M.out (V (x, c)) := by
    have h0 := hshows.1 0 (by simp [PvsNP.encodeAnswer, Computability.encodeBool])
    simpa [Turing.Tape.right₀, Turing.ListBlank.nth_zero, PvsNP.encodeAnswer, Computability.encodeBool] using h0
  have hdec : (@decide (te.head = M.out true) (Classical.propDecidable _)) = V (x, c) := by
    rw [hhead_eq]
    cases hv : V (x, c) with
    | true => simp
    | false =>
        have hne : M.out false ≠ M.out true := fun h => by
          have := M.out_injective h; cases this
        simp [hne]
  rw [hdec] at hcfgst
  refine ⟨(2 * x.length + 4 * c.length + 7) + k₁ + 1, cfg, ?_, ?_, hcfghalt, hcfgst⟩
  · have := heval.steps_le_m; omega
  · have h12 := runFlatTM_compose (simFlatTM M) (2 * x.length + 4 * c.length + 7) k₁ _ _ hpre
    rw [hr₁] at h12
    have h123 := runFlatTM_compose (simFlatTM M) (2 * x.length + 4 * c.length + 7 + k₁) 1 _ _ h12
    rw [hr₂] at h123
    exact h123

end Sim

/-! ## Part 2: Polynomial Length-Check FlatTM (`c.length ≤ p.eval x.length`) -/

section LenCheck

def sigL (d : ℕ) : ℕ := 6 + 2 * 2 ^ d

def xSym (b : Bool) (m : ℕ) : ℕ :=
  if m = 0 then (if b then 2 else 1) else 6 + 2 * (m - 1) + (if b then 1 else 0)

def cMark (b : Bool) : ℕ := if b then 5 else 4
def cUnmark (b : Bool) : ℕ := if b then 2 else 1

lemma xSym_lt {b : Bool} {m d : ℕ} (hm : m < 2 ^ d) : xSym b m < sigL d := by
  unfold xSym sigL
  split_ifs <;> cases b <;> omega

lemma xSym_ne_0345 (b : Bool) (m : ℕ) :
    xSym b m ≠ 0 ∧ xSym b m ≠ 3 ∧ xSym b m ≠ 4 ∧ xSym b m ≠ 5 := by
  unfold xSym; split_ifs <;> cases b <;> omega

lemma xSym_inj {b₁ b₂ : Bool} {m₁ m₂ : ℕ} (h : xSym b₁ m₁ = xSym b₂ m₂) :
    b₁ = b₂ ∧ m₁ = m₂ := by
  by_cases h1 : m₁ = 0 <;> by_cases h2 : m₂ = 0 <;>
    simp [xSym, h1, h2] at h <;> cases b₁ <;> cases b₂ <;> simp at h ⊢ <;> omega

lemma xSym_zero (b : Bool) : xSym b 0 = if b then 2 else 1 := rfl

def lenTape (xs : List (Bool × ℕ)) (u : ℕ) (c : List Bool) : List ℕ :=
  3 :: (xs.map (fun bm => xSym bm.1 bm.2) ++ [0] ++ (c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3])

lemma lenTape_init (x c : List Bool) :
    lenTape (x.map (fun b => (b, 0))) 0 c = pairTape x c := by
  simp [lenTape, pairTape, symbolsOf, xSym_zero, cUnmark, List.map_map, Function.comp_def]

def MaskOK (d lvl : ℕ) (xs : List (Bool × ℕ)) : Prop :=
  ∀ bm ∈ xs, bm.2 < 2 ^ d ∧ ∀ j < lvl, (bm.2 / 2 ^ j) % 2 = 0

lemma MaskOK.mono {d lvl₁ lvl₂ : ℕ} (h : lvl₁ ≤ lvl₂) {xs : List (Bool × ℕ)}
    (hok : MaskOK d lvl₂ xs) : MaskOK d lvl₁ xs :=
  fun bm hbm => ⟨(hok bm hbm).1, fun j hj => (hok bm hbm).2 j (lt_of_lt_of_le hj h)⟩

def allXSyms (d : ℕ) : List (Bool × ℕ) :=
  (List.range (2 ^ d)).flatMap (fun m => [(false, m), (true, m)])

lemma mem_allXSyms {d : ℕ} {b : Bool} {m : ℕ} (hm : m < 2 ^ d) :
    (b, m) ∈ allXSyms d := by
  unfold allXSyms; rw [List.mem_flatMap]
  refine ⟨m, List.mem_range.mpr hm, ?_⟩
  cases b <;> simp

lemma allXSyms_bound {d : ℕ} {bm : Bool × ℕ} (h : bm ∈ allXSyms d) : bm.2 < 2 ^ d := by
  unfold allXSyms at h; rw [List.mem_flatMap] at h
  rcases h with ⟨m, hm, hmem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> exact List.mem_range.mp hm

/-- Specification of a single-tape counter FlatTM adding `K |xs|` marks to `c` (capped at `|c|`). -/
structure CounterSpec (d lvl : ℕ) (K : ℕ → ℕ) (T : ℕ → ℕ → ℕ) where
  M : FlatTM
  exit : ℕ
  hSig : M.sig = sigL d
  hTapes : M.tapes = 1
  hValid : validFlatTM M
  hExitLt : exit < M.states
  hNoExitTrans : ∀ e ∈ M.trans, e.src_state ≠ exit
  hHaltIff : ∀ cfg, haltingStateReached M cfg = true ↔ cfg.state_idx = exit
  hRun : ∀ (xs : List (Bool × ℕ)) (u : ℕ) (c : List Bool),
    MaskOK d lvl xs → u ≤ c.length →
    ∃ t ≤ T xs.length c.length,
      ExactRun M ⟨M.start, [([], 0, lenTape xs u c)]⟩
        ⟨exit, [([], 0, lenTape xs (min (u + K xs.length) c.length) c)]⟩ t

def CounterSpec.mono {d lvl₁ lvl₂ K T} (h : lvl₁ ≤ lvl₂) (C : CounterSpec d lvl₁ K T) :
    CounterSpec d lvl₂ K T :=
  { C with hRun := fun xs u c hok hu => C.hRun xs u c (hok.mono h) hu }

/-! ### 2a. `noopCounter`: adds 0 marks in 0 steps -/

def noopCounter (d lvl : ℕ) : CounterSpec d lvl (fun _ => 0) (fun _ _ => 0) where
  M := { sig := sigL d, tapes := 1, states := 1, trans := [], start := 0, halt := [true] }
  exit := 0
  hSig := rfl
  hTapes := rfl
  hValid := ⟨by simp, rfl, fun _ h => by cases h⟩
  hExitLt := by simp
  hNoExitTrans := fun _ h => by cases h
  hHaltIff := fun cfg => by
    unfold haltingStateReached
    cases h : cfg.state_idx with
    | zero => simp
    | succ n => simp
  hRun := fun xs u c _ hu => by
    refine ⟨0, by omega, ?_⟩
    have hmin : min (u + 0) c.length = u := by omega
    rw [hmin]
    exact ExactRun.zero _ _

/-! ### 2b. `markOneC`: adds 1 mark to `c` in `≤ 2*(|x|+|c|) + 6` steps -/

def markOneTM (d : ℕ) : FlatTM where
  sig := sigL d
  tapes := 1
  states := 5
  trans :=
    [ mk1 0 (some 3) 1 none .Rmove
    , mk1 1 (some 0) 2 none .Rmove
    , mk1 2 (some 4) 2 none .Rmove
    , mk1 2 (some 5) 2 none .Rmove
    , mk1 2 (some 1) 3 (some 4) .Lmove
    , mk1 2 (some 2) 3 (some 5) .Lmove
    , mk1 2 (some 0) 3 none .Lmove
    , mk1 3 (some 0) 3 none .Lmove
    , mk1 3 (some 4) 3 none .Lmove
    , mk1 3 (some 5) 3 none .Lmove
    , mk1 3 (some 3) 4 none .Nmove
    ] ++
    (allXSyms d).map (fun bm => mk1 1 (some (xSym bm.1 bm.2)) 1 none .Rmove) ++
    (allXSyms d).map (fun bm => mk1 3 (some (xSym bm.1 bm.2)) 3 none .Lmove)
  start := 0
  halt := [false, false, false, false, true]

lemma markOneTM_valid (d : ℕ) : validFlatTM (markOneTM d) := by
  have h6 : 6 ≤ sigL d := by unfold sigL; omega
  have hmk : ∀ s rd dst wr mv, s < 5 → dst < 5 →
      (match rd with | none => True | some v => v < sigL d) →
      (match wr with | none => True | some v => v < sigL d) →
      flatTMTransEntryValid (markOneTM d) (mk1 s rd dst wr mv) := by
    intro s rd dst wr mv hs hd hrd hwr
    refine ⟨hs, hd, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hrd
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hwr
  refine ⟨by simp [markOneTM], rfl, ?_⟩
  intro e he
  simp only [markOneTM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at he
  rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨bm, hbm, rfl⟩) | ⟨bm, hbm, rfl⟩
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm)) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm)) trivial

lemma markOneTM_key_unique (d : ℕ) {e₁ e₂ : FlatTMTransEntry}
    (h₁ : e₁ ∈ (markOneTM d).trans) (h₂ : e₂ ∈ (markOneTM d).trans)
    (hs : e₁.src_state = e₂.src_state) (ht : e₁.src_tape_vals = e₂.src_tape_vals) :
    e₁ = e₂ := by
  simp only [markOneTM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at h₁ h₂
  rcases h₁ with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨bm₁, _, rfl⟩) | ⟨bm₁, _, rfl⟩ <;>
  rcases h₂ with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨bm₂, _, rfl⟩) | ⟨bm₂, _, rfl⟩ <;>
  simp [mk1] at hs ht ⊢
  all_goals try (have := xSym_ne_0345 bm₁.1 bm₁.2; omega)
  all_goals try (have := xSym_ne_0345 bm₂.1 bm₂.2; omega)
  all_goals try (rw [ht])

lemma markOneTM_step (d st dst head : ℕ) (right : List ℕ) (rd wr : Option ℕ) (mv : TMMove)
    (hmem : mk1 st rd dst wr mv ∈ (markOneTM d).trans)
    (hrd : currentTapeSymbol ([], head, right) = rd)
    (hnh : st ≠ 4) :
    ExactRun (markOneTM d) ⟨st, [([], head, right)]⟩ ⟨dst, [tapeStep ([], head, right) wr mv]⟩ 1 := by
  have hhalt_f : haltingStateReached (markOneTM d) ⟨st, [([], head, right)]⟩ = false := by
    unfold haltingStateReached markOneTM
    match st with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => exact absurd rfl hnh
    | n + 5 => rfl
  apply ExactRun.step1 _ _ _ hhalt_f
  rw [stepFlatTM_of_unique (markOneTM d) (mk1 st rd dst wr mv) _ hmem
      (by simp [entryMatchesConfig, mk1, hrd])]
  · simp [applyTransitionEntry, mk1]
  · intro e' he' hm
    simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    exact markOneTM_key_unique d he' hmem hm.1 (hm.2.trans (by simp [mk1, hrd]))

lemma markOneTM_scanX (d : ℕ) (xs : List (Bool × ℕ)) (pre suf : List ℕ)
    (hxs : ∀ bm ∈ xs, bm.2 < 2 ^ d) :
    ExactRun (markOneTM d)
      ⟨1, [([], pre.length, pre ++ xs.map (fun bm => xSym bm.1 bm.2) ++ suf)]⟩
      ⟨1, [([], (pre ++ xs.map (fun bm => xSym bm.1 bm.2)).length,
        pre ++ xs.map (fun bm => xSym bm.1 bm.2) ++ suf)]⟩
      xs.length := by
  induction xs generalizing pre with
  | nil => simp; exact ExactRun.zero _ _
  | cons bm tl ih =>
      have hlen : (bm :: tl).length = 1 + tl.length := by simp; omega
      rw [hlen]
      have hbm : bm.2 < 2 ^ d := hxs bm (List.mem_cons_self ..)
      have hmem : mk1 1 (some (xSym bm.1 bm.2)) 1 none .Rmove ∈ (markOneTM d).trans := by
        simp only [markOneTM, List.mem_append, List.mem_map]
        left; right; exact ⟨bm, mem_allXSyms hbm, rfl⟩
      have hcfg : pre ++ (bm :: tl).map (fun p => xSym p.1 p.2) ++ suf =
          pre ++ xSym bm.1 bm.2 :: (tl.map (fun p => xSym p.1 p.2) ++ suf) := by simp
      have h1 : ExactRun (markOneTM d)
          ⟨1, [([], pre.length, pre ++ (bm :: tl).map (fun p => xSym p.1 p.2) ++ suf)]⟩
          ⟨1, [([], (pre ++ [xSym bm.1 bm.2]).length,
            (pre ++ [xSym bm.1 bm.2]) ++ tl.map (fun p => xSym p.1 p.2) ++ suf)]⟩ 1 := by
        rw [hcfg]
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
          markOneTM_step d 1 1 pre.length _ _ none .Rmove hmem (currentTapeSymbol_at pre _ _) (by omega)
      have h2 := ih (pre ++ [xSym bm.1 bm.2]) (fun p hp => hxs p (List.mem_cons_of_mem bm hp))
      simpa [List.append_assoc] using h1.trans h2

lemma markOneTM_scanMark (d : ℕ) (cs : List Bool) (pre suf : List ℕ) :
    ExactRun (markOneTM d)
      ⟨2, [([], pre.length, pre ++ cs.map cMark ++ suf)]⟩
      ⟨2, [([], (pre ++ cs.map cMark).length, pre ++ cs.map cMark ++ suf)]⟩
      cs.length := by
  induction cs generalizing pre with
  | nil => simp; exact ExactRun.zero _ _
  | cons b tl ih =>
      have hlen : (b :: tl).length = 1 + tl.length := by simp; omega
      rw [hlen]
      have h1 : ExactRun (markOneTM d)
          ⟨2, [([], pre.length, pre ++ (b :: tl).map cMark ++ suf)]⟩
          ⟨2, [([], (pre ++ [cMark b]).length, (pre ++ [cMark b]) ++ tl.map cMark ++ suf)]⟩ 1 := by
        cases b with
        | false =>
            have hmem : mk1 2 (some 4) 2 none .Rmove ∈ (markOneTM d).trans := by simp [markOneTM]
            have hcfg : pre ++ (false :: tl).map cMark ++ suf = pre ++ 4 :: (tl.map cMark ++ suf) := by
              simp [cMark]
            rw [hcfg]
            simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, cMark, List.append_assoc] using
              markOneTM_step d 2 2 pre.length _ _ none .Rmove hmem (currentTapeSymbol_at pre 4 _) (by omega)
        | true =>
            have hmem : mk1 2 (some 5) 2 none .Rmove ∈ (markOneTM d).trans := by simp [markOneTM]
            have hcfg : pre ++ (true :: tl).map cMark ++ suf = pre ++ 5 :: (tl.map cMark ++ suf) := by
              simp [cMark]
            rw [hcfg]
            simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, cMark, List.append_assoc] using
              markOneTM_step d 2 2 pre.length _ _ none .Rmove hmem (currentTapeSymbol_at pre 5 _) (by omega)
      simpa [List.append_assoc] using h1.trans (ih (pre ++ [cMark b]))

lemma markOneTM_rewind (d : ℕ) (mid suf : List ℕ)
    (hmid : ∀ s ∈ mid, s = 0 ∨ s = 4 ∨ s = 5 ∨ ∃ b m, m < 2 ^ d ∧ s = xSym b m) :
    ExactRun (markOneTM d)
      ⟨3, [([], mid.length, 3 :: (mid ++ suf))]⟩
      ⟨3, [([], 0, 3 :: (mid ++ suf))]⟩
      mid.length := by
  induction mid using List.reverseRecOn generalizing suf with
  | nil => simp; exact ExactRun.zero _ _
  | append_singleton init s ih =>
      have hlen : (init ++ [s]).length = 1 + init.length := by simp; omega
      have hs := hmid s (by simp)
      have hmem : mk1 3 (some s) 3 none .Lmove ∈ (markOneTM d).trans := by
        rcases hs with rfl | rfl | rfl | ⟨b, m, hm, rfl⟩
        · simp [markOneTM]
        · simp [markOneTM]
        · simp [markOneTM]
        · simp only [markOneTM, List.mem_append, List.mem_map]
          right; exact ⟨(b, m), mem_allXSyms hm, rfl⟩
      have hcfg : 3 :: (init ++ [s] ++ suf) = (3 :: init) ++ s :: suf := by simp [List.append_assoc]
      have hidx : (init ++ [s]).length = (3 :: init).length := by simp
      have h1 : ExactRun (markOneTM d)
          ⟨3, [([], (init ++ [s]).length, 3 :: (init ++ [s] ++ suf))]⟩
          ⟨3, [([], init.length, 3 :: (init ++ (s :: suf)))]⟩ 1 := by
        rw [hcfg, hidx]
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
          markOneTM_step d 3 3 (3 :: init).length _ _ none .Lmove hmem (currentTapeSymbol_at (3 :: init) s suf) (by omega)
      have h2 := ih (s :: suf) (fun x hx => hmid x (by simp [hx]))
      have h12 := h1.trans h2
      rw [← hlen] at h12
      simpa [List.append_assoc] using h12

lemma list_drop_eq_cons {α : Type*} (l : List α) (u : ℕ) (h : u < l.length) :
    l.drop u = l[u] :: l.drop (u + 1) := by
  induction l generalizing u with
  | nil => simp at h
  | cons a tl ih =>
      cases u with
      | zero => rfl
      | succ k => exact ih k (by simp at h; omega)

def markOneCounter (d : ℕ) : CounterSpec d 0 (fun _ => 1) (fun n m => 2 * (n + m) + 6) where
  M := markOneTM d
  exit := 4
  hSig := rfl
  hTapes := rfl
  hValid := markOneTM_valid d
  hExitLt := by simp [markOneTM]
  hNoExitTrans := fun e he => by
    simp only [markOneTM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at he
    rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;>
      simp [mk1]
  hHaltIff := fun cfg => by
    unfold haltingStateReached markOneTM
    match cfg.state_idx with
    | 0 | 1 | 2 | 3 => simp
    | 4 => simp
    | n + 5 => simp
  hRun := fun xs u c hok hu => by
    have hxs_lt : ∀ bm ∈ xs, bm.2 < 2 ^ d := fun bm hbm => (hok bm hbm).1
    let xL := xs.map (fun bm => xSym bm.1 bm.2)
    let cPre := (c.take u).map cMark
    let cSuf := (c.drop u).map cUnmark
    -- Step 0 -> 1
    have h0 : ExactRun (markOneTM d) ⟨0, [([], 0, lenTape xs u c)]⟩
        ⟨1, [([], 1, [3] ++ xL ++ ([0] ++ cPre ++ cSuf ++ [0, 3]))]⟩ 1 := by
      have hmem : mk1 0 (some 3) 1 none .Rmove ∈ (markOneTM d).trans := by simp [markOneTM]
      simpa [lenTape, xL, cPre, cSuf, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
        markOneTM_step d 0 1 0 (lenTape xs u c) _ none .Rmove hmem (currentTapeSymbol_at [] 3 _) (by omega)
    -- Scan X
    have h1 := markOneTM_scanX d xs [3] ([0] ++ cPre ++ cSuf ++ [0, 3]) hxs_lt
    -- Step across 0 -> state 2
    have h2 : ExactRun (markOneTM d)
        ⟨1, [([], ([3] ++ xL).length, ([3] ++ xL) ++ 0 :: (cPre ++ cSuf ++ [0, 3]))]⟩
        ⟨2, [([], ([3] ++ xL ++ [0]).length, ([3] ++ xL ++ [0]) ++ cPre ++ (cSuf ++ [0, 3]))]⟩ 1 := by
      have hmem : mk1 1 (some 0) 2 none .Rmove ∈ (markOneTM d).trans := by simp [markOneTM]
      have hs := markOneTM_step d 1 2 ([3] ++ xL).length
        (([3] ++ xL) ++ 0 :: (cPre ++ cSuf ++ [0, 3])) (some 0) none .Rmove hmem
        (currentTapeSymbol_at ([3] ++ xL) 0 (cPre ++ cSuf ++ [0, 3])) (by omega)
      simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.length_append, List.length_singleton, List.append_assoc] using hs
    -- Scan marked cPre
    have h3 := markOneTM_scanMark d (c.take u) ([3] ++ xL ++ [0]) (cSuf ++ [0, 3])
    -- Now at cell `1 + xs.length + 1 + u`, reading `cSuf ++ [0, 3]`
    have hmid_ok : ∀ s ∈ xL ++ [0] ++ cPre, s = 0 ∨ s = 4 ∨ s = 5 ∨ ∃ b m, m < 2 ^ d ∧ s = xSym b m := by
      intro s hs
      simp only [List.mem_append, List.mem_singleton, xL, cPre, List.mem_map] at hs
      rcases hs with (⟨bm, hbm, rfl⟩ | rfl) | ⟨b, _, rfl⟩
      · exact Or.inr (Or.inr (Or.inr ⟨bm.1, bm.2, hxs_lt bm hbm, rfl⟩))
      · exact Or.inl rfl
      · cases b <;> [exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inl rfl))]
    by_cases hlt : u < c.length
    · -- Mark c[u]
      have hdrop : c.drop u = (c)[u] :: c.drop (u + 1) := list_drop_eq_cons c u hlt
      have hcSuf : cSuf = cUnmark (c)[u] :: (c.drop (u + 1)).map cUnmark := by
        dsimp only [cSuf]; rw [hdrop]; rfl
      have htake_succ : c.take (u + 1) = c.take u ++ [(c)[u]] := List.take_succ_eq_append_getElem hlt
      have hmin : min (u + 1) c.length = u + 1 := by omega
      let preAll := [3] ++ xL ++ [0] ++ cPre
      have h4 : ExactRun (markOneTM d)
          ⟨2, [([], preAll.length, preAll ++ cUnmark (c)[u] :: ((c.drop (u + 1)).map cUnmark ++ [0, 3]))]⟩
          ⟨3, [([], (xL ++ [0] ++ cPre).length,
            3 :: ((xL ++ [0] ++ cPre) ++ (cMark (c)[u] :: (c.drop (u + 1)).map cUnmark ++ [0, 3])))]⟩ 1 := by
        cases hc : (c)[u] with
        | false =>
            have hmem : mk1 2 (some 1) 3 (some 4) .Lmove ∈ (markOneTM d).trans := by simp [markOneTM]
            have hs := markOneTM_step d 2 3 preAll.length
              (preAll ++ 1 :: ((c.drop (u + 1)).map cUnmark ++ [0, 3])) (some 1) (some 4) .Lmove hmem
              (currentTapeSymbol_at preAll 1 ((c.drop (u + 1)).map cUnmark ++ [0, 3])) (by omega)
            rw [tapeStep_write_at] at hs
            simpa [preAll, cUnmark, cMark, moveTapeHead, List.append_assoc] using hs
        | true =>
            have hmem : mk1 2 (some 2) 3 (some 5) .Lmove ∈ (markOneTM d).trans := by simp [markOneTM]
            have hs := markOneTM_step d 2 3 preAll.length
              (preAll ++ 2 :: ((c.drop (u + 1)).map cUnmark ++ [0, 3])) (some 2) (some 5) .Lmove hmem
              (currentTapeSymbol_at preAll 2 ((c.drop (u + 1)).map cUnmark ++ [0, 3])) (by omega)
            rw [tapeStep_write_at] at hs
            simpa [preAll, cUnmark, cMark, moveTapeHead, List.append_assoc] using hs
      have h5 := markOneTM_rewind d (xL ++ [0] ++ cPre)
        (cMark (c)[u] :: (c.drop (u + 1)).map cUnmark ++ [0, 3]) hmid_ok
      have h6 : ExactRun (markOneTM d)
          ⟨3, [([], 0, 3 :: ((xL ++ [0] ++ cPre) ++ (cMark (c)[u] :: (c.drop (u + 1)).map cUnmark ++ [0, 3])))]⟩
          ⟨4, [([], 0, lenTape xs (min (u + 1) c.length) c)]⟩ 1 := by
        have hmem : mk1 3 (some 3) 4 none .Nmove ∈ (markOneTM d).trans := by simp [markOneTM]
        have hlt_eq : lenTape xs (u + 1) c =
            3 :: ((xL ++ [0] ++ cPre) ++ (cMark (c)[u] :: (c.drop (u + 1)).map cUnmark ++ [0, 3])) := by
          simp only [lenTape, htake_succ, xL, cPre, List.map_append, List.map_singleton,
            List.append_assoc, List.cons_append, List.nil_append]
        rw [hmin, hlt_eq]
        have hs := markOneTM_step d 3 4 0
          ([] ++ 3 :: ((xL ++ [0] ++ cPre) ++ (cMark (c)[u] :: (c.drop (u + 1)).map cUnmark ++ [0, 3])))
          (some 3) none .Nmove hmem
          (currentTapeSymbol_at [] 3 ((xL ++ [0] ++ cPre) ++ (cMark (c)[u] :: (c.drop (u + 1)).map cUnmark ++ [0, 3])))
          (by omega)
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead] using hs
      have h01 : ExactRun (markOneTM d) ⟨0, [([], 0, lenTape xs u c)]⟩
          ⟨1, [([], ([3] ++ xL).length, ([3] ++ xL) ++ 0 :: (cPre ++ cSuf ++ [0, 3]))]⟩ (1 + xs.length) := by
        simpa [List.append_assoc] using h0.trans (by simpa [xL] using h1)
      have h02 := h01.trans h2
      have h03 : ExactRun (markOneTM d) ⟨0, [([], 0, lenTape xs u c)]⟩
          ⟨2, [([], preAll.length, preAll ++ cUnmark (c)[u] :: ((c.drop (u + 1)).map cUnmark ++ [0, 3]))]⟩
          (1 + xs.length + 1 + (c.take u).length) := by
        simpa [preAll, cPre, hcSuf, List.append_assoc] using h02.trans h3
      have htot := ((h03.trans h4).trans h5).trans h6
      refine ⟨_, ?_, htot⟩
      simp only [xL, cPre, List.length_append, List.length_map, List.length_take, List.length_singleton]
      omega
    · -- u = c.length: hit 0, rewind unchanged
      have hu_eq : u = c.length := by omega
      have hdrop : c.drop u = [] := List.drop_eq_nil_of_le (by omega)
      have hcSuf : cSuf = [] := by dsimp only [cSuf]; rw [hdrop]; rfl
      have hmin : min (u + 1) c.length = u := by omega
      let preAll := [3] ++ xL ++ [0] ++ cPre
      have h4 : ExactRun (markOneTM d)
          ⟨2, [([], preAll.length, preAll ++ 0 :: [3])]⟩
          ⟨3, [([], (xL ++ [0] ++ cPre).length, 3 :: ((xL ++ [0] ++ cPre) ++ [0, 3]))]⟩ 1 := by
        have hmem : mk1 2 (some 0) 3 none .Lmove ∈ (markOneTM d).trans := by simp [markOneTM]
        have hs := markOneTM_step d 2 3 preAll.length (preAll ++ 0 :: [3]) (some 0) none .Lmove hmem
          (currentTapeSymbol_at preAll 0 [3]) (by omega)
        simpa [preAll, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
      have h5 := markOneTM_rewind d (xL ++ [0] ++ cPre) [0, 3] hmid_ok
      have h6 : ExactRun (markOneTM d)
          ⟨3, [([], 0, 3 :: ((xL ++ [0] ++ cPre) ++ [0, 3]))]⟩
          ⟨4, [([], 0, lenTape xs (min (u + 1) c.length) c)]⟩ 1 := by
        have hmem : mk1 3 (some 3) 4 none .Nmove ∈ (markOneTM d).trans := by simp [markOneTM]
        have hlt_eq : lenTape xs u c = 3 :: ((xL ++ [0] ++ cPre) ++ [0, 3]) := by
          simp only [lenTape, hdrop, xL, cPre, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
        rw [hmin, hlt_eq]
        have hs := markOneTM_step d 3 4 0 ([] ++ 3 :: ((xL ++ [0] ++ cPre) ++ [0, 3]))
          (some 3) none .Nmove hmem (currentTapeSymbol_at [] 3 ((xL ++ [0] ++ cPre) ++ [0, 3])) (by omega)
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead] using hs
      have h01 : ExactRun (markOneTM d) ⟨0, [([], 0, lenTape xs u c)]⟩
          ⟨1, [([], ([3] ++ xL).length, ([3] ++ xL) ++ 0 :: (cPre ++ cSuf ++ [0, 3]))]⟩ (1 + xs.length) := by
        simpa [List.append_assoc] using h0.trans (by simpa [xL] using h1)
      have h02 := h01.trans h2
      have h03 : ExactRun (markOneTM d) ⟨0, [([], 0, lenTape xs u c)]⟩
          ⟨2, [([], preAll.length, preAll ++ 0 :: [3])]⟩
          (1 + xs.length + 1 + (c.take u).length) := by
        simpa [preAll, cPre, hcSuf, List.append_assoc] using h02.trans h3
      have htot := ((h03.trans h4).trans h5).trans h6
      refine ⟨_, ?_, htot⟩
      simp only [xL, cPre, List.length_append, List.length_map, List.length_take, List.length_singleton]
      omega

/-! ### 2c. Sequential composition `seqCounter` (single bridge on `some 3`) -/

def seqTM (M₁ M₂ : FlatTM) (e₁ : ℕ) : FlatTM where
  sig := max M₁.sig M₂.sig
  tapes := 1
  states := M₁.states + M₂.states
  trans := M₁.trans ++ [mk1 e₁ (some 3) (M₁.states + M₂.start) none .Nmove] ++ M₂.trans.map (shiftEntry M₁.states)
  start := M₁.start
  halt := List.replicate M₁.states false ++ M₂.halt

lemma seqTM_valid (M₁ M₂ : FlatTM) (e₁ : ℕ)
    (h1 : validFlatTM M₁) (h2 : validFlatTM M₂) (ht1 : M₁.tapes = 1) (ht2 : M₂.tapes = 1)
    (he₁ : e₁ < M₁.states) (h3 : 3 < max M₁.sig M₂.sig) :
    validFlatTM (seqTM M₁ M₂ e₁) := by
  refine ⟨Nat.lt_of_lt_of_le h1.1 (Nat.le_add_right _ _), by simp [seqTM, h2.2.1], ?_⟩
  intro e he
  simp only [seqTM, List.mem_append, List.mem_singleton, List.mem_map] at he
  rcases he with (hm1 | rfl) | ⟨e', he', rfl⟩
  · have hv := h1.2.2 e hm1
    refine ⟨Nat.lt_of_lt_of_le hv.1 (Nat.le_add_right _ _),
            Nat.lt_of_lt_of_le hv.2.1 (Nat.le_add_right _ _),
            hv.2.2.1.trans ht1, hv.2.2.2.1.trans ht1, hv.2.2.2.2.1.trans ht1, ?_, ?_⟩
    · intro x hx; cases x with
      | none => trivial
      | some v => exact Nat.lt_of_lt_of_le (hv.2.2.2.2.2.1 (some v) hx) (Nat.le_max_left _ _)
    · intro x hx; cases x with
      | none => trivial
      | some v => exact Nat.lt_of_lt_of_le (hv.2.2.2.2.2.2 (some v) hx) (Nat.le_max_left _ _)
  · refine ⟨Nat.lt_of_lt_of_le he₁ (Nat.le_add_right _ _), by simp [seqTM, mk1]; have := h2.1; omega, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact h3
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; trivial
  · have hv := h2.2.2 e' he'
    refine ⟨by simp [seqTM, shiftEntry]; have := hv.1; omega, by simp [seqTM, shiftEntry]; have := hv.2.1; omega,
            hv.2.2.1.trans ht2, hv.2.2.2.1.trans ht2, hv.2.2.2.2.1.trans ht2, ?_, ?_⟩
    · intro x hx; cases x with
      | none => trivial
      | some v => exact Nat.lt_of_lt_of_le (hv.2.2.2.2.2.1 (some v) hx) (Nat.le_max_right _ _)
    · intro x hx; cases x with
      | none => trivial
      | some v => exact Nat.lt_of_lt_of_le (hv.2.2.2.2.2.2 (some v) hx) (Nat.le_max_right _ _)

lemma seqTM_halt_lt (M₁ M₂ : FlatTM) (e₁ : ℕ) (cfg : FlatTMConfig) (hlt : cfg.state_idx < M₁.states) :
    haltingStateReached (seqTM M₁ M₂ e₁) cfg = false := by
  unfold haltingStateReached seqTM
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt])]
  simp [hlt]

lemma seqTM_halt_shift (M₁ M₂ : FlatTM) (e₁ : ℕ) (cfg : FlatTMConfig) :
    haltingStateReached (seqTM M₁ M₂ e₁) (shiftCfg M₁.states cfg) = haltingStateReached M₂ cfg := by
  unfold haltingStateReached seqTM shiftCfg
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_replicate]
  simp [List.getD_eq_getElem?_getD]

-- Cleaner: lift `stepFlatTM` directly without assuming `step ≠ none`!
lemma seqTM_step1_eq {M₁ M₂ : FlatTM} {e₁ : ℕ}
    (h1 : validFlatTM M₁) (h2 : validFlatTM M₂)
    (cfg : FlatTMConfig) (hlt : cfg.state_idx < M₁.states) (hne : cfg.state_idx ≠ e₁) :
    stepFlatTM (seqTM M₁ M₂ e₁) cfg = stepFlatTM M₁ cfg := by
  unfold stepFlatTM seqTM
  simp only [Option.bind_eq_bind]
  cases hf : M₁.trans.find? (fun e => entryMatchesConfig e cfg) with
  | some e =>
      have hfind : (M₁.trans ++ [mk1 e₁ (some 3) (M₁.states + M₂.start) none .Nmove] ++
          M₂.trans.map (shiftEntry M₁.states)).find? (fun e => entryMatchesConfig e cfg) = some e := by
        rw [List.append_assoc]
        exact list_find?_append_some _ _ _ hf
      rw [hfind]
  | none =>
      have hnone1 : ∀ e ∈ M₁.trans, entryMatchesConfig e cfg = false := by
        intro e he
        cases hv : entryMatchesConfig e cfg with
        | false => rfl
        | true =>
            have hne_none := List.find?_eq_none.mp hf e he
            exact absurd hv hne_none
      have hnone2 : entryMatchesConfig (mk1 e₁ (some 3) (M₁.states + M₂.start) none .Nmove) cfg = false := by
        simp [entryMatchesConfig, mk1, hne.symm]
      have hnone3 : ∀ e ∈ M₂.trans.map (shiftEntry M₁.states), entryMatchesConfig e cfg = false := by
        intro e he
        rw [List.mem_map] at he; rcases he with ⟨e', _, rfl⟩
        have hne' : e'.src_state + M₁.states ≠ cfg.state_idx := by omega
        simp [entryMatchesConfig, shiftEntry, hne']
      rw [List.append_assoc, list_find?_append_left _ _ _ hnone1]
      simp only [List.cons_append, List.nil_append, List.find?, hnone2]
      have hf3 : (M₂.trans.map (shiftEntry M₁.states)).find? (fun e => entryMatchesConfig e cfg) = none :=
        List.find?_eq_none.mpr (fun e he => by rw [hnone3 e he]; decide)
      rw [hf3]

lemma seqTM_step2_eq {M₁ M₂ : FlatTM} {e₁ : ℕ}
    (h1 : validFlatTM M₁) (he₁ : e₁ < M₁.states)
    (cfg : FlatTMConfig) :
    stepFlatTM (seqTM M₁ M₂ e₁) (shiftCfg M₁.states cfg) =
      (stepFlatTM M₂ cfg).map (shiftCfg M₁.states) := by
  unfold stepFlatTM seqTM
  simp only [Option.bind_eq_bind]
  have hnone1 : ∀ e ∈ M₁.trans, entryMatchesConfig e (shiftCfg M₁.states cfg) = false := by
    intro e he
    have hv := (h1.2.2 e he).1
    have hne : e.src_state ≠ cfg.state_idx + M₁.states := by omega
    simp [entryMatchesConfig, shiftCfg, hne]
  have hnoneB : entryMatchesConfig (mk1 e₁ (some 3) (M₁.states + M₂.start) none .Nmove)
      (shiftCfg M₁.states cfg) = false := by
    have hne : e₁ ≠ cfg.state_idx + M₁.states := by omega
    simp [entryMatchesConfig, mk1, shiftCfg, hne]
  rw [List.append_assoc, list_find?_append_left _ _ _ hnone1]
  simp only [List.cons_append, List.nil_append, List.find?, hnoneB]
  rw [list_find?_map_shift]
  cases hf : M₂.trans.find? (fun e => entryMatchesConfig e cfg) with
  | none => rfl
  | some e =>
      simp only [Option.map_some, Option.bind_some]
      unfold applyTransitionEntry shiftEntry shiftCfg
      dsimp only
      split_ifs <;> simp

lemma seqTM_lift1_clean {M₁ M₂ : FlatTM} {e₁ : ℕ}
    (h1 : validFlatTM M₁) (h2 : validFlatTM M₂)
    (hHalt1 : ∀ cfg, haltingStateReached M₁ cfg = true ↔ cfg.state_idx = e₁)
    {c0 c1 : FlatTMConfig} {t1 : ℕ}
    (h0 : c0.state_idx < M₁.states) (hrun : ExactRun M₁ c0 c1 t1) :
    ExactRun (seqTM M₁ M₂ e₁) c0 c1 t1 := by
  induction t1 generalizing c0 with
  | zero =>
      have : c0 = c1 := Option.some.inj hrun.1
      subst this; exact ExactRun.zero _ _
  | succ n ih =>
      have hnh0 : haltingStateReached M₁ c0 = false := hrun.2 0 (by omega) c0 rfl
      have hne_e1 : c0.state_idx ≠ e₁ := fun heq => by
        have := (hHalt1 c0).mpr heq; rw [hnh0] at this; cases this
      have hnh_seq : haltingStateReached (seqTM M₁ M₂ e₁) c0 = false := seqTM_halt_lt M₁ M₂ e₁ c0 h0
      have hst_eq := seqTM_step1_eq h1 h2 c0 h0 hne_e1
      have hr := hrun.1
      change (if haltingStateReached M₁ c0 = true then some c0
              else match stepFlatTM M₁ c0 with
                | none => some c0
                | some cm => runFlatTM n M₁ cm) = some c1 at hr
      rw [hnh0] at hr
      cases hs : stepFlatTM M₁ c0 with
      | none =>
          rw [hs] at hr
          have heq : c0 = c1 := Option.some.inj hr
          subst heq
          refine ⟨?_, ?_⟩
          · rw [runFlatTM_stuck (seqTM M₁ M₂ e₁) c0 hnh_seq (hst_eq.trans hs) (n + 1)]
          · intro k _ ck hck
            rw [runFlatTM_stuck (seqTM M₁ M₂ e₁) c0 hnh_seq (hst_eq.trans hs) k] at hck
            have := Option.some.inj hck; subst this; exact hnh_seq
      | some cm =>
          rw [hs] at hr
          have hcm_lt : cm.state_idx < M₁.states :=
            ExactRun.state_lt h1 h0 (runFlatTM_step_one M₁ c0 cm hnh0 hs)
          have hrem : ExactRun M₁ cm c1 n := by
            refine ⟨hr, ?_⟩
            intro k hk ck hck
            have hck' : runFlatTM (k + 1) M₁ c0 = some ck := by
              show (if haltingStateReached M₁ c0 = true then some c0
                    else match stepFlatTM M₁ c0 with
                      | none => some c0
                      | some cm' => runFlatTM k M₁ cm') = some ck
              rw [hnh0, hs]; exact hck
            exact hrun.2 (k + 1) (by omega) ck hck'
          have h1step := ExactRun.step1 (seqTM M₁ M₂ e₁) c0 cm hnh_seq (hst_eq.trans hs)
          have hrest := ih hcm_lt hrem
          simpa [Nat.add_comm] using h1step.trans hrest

lemma seqTM_lift2_clean {M₁ M₂ : FlatTM} {e₁ : ℕ}
    (h1 : validFlatTM M₁) (he₁ : e₁ < M₁.states)
    {c0 c1 : FlatTMConfig} {t2 : ℕ}
    (hrun : ExactRun M₂ c0 c1 t2) :
    ExactRun (seqTM M₁ M₂ e₁) (shiftCfg M₁.states c0) (shiftCfg M₁.states c1) t2 := by
  induction t2 generalizing c0 with
  | zero =>
      have : c0 = c1 := Option.some.inj hrun.1
      subst this; exact ExactRun.zero _ _
  | succ n ih =>
      have hnh0 : haltingStateReached M₂ c0 = false := hrun.2 0 (by omega) c0 rfl
      have hnh_seq : haltingStateReached (seqTM M₁ M₂ e₁) (shiftCfg M₁.states c0) = false := by
        rw [seqTM_halt_shift]; exact hnh0
      have hst_eq := seqTM_step2_eq (M₂ := M₂) h1 he₁ c0
      have hr := hrun.1
      change (if haltingStateReached M₂ c0 = true then some c0
              else match stepFlatTM M₂ c0 with
                | none => some c0
                | some cm => runFlatTM n M₂ cm) = some c1 at hr
      rw [hnh0] at hr
      cases hs : stepFlatTM M₂ c0 with
      | none =>
          rw [hs] at hr
          have heq : c0 = c1 := Option.some.inj hr
          subst heq
          refine ⟨?_, ?_⟩
          · rw [runFlatTM_stuck (seqTM M₁ M₂ e₁) _ hnh_seq (by rw [hst_eq, hs]; rfl) (n + 1)]
          · intro k _ ck hck
            rw [runFlatTM_stuck (seqTM M₁ M₂ e₁) _ hnh_seq (by rw [hst_eq, hs]; rfl) k] at hck
            have := Option.some.inj hck; subst this; exact hnh_seq
      | some cm =>
          rw [hs] at hr
          have hrem : ExactRun M₂ cm c1 n := by
            refine ⟨hr, ?_⟩
            intro k hk ck hck
            have hck' : runFlatTM (k + 1) M₂ c0 = some ck := by
              show (if haltingStateReached M₂ c0 = true then some c0
                    else match stepFlatTM M₂ c0 with
                      | none => some c0
                      | some cm' => runFlatTM k M₂ cm') = some ck
              rw [hnh0, hs]; exact hck
            exact hrun.2 (k + 1) (by omega) ck hck'
          have h1step := ExactRun.step1 (seqTM M₁ M₂ e₁) _ (shiftCfg M₁.states cm) hnh_seq (by rw [hst_eq, hs]; rfl)
          have hrest := ih hrem
          simpa [Nat.add_comm] using h1step.trans hrest

lemma seqTM_bridge_step {M₁ M₂ : FlatTM} {e₁ : ℕ}
    (he₁ : e₁ < M₁.states) (hno : ∀ e ∈ M₁.trans, e.src_state ≠ e₁) (right : List ℕ)
    (h3 : currentTapeSymbol ([], 0, right) = some 3) :
    ExactRun (seqTM M₁ M₂ e₁)
      ⟨e₁, [([], 0, right)]⟩
      (shiftCfg M₁.states ⟨M₂.start, [([], 0, right)]⟩) 1 := by
  apply ExactRun.step1 _ _ _ (seqTM_halt_lt M₁ M₂ e₁ _ he₁)
  unfold stepFlatTM seqTM
  simp only [Option.bind_eq_bind]
  have hnone1 : ∀ e ∈ M₁.trans, entryMatchesConfig e ⟨e₁, [([], 0, right)]⟩ = false := by
    intro e he; simp [entryMatchesConfig, hno e he]
  rw [List.append_assoc, list_find?_append_left _ _ _ hnone1]
  simp only [List.cons_append, List.nil_append, List.find?]
  have hm : entryMatchesConfig (mk1 e₁ (some 3) (M₁.states + M₂.start) none .Nmove) ⟨e₁, [([], 0, right)]⟩ = true := by
    simp [entryMatchesConfig, mk1, h3]
  rw [hm]
  simp [applyTransitionEntry, mk1, tapeStep, writeCurrentTapeSymbol, moveTapeHead, shiftCfg, Nat.add_comm]

def seqCounter {d lvl : ℕ} {K₁ K₂ : ℕ → ℕ} {T₁ T₂ : ℕ → ℕ → ℕ}
    (C₁ : CounterSpec d lvl K₁ T₁) (C₂ : CounterSpec d lvl K₂ T₂) :
    CounterSpec d lvl (fun n => K₁ n + K₂ n) (fun n m => T₁ n m + 1 + T₂ n m) where
  M := seqTM C₁.M C₂.M C₁.exit
  exit := C₂.exit + C₁.M.states
  hSig := by simp [seqTM, C₁.hSig, C₂.hSig]
  hTapes := rfl
  hValid := seqTM_valid C₁.M C₂.M C₁.exit C₁.hValid C₂.hValid C₁.hTapes C₂.hTapes C₁.hExitLt
    (by rw [C₁.hSig, C₂.hSig]; unfold sigL; omega)
  hExitLt := by simp [seqTM]; have := C₂.hExitLt; omega
  hNoExitTrans := fun e he => by
    simp only [seqTM, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (hm1 | rfl) | ⟨e', he', rfl⟩
    · have := (C₁.hValid.2.2 e hm1).1; omega
    · simp only [mk1]; have := C₁.hExitLt; omega
    · simp only [shiftEntry]; have := C₂.hNoExitTrans e' he'; omega
  hHaltIff := fun cfg => by
    by_cases hlt : cfg.state_idx < C₁.M.states
    · rw [seqTM_halt_lt C₁.M C₂.M C₁.exit cfg hlt]; simp; omega
    · have hge : C₁.M.states ≤ cfg.state_idx := Nat.le_of_not_lt hlt
      let cfg2 : FlatTMConfig := { cfg with state_idx := cfg.state_idx - C₁.M.states }
      have hsh : cfg = shiftCfg C₁.M.states cfg2 := by
        cases cfg with | mk st tp =>
          simp only [shiftCfg, cfg2] at hge ⊢
          congr 1; omega
      rw [hsh, seqTM_halt_shift, C₂.hHaltIff]
      simp [shiftCfg, cfg2]
  hRun := fun xs u c hok hu => by
    obtain ⟨t₁, ht₁, hr₁⟩ := C₁.hRun xs u c hok hu
    have hu' : min (u + K₁ xs.length) c.length ≤ c.length := Nat.min_le_right _ _
    obtain ⟨t₂, ht₂, hr₂⟩ := C₂.hRun xs (min (u + K₁ xs.length) c.length) c hok hu'
    have hlift1 := seqTM_lift1_clean C₁.hValid C₂.hValid C₁.hHaltIff C₁.hValid.1 hr₁
    have hbr := seqTM_bridge_step (M₂ := C₂.M) C₁.hExitLt C₁.hNoExitTrans
      (lenTape xs (min (u + K₁ xs.length) c.length) c) (currentTapeSymbol_at [] 3 _)
    have hlift2 := seqTM_lift2_clean (M₁ := C₁.M) C₁.hValid C₁.hExitLt hr₂
    have hmin : min (min (u + K₁ xs.length) c.length + K₂ xs.length) c.length =
        min (u + (K₁ xs.length + K₂ xs.length)) c.length := by omega
    rw [hmin] at hlift2
    exact ⟨t₁ + 1 + t₂, by omega, (hlift1.trans hbr).trans hlift2⟩

def repeatCounter {d lvl : ℕ} {K : ℕ → ℕ} {T : ℕ → ℕ → ℕ}
    (r : ℕ) (C : CounterSpec d lvl K T) :
    CounterSpec d lvl (fun n => r * K n) (fun n m => r * (T n m + 1)) :=
  match r with
  | 0 =>
      { noopCounter d lvl with
        hRun := fun xs u c hok hu => by
          simpa using (noopCounter d lvl).hRun xs u c hok hu }
  | r' + 1 =>
      let prev := repeatCounter r' C
      let combined := seqCounter C prev
      { combined with
        hRun := fun xs u c hok hu => by
          obtain ⟨t, ht, hr⟩ := combined.hRun xs u c hok hu
          refine ⟨t, ?_, ?_⟩
          · have : (r' + 1) * (T xs.length c.length + 1) =
                T xs.length c.length + 1 + r' * (T xs.length c.length + 1) := by ring
            omega
          · have : (r' + 1) * K xs.length = K xs.length + r' * K xs.length := by ring
            rwa [this] }

/-! ### 2d. `forEachXBit`: iterates `body` once for every bit of `x`, using marker bit `k` -/

lemma bit_set_props {m k d : ℕ} (hm : m < 2 ^ d) (hk : k < d) (h0 : (m / 2 ^ k) % 2 = 0) :
    m + 2 ^ k < 2 ^ d ∧
    ((m + 2 ^ k) / 2 ^ k) % 2 = 1 ∧
    ∀ j < k, ((m + 2 ^ k) / 2 ^ j) % 2 = (m / 2 ^ j) % 2 := by
  have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv : (m + 2 ^ k) / 2 ^ k = m / 2 ^ k + 1 := by
    rw [Nat.add_div_right _ hpow]
  have hlt : m + 2 ^ k < 2 ^ d := by
    have h2k1 : 2 ^ (k + 1) ∣ 2 ^ d := Nat.pow_dvd_pow 2 (by omega)
    rcases h2k1 with ⟨q, hq⟩
    have hrem : m % 2 ^ (k + 1) < 2 ^ k := by
      have hmod := Nat.div_add_mod m (2 ^ k)
      have hdiv2 : m / 2 ^ k = 2 * (m / 2 ^ (k + 1)) := by
        have : m / 2 ^ (k + 1) = (m / 2 ^ k) / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
        omega
      have h1 : m = 2 ^ (k + 1) * (m / 2 ^ (k + 1)) + m % 2 ^ k := by
        have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
        calc m = 2 ^ k * (m / 2 ^ k) + m % 2 ^ k := hmod.symm
          _ = 2 ^ k * (2 * (m / 2 ^ (k + 1))) + m % 2 ^ k := by rw [hdiv2]
          _ = 2 ^ (k + 1) * (m / 2 ^ (k + 1)) + m % 2 ^ k := by rw [h2k]; ring
      have hlt_mod : m % 2 ^ k < 2 ^ k := Nat.mod_lt m hpow
      have hlt_mod2 : m % 2 ^ k < 2 ^ (k + 1) := lt_trans hlt_mod (by rw [Nat.pow_succ]; omega)
      have : m % 2 ^ (k + 1) = m % 2 ^ k := by
        conv_lhs => rw [h1]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_mod2]
      omega
    have hq_lt : m / 2 ^ (k + 1) < q := by
      rw [hq] at hm
      exact Nat.div_lt_of_lt_mul hm
    have hdm := Nat.div_add_mod m (2 ^ (k + 1))
    have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    nlinarith
  refine ⟨hlt, by rw [hdiv]; omega, ?_⟩
  intro j hj
  have h2j : 0 < 2 ^ j := Nat.two_pow_pos j
  have hquot : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Nat.pow_add]; congr 1; omega
  have heven : 2 ^ (k - j) % 2 = 0 := by
    have hkjm : k - j = (k - j - 1) + 1 := by omega
    rw [hkjm, Nat.pow_succ]; omega
  rw [hquot, Nat.add_mul_div_left _ _ h2j]
  omega

-- 7 wrapper states (0..6):
-- 0: start at 0 -> R to 1
-- 1: at cell 1: if 0 -> L to 6 (halt); if xSym(bit k = 0) -> set bit k, L to 7 + body.start
-- 7 + bodyExit: at cell 0 reading 3 -> R to 2
-- 2: scan right over bit k = 0; on bit k = 1 -> clear bit k, R to 3
-- 3: at next cell: if 0 -> L to 5 (rewindToHalt); if xSym(bit k = 0) -> set bit k, L to 4 (rewindToBody)
-- 4: rewind left over all xSym; on 3 -> 7 + body.start (Nmove)
-- 5: rewind left over all xSym; on 3 -> 6 (halt, Nmove)
-- 6: HALT!
def forEachTM7 (d k : ℕ) (body : FlatTM) (bodyExit : ℕ) : FlatTM where
  sig := sigL d
  tapes := 1
  states := 7 + body.states
  trans :=
    [ mk1 0 (some 3) 1 none .Rmove
    , mk1 1 (some 0) 6 none .Lmove
    , mk1 3 (some 0) 5 none .Lmove
    , mk1 4 (some 3) (7 + body.start) none .Nmove
    , mk1 5 (some 3) 6 none .Nmove
    , mk1 (7 + bodyExit) (some 3) 2 none .Rmove
    ] ++
    ((allXSyms d).filter (fun bm => (bm.2 / 2 ^ k) % 2 == 0 && decide (bm.2 + 2 ^ k < 2 ^ d))).flatMap (fun bm =>
      [ mk1 1 (some (xSym bm.1 bm.2)) (7 + body.start) (some (xSym bm.1 (bm.2 + 2 ^ k))) .Lmove
      , mk1 2 (some (xSym bm.1 bm.2)) 2 none .Rmove
      , mk1 3 (some (xSym bm.1 bm.2)) 4 (some (xSym bm.1 (bm.2 + 2 ^ k))) .Lmove
      ]) ++
    ((allXSyms d).filter (fun bm => (bm.2 / 2 ^ k) % 2 == 1)).map (fun bm =>
      mk1 2 (some (xSym bm.1 bm.2)) 3 (some (xSym bm.1 (bm.2 - 2 ^ k))) .Rmove) ++
    (allXSyms d).flatMap (fun bm =>
      [ mk1 4 (some (xSym bm.1 bm.2)) 4 none .Lmove
      , mk1 5 (some (xSym bm.1 bm.2)) 5 none .Lmove
      ]) ++
    body.trans.map (shiftEntry 7)
  start := 0
  halt := List.replicate 7 false |>.set 6 true |>.append (List.replicate body.states false)

lemma forEachTM7_halt_iff (d k : ℕ) (body : FlatTM) (bodyExit : ℕ) (cfg : FlatTMConfig) :
    haltingStateReached (forEachTM7 d k body bodyExit) cfg = true ↔ cfg.state_idx = 6 := by
  unfold haltingStateReached forEachTM7
  change ([false, false, false, false, false, false, true] ++ List.replicate body.states false).getD cfg.state_idx false = true ↔
    cfg.state_idx = 6
  match h : cfg.state_idx with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp
  | 6 => simp
  | n + 7 =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp

lemma forEachTM7_valid (d k : ℕ) (hk : k < d) (body : FlatTM) (bodyExit : ℕ)
    (hsig : body.sig = sigL d) (ht : body.tapes = 1) (hv : validFlatTM body) (he : bodyExit < body.states) :
    validFlatTM (forEachTM7 d k body bodyExit) := by
  have h6sig : 6 ≤ sigL d := by unfold sigL; omega
  have hmk : ∀ s rd dst wr mv, s < 7 + body.states → dst < 7 + body.states →
      (match rd with | none => True | some v => v < sigL d) →
      (match wr with | none => True | some v => v < sigL d) →
      flatTMTransEntryValid (forEachTM7 d k body bodyExit) (mk1 s rd dst wr mv) := by
    intro s rd dst wr mv hs hd hrd hwr
    refine ⟨hs, hd, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hrd
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hwr
  refine ⟨by simp [forEachTM7], by simp [forEachTM7]; omega, ?_⟩
  intro e hmem
  simp only [forEachTM7, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_filter, List.mem_map, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmem
  rcases hmem with ((((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨bm, ⟨hbm, _, hadd⟩, hr⟩) | ⟨bm, ⟨hbm, _⟩, rfl⟩) | ⟨bm, hbm, hr⟩) | ⟨e', he', rfl⟩
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by have := hv.1; omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · exact hmk _ _ _ _ _ (by omega) (by omega) (by omega) trivial
  · rcases hr with rfl | rfl | rfl
    · exact hmk _ _ _ _ _ (by omega) (by have := hv.1; omega) (xSym_lt (allXSyms_bound hbm)) (xSym_lt hadd)
    · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm)) trivial
    · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm)) (xSym_lt hadd)
  · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm))
      (xSym_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (allXSyms_bound hbm)))
  · rcases hr with rfl | rfl
    · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm)) trivial
    · exact hmk _ _ _ _ _ (by omega) (by omega) (xSym_lt (allXSyms_bound hbm)) trivial
  · have hv' := hv.2.2 e' he'
    refine ⟨by simp [forEachTM7, shiftEntry]; have := hv'.1; omega,
            by simp [forEachTM7, shiftEntry]; have := hv'.2.1; omega,
            hv'.2.2.1.trans ht, hv'.2.2.2.1.trans ht, hv'.2.2.2.2.1.trans ht, ?_, ?_⟩
    · intro x hx; rw [show (forEachTM7 d k body bodyExit).sig = body.sig from hsig.symm]; exact hv'.2.2.2.2.2.1 x hx
    · intro x hx; rw [show (forEachTM7 d k body bodyExit).sig = body.sig from hsig.symm]; exact hv'.2.2.2.2.2.2 x hx

lemma forEachTM7_mem_lt7 (d k : ℕ) (body : FlatTM) (bodyExit : ℕ) {e : FlatTMTransEntry}
    (he : e ∈ (forEachTM7 d k body bodyExit).trans) (hlt : e.src_state < 7) :
    e = mk1 0 (some 3) 1 none .Rmove ∨
    e = mk1 1 (some 0) 6 none .Lmove ∨
    e = mk1 3 (some 0) 5 none .Lmove ∨
    e = mk1 4 (some 3) (7 + body.start) none .Nmove ∨
    e = mk1 5 (some 3) 6 none .Nmove ∨
    (∃ bm : Bool × ℕ, (bm.2 / 2 ^ k) % 2 = 0 ∧
      e = mk1 1 (some (xSym bm.1 bm.2)) (7 + body.start) (some (xSym bm.1 (bm.2 + 2 ^ k))) .Lmove) ∨
    (∃ bm : Bool × ℕ, (bm.2 / 2 ^ k) % 2 = 0 ∧
      e = mk1 2 (some (xSym bm.1 bm.2)) 2 none .Rmove) ∨
    (∃ bm : Bool × ℕ, (bm.2 / 2 ^ k) % 2 = 0 ∧
      e = mk1 3 (some (xSym bm.1 bm.2)) 4 (some (xSym bm.1 (bm.2 + 2 ^ k))) .Lmove) ∨
    (∃ bm : Bool × ℕ, (bm.2 / 2 ^ k) % 2 = 1 ∧
      e = mk1 2 (some (xSym bm.1 bm.2)) 3 (some (xSym bm.1 (bm.2 - 2 ^ k))) .Rmove) ∨
    (∃ bm : Bool × ℕ, e = mk1 4 (some (xSym bm.1 bm.2)) 4 none .Lmove) ∨
    (∃ bm : Bool × ℕ, e = mk1 5 (some (xSym bm.1 bm.2)) 5 none .Lmove) := by
  simp only [forEachTM7, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_filter, List.mem_map, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
  rcases he with ((((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨bm, ⟨_, h0, _⟩, hr⟩) | ⟨bm, ⟨_, h1⟩, rfl⟩) | ⟨bm, _, hr⟩) | ⟨e', _, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · simp [mk1] at hlt
  · rcases hr with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨bm, h0, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨bm, h0, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨bm, h0, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨bm, h1, rfl⟩))))))))
  · rcases hr with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨bm, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨bm, rfl⟩)))))))))
  · simp [shiftEntry] at hlt

lemma forEachTM7_wrap_unique (d k : ℕ) (body : FlatTM) (bodyExit : ℕ)
    {e₁ e₂ : FlatTMTransEntry}
    (h₁ : e₁ ∈ (forEachTM7 d k body bodyExit).trans)
    (h₂ : e₂ ∈ (forEachTM7 d k body bodyExit).trans)
    (hlt1 : e₁.src_state < 7)
    (hs : e₁.src_state = e₂.src_state) (ht : e₁.src_tape_vals = e₂.src_tape_vals) :
    e₁ = e₂ := by
  have hlt2 : e₂.src_state < 7 := by omega
  have c1 := forEachTM7_mem_lt7 d k body bodyExit h₁ hlt1
  have c2 := forEachTM7_mem_lt7 d k body bodyExit h₂ hlt2
  rcases c1 with rfl | rfl | rfl | rfl | rfl | ⟨bm₁, h0₁, rfl⟩ | ⟨bm₁, h0₁, rfl⟩ | ⟨bm₁, h0₁, rfl⟩ | ⟨bm₁, h1₁, rfl⟩ | ⟨bm₁, rfl⟩ | ⟨bm₁, rfl⟩ <;>
  rcases c2 with rfl | rfl | rfl | rfl | rfl | ⟨bm₂, h0₂, rfl⟩ | ⟨bm₂, h0₂, rfl⟩ | ⟨bm₂, h0₂, rfl⟩ | ⟨bm₂, h1₂, rfl⟩ | ⟨bm₂, rfl⟩ | ⟨bm₂, rfl⟩ <;>
  simp [mk1] at hs ht ⊢
  all_goals try (have := xSym_ne_0345 bm₁.1 bm₁.2; omega)
  all_goals try (have := xSym_ne_0345 bm₂.1 bm₂.2; omega)
  all_goals try (obtain ⟨hb, hm⟩ := xSym_inj ht; rw [hb, hm])
  all_goals (obtain ⟨_, hm⟩ := xSym_inj ht; simp_all)

lemma forEachTM7_wrap_step (d k : ℕ) (body : FlatTM) (bodyExit : ℕ)
    (st dst head : ℕ) (right : List ℕ) (rd wr : Option ℕ) (mv : TMMove)
    (hlt : st < 6)
    (hmem : mk1 st rd dst wr mv ∈ (forEachTM7 d k body bodyExit).trans)
    (hrd : currentTapeSymbol ([], head, right) = rd) :
    ExactRun (forEachTM7 d k body bodyExit)
      ⟨st, [([], head, right)]⟩ ⟨dst, [tapeStep ([], head, right) wr mv]⟩ 1 := by
  have hnh : haltingStateReached (forEachTM7 d k body bodyExit) ⟨st, [([], head, right)]⟩ = false := by
    cases hv : haltingStateReached (forEachTM7 d k body bodyExit) ⟨st, [([], head, right)]⟩ with
    | false => rfl
    | true => rw [forEachTM7_halt_iff] at hv; simp at hv; omega
  apply ExactRun.step1 _ _ _ hnh
  rw [stepFlatTM_of_unique (forEachTM7 d k body bodyExit) (mk1 st rd dst wr mv) _ hmem
      (by simp [entryMatchesConfig, mk1, hrd])]
  · simp [applyTransitionEntry, mk1]
  · intro e' he' hm
    simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    exact (forEachTM7_wrap_unique d k body bodyExit hmem he' (by simp [mk1]; omega)
      hm.1.symm ((by simp [mk1, hrd] : _ = _).trans hm.2.symm)).symm

lemma forEachTM7_lift_body (d k : ℕ) {body : FlatTM} {bodyExit : ℕ}
    (hHalt : ∀ cfg, haltingStateReached body cfg = true ↔ cfg.state_idx = bodyExit)
    {c0 c1 : FlatTMConfig} {t : ℕ}
    (hrun : ExactRun body c0 c1 t) :
    ExactRun (forEachTM7 d k body bodyExit) (shiftCfg 7 c0) (shiftCfg 7 c1) t := by
  have hstep_eq : ∀ cfg : FlatTMConfig, cfg.state_idx ≠ bodyExit →
      stepFlatTM (forEachTM7 d k body bodyExit) (shiftCfg 7 cfg) =
      (stepFlatTM body cfg).map (shiftCfg 7) := by
    intro cfg hne
    unfold stepFlatTM forEachTM7
    simp only [Option.bind_eq_bind]
    have hnone_pre : ∀ e ∈
        ([ mk1 0 (some 3) 1 none .Rmove
         , mk1 1 (some 0) 6 none .Lmove
         , mk1 3 (some 0) 5 none .Lmove
         , mk1 4 (some 3) (7 + body.start) none .Nmove
         , mk1 5 (some 3) 6 none .Nmove
         , mk1 (7 + bodyExit) (some 3) 2 none .Rmove
         ] ++
         ((allXSyms d).filter (fun bm => (bm.2 / 2 ^ k) % 2 == 0 && decide (bm.2 + 2 ^ k < 2 ^ d))).flatMap (fun bm =>
           [ mk1 1 (some (xSym bm.1 bm.2)) (7 + body.start) (some (xSym bm.1 (bm.2 + 2 ^ k))) .Lmove
           , mk1 2 (some (xSym bm.1 bm.2)) 2 none .Rmove
           , mk1 3 (some (xSym bm.1 bm.2)) 4 (some (xSym bm.1 (bm.2 + 2 ^ k))) .Lmove
           ]) ++
         ((allXSyms d).filter (fun bm => (bm.2 / 2 ^ k) % 2 == 1)).map (fun bm =>
           mk1 2 (some (xSym bm.1 bm.2)) 3 (some (xSym bm.1 (bm.2 - 2 ^ k))) .Rmove) ++
         (allXSyms d).flatMap (fun bm =>
           [ mk1 4 (some (xSym bm.1 bm.2)) 4 none .Lmove
           , mk1 5 (some (xSym bm.1 bm.2)) 5 none .Lmove
           ])),
        entryMatchesConfig e (shiftCfg 7 cfg) = false := by
      intro e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_flatMap, List.mem_filter, List.mem_map] at he
      rcases he with (((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨_, _, hr⟩) | ⟨_, _, rfl⟩) | ⟨_, _, hr⟩
      · simp [entryMatchesConfig, mk1, shiftCfg]
      · simp [entryMatchesConfig, mk1, shiftCfg]
      · simp [entryMatchesConfig, mk1, shiftCfg]
      · simp [entryMatchesConfig, mk1, shiftCfg]
      · simp [entryMatchesConfig, mk1, shiftCfg]
      · have : 7 + bodyExit ≠ cfg.state_idx + 7 := by omega
        simp [entryMatchesConfig, mk1, shiftCfg, this]
      · rcases hr with rfl | rfl | rfl <;> simp [entryMatchesConfig, mk1, shiftCfg]
      · simp [entryMatchesConfig, mk1, shiftCfg]
      · rcases hr with rfl | rfl <;> simp [entryMatchesConfig, mk1, shiftCfg]
    rw [list_find?_append_left _ _ _ hnone_pre, list_find?_map_shift]
    cases hf : body.trans.find? (fun e => entryMatchesConfig e cfg) with
    | none => rfl
    | some e =>
        simp only [Option.map_some, Option.bind_some]
        unfold applyTransitionEntry shiftEntry shiftCfg; dsimp only; split_ifs <;> simp
  induction t generalizing c0 with
  | zero =>
      have : c0 = c1 := Option.some.inj hrun.1; subst this; exact ExactRun.zero _ _
  | succ n ih =>
      have hnh0 : haltingStateReached body c0 = false := hrun.2 0 (by omega) c0 rfl
      have hne : c0.state_idx ≠ bodyExit := fun heq => by
        have := (hHalt c0).mpr heq; rw [hnh0] at this; cases this
      have hnh_w : haltingStateReached (forEachTM7 d k body bodyExit) (shiftCfg 7 c0) = false := by
        cases hv : haltingStateReached (forEachTM7 d k body bodyExit) (shiftCfg 7 c0) with
        | false => rfl
        | true => rw [forEachTM7_halt_iff] at hv; simp [shiftCfg] at hv
      have hst := hstep_eq c0 hne
      have hr := hrun.1
      change (if haltingStateReached body c0 = true then some c0
              else match stepFlatTM body c0 with
                | none => some c0
                | some cm => runFlatTM n body cm) = some c1 at hr
      rw [hnh0] at hr
      cases hs : stepFlatTM body c0 with
      | none =>
          rw [hs] at hr; have heq : c0 = c1 := Option.some.inj hr; subst heq
          refine ⟨by rw [runFlatTM_stuck _ _ hnh_w (by rw [hst, hs]; rfl) (n + 1)], ?_⟩
          intro j _ ck hck
          rw [runFlatTM_stuck _ _ hnh_w (by rw [hst, hs]; rfl) j] at hck
          have := Option.some.inj hck; subst this; exact hnh_w
      | some cm =>
          rw [hs] at hr
          have hrem : ExactRun body cm c1 n := by
            refine ⟨hr, ?_⟩
            intro j hj ck hck
            have hck' : runFlatTM (j + 1) body c0 = some ck := by
              show (if haltingStateReached body c0 = true then some c0
                    else match stepFlatTM body c0 with
                      | none => some c0
                      | some cm' => runFlatTM j body cm') = some ck
              rw [hnh0, hs]; exact hck
            exact hrun.2 (j + 1) (by omega) ck hck'
          have h1 := ExactRun.step1 _ _ (shiftCfg 7 cm) hnh_w (by rw [hst, hs]; rfl)
          simpa [Nat.add_comm] using h1.trans (ih hrem)

lemma forEachTM7_bridge_exit (d k : ℕ) {body : FlatTM} {bodyExit : ℕ}
    (right : List ℕ) (h3 : currentTapeSymbol ([], 0, right) = some 3) :
    ExactRun (forEachTM7 d k body bodyExit)
      (shiftCfg 7 ⟨bodyExit, [([], 0, right)]⟩)
      ⟨2, [([], 1, right)]⟩ 1 := by
  have hnh : haltingStateReached (forEachTM7 d k body bodyExit) (shiftCfg 7 ⟨bodyExit, [([], 0, right)]⟩) = false := by
    cases hv : haltingStateReached (forEachTM7 d k body bodyExit) (shiftCfg 7 ⟨bodyExit, [([], 0, right)]⟩) with
    | false => rfl
    | true => rw [forEachTM7_halt_iff] at hv; simp [shiftCfg] at hv
  apply ExactRun.step1 _ _ _ hnh
  unfold stepFlatTM forEachTM7
  simp only [Option.bind_eq_bind]
  have hfind :
      ([ mk1 0 (some 3) 1 none .Rmove
       , mk1 1 (some 0) 6 none .Lmove
       , mk1 3 (some 0) 5 none .Lmove
       , mk1 4 (some 3) (7 + body.start) none .Nmove
       , mk1 5 (some 3) 6 none .Nmove
       , mk1 (7 + bodyExit) (some 3) 2 none .Rmove
       ]).find? (fun e => entryMatchesConfig e (shiftCfg 7 ⟨bodyExit, [([], 0, right)]⟩)) =
      some (mk1 (7 + bodyExit) (some 3) 2 none .Rmove) := by
    simp [List.find?, entryMatchesConfig, mk1, shiftCfg, h3, Nat.add_comm]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, list_find?_append_some _ _ _ hfind]
  simp [applyTransitionEntry, mk1, shiftCfg, tapeStep, writeCurrentTapeSymbol, moveTapeHead]

lemma forEachTM7_scan_zero (d k : ℕ) (body : FlatTM) (bodyExit : ℕ)
    (xs : List (Bool × ℕ)) (pre suf : List ℕ)
    (hok : ∀ bm ∈ xs, bm.2 < 2 ^ d ∧ (bm.2 / 2 ^ k) % 2 = 0 ∧ bm.2 + 2 ^ k < 2 ^ d) :
    ExactRun (forEachTM7 d k body bodyExit)
      ⟨2, [([], pre.length, pre ++ xs.map (fun bm => xSym bm.1 bm.2) ++ suf)]⟩
      ⟨2, [([], (pre ++ xs.map (fun bm => xSym bm.1 bm.2)).length,
        pre ++ xs.map (fun bm => xSym bm.1 bm.2) ++ suf)]⟩
      xs.length := by
  induction xs generalizing pre with
  | nil => simp; exact ExactRun.zero _ _
  | cons bm tl ih =>
      have hlen : (bm :: tl).length = 1 + tl.length := by simp; omega
      rw [hlen]
      have hbm := hok bm (List.mem_cons_self ..)
      have hmem : mk1 2 (some (xSym bm.1 bm.2)) 2 none .Rmove ∈ (forEachTM7 d k body bodyExit).trans := by
        simp only [forEachTM7, List.mem_append, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
          beq_iff_eq, decide_eq_true_eq, List.mem_cons]
        left; left; left; right
        exact ⟨bm, ⟨mem_allXSyms hbm.1, hbm.2.1, hbm.2.2⟩, Or.inr (Or.inl rfl)⟩
      have hcfg : pre ++ (bm :: tl).map (fun p => xSym p.1 p.2) ++ suf =
          pre ++ xSym bm.1 bm.2 :: (tl.map (fun p => xSym p.1 p.2) ++ suf) := by simp
      have h1 : ExactRun (forEachTM7 d k body bodyExit)
          ⟨2, [([], pre.length, pre ++ (bm :: tl).map (fun p => xSym p.1 p.2) ++ suf)]⟩
          ⟨2, [([], (pre ++ [xSym bm.1 bm.2]).length,
            (pre ++ [xSym bm.1 bm.2]) ++ tl.map (fun p => xSym p.1 p.2) ++ suf)]⟩ 1 := by
        rw [hcfg]
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
          forEachTM7_wrap_step d k body bodyExit 2 2 pre.length _ _ none .Rmove (by omega) hmem
            (currentTapeSymbol_at pre _ _)
      simpa [List.append_assoc] using h1.trans (ih (pre ++ [xSym bm.1 bm.2]) (fun p hp => hok p (List.mem_cons_of_mem bm hp)))

lemma forEachTM7_rewind (d k : ℕ) (body : FlatTM) (bodyExit : ℕ) (st : ℕ) (hst : st = 4 ∨ st = 5)
    (xs : List (Bool × ℕ)) (suf : List ℕ)
    (hxs : ∀ bm ∈ xs, bm.2 < 2 ^ d) :
    ExactRun (forEachTM7 d k body bodyExit)
      ⟨st, [([], xs.length, 3 :: (xs.map (fun bm => xSym bm.1 bm.2) ++ suf))]⟩
      ⟨st, [([], 0, 3 :: (xs.map (fun bm => xSym bm.1 bm.2) ++ suf))]⟩
      xs.length := by
  induction xs using List.reverseRecOn generalizing suf with
  | nil => simp; exact ExactRun.zero _ _
  | append_singleton init bm ih =>
      have hlen : (init ++ [bm]).length = 1 + init.length := by simp; omega
      rw [hlen]
      have hbm : bm.2 < 2 ^ d := hxs bm (by simp)
      have hmem : mk1 st (some (xSym bm.1 bm.2)) st none .Lmove ∈ (forEachTM7 d k body bodyExit).trans := by
        simp only [forEachTM7, List.mem_append, List.mem_flatMap, List.mem_cons]
        left; right
        refine ⟨bm, mem_allXSyms hbm, ?_⟩
        rcases hst with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr (Or.inl rfl)]
      have hcfg : 3 :: ((init ++ [bm]).map (fun p => xSym p.1 p.2) ++ suf) =
          (3 :: init.map (fun p => xSym p.1 p.2)) ++ xSym bm.1 bm.2 :: suf := by
        simp [List.append_assoc]
      have hidx : (init ++ [bm]).length = (3 :: init.map (fun p => xSym p.1 p.2)).length := by simp
      have h1 : ExactRun (forEachTM7 d k body bodyExit)
          ⟨st, [([], (init ++ [bm]).length, 3 :: ((init ++ [bm]).map (fun p => xSym p.1 p.2) ++ suf))]⟩
          ⟨st, [([], init.length, 3 :: (init.map (fun p => xSym p.1 p.2) ++ (xSym bm.1 bm.2 :: suf)))]⟩ 1 := by
        rw [hcfg, hidx]
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
          forEachTM7_wrap_step d k body bodyExit st st (3 :: init.map (fun p => xSym p.1 p.2)).length _ _ none .Lmove
            (by rcases hst with rfl | rfl <;> omega) hmem (currentTapeSymbol_at _ _ suf)
      simpa [List.append_assoc, Nat.add_comm] using h1.trans (ih (xSym bm.1 bm.2 :: suf) (fun p hp => hxs p (by simp [hp])))

def forEachCounter {d k : ℕ} (hk : k < d) {K : ℕ → ℕ} {T : ℕ → ℕ → ℕ}
    (body : CounterSpec d k K T) :
    CounterSpec d (k + 1) (fun n => n * K n) (fun n m => n * (T n m + 2 * n + 6) + 4) where
  M := forEachTM7 d k body.M body.exit
  exit := 6
  hSig := rfl
  hTapes := rfl
  hValid := forEachTM7_valid d k hk body.M body.exit body.hSig body.hTapes body.hValid body.hExitLt
  hExitLt := by simp [forEachTM7]; omega
  hNoExitTrans := fun e he => by
    simp only [forEachTM7, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_filter, List.mem_map] at he
    rcases he with ((((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨_, _, hr⟩) | ⟨_, _, rfl⟩) | ⟨_, _, hr⟩) | ⟨_, _, rfl⟩
    · simp [mk1]
    · simp [mk1]
    · simp [mk1]
    · simp [mk1]
    · simp [mk1]
    · simp [mk1]; omega
    · rcases hr with rfl | rfl | rfl <;> simp [mk1]
    · simp [mk1]
    · rcases hr with rfl | rfl <;> simp [mk1]
    · simp [shiftEntry]
  hHaltIff := forEachTM7_halt_iff d k body.M body.exit
  hRun := fun xs u c hok hu => by
    let sufC (v : ℕ) : List ℕ := [0] ++ (c.take v).map cMark ++ (c.drop v).map cUnmark ++ [0, 3]
    have hloop : ∀ (rest : List (Bool × ℕ)) (pre : List (Bool × ℕ)) (cur : Bool × ℕ) (u' : ℕ),
        MaskOK d (k + 1) (pre ++ cur :: rest) → u' ≤ c.length →
        ∃ t ≤ (rest.length + 1) * (T (pre.length + 1 + rest.length) c.length + 2 * (pre.length + 1 + rest.length) + 6),
          ExactRun (forEachTM7 d k body.M body.exit)
            (shiftCfg 7 ⟨body.M.start, [([], 0, lenTape (pre ++ (cur.1, cur.2 + 2 ^ k) :: rest) u' c)]⟩)
            ⟨6, [([], 0, lenTape (pre ++ cur :: rest) (min (u' + (rest.length + 1) * K (pre.length + 1 + rest.length)) c.length) c)]⟩
            t := by
      intro rest
      induction rest with
      | nil =>
          intro pre cur u' hok' hu'
          have hcur_ok := hok' cur (by simp)
          have hbit := bit_set_props hcur_ok.1 hk (hcur_ok.2 k (by omega))
          let xsM := pre ++ [(cur.1, cur.2 + 2 ^ k)]
          have hxsM_len : xsM.length = pre.length + 1 + 0 := by simp [xsM]
          have hxsM_ok : MaskOK d k xsM := by
            intro bm hbm
            simp only [xsM, List.mem_append, List.mem_singleton] at hbm
            rcases hbm with hp | rfl
            · exact ⟨(hok' bm (by simp [hp])).1, fun j hj => (hok' bm (by simp [hp])).2 j (by omega)⟩
            · exact ⟨hbit.1, fun j hj => by rw [hbit.2.2 j hj]; exact hcur_ok.2 j (by omega)⟩
          obtain ⟨tb, htb, hrb⟩ := body.hRun xsM u' c hxsM_ok hu'
          let u1 := min (u' + K xsM.length) c.length
          have hl1 := forEachTM7_lift_body d k body.hHaltIff hrb
          have hbr := forEachTM7_bridge_exit d k (body := body.M) (bodyExit := body.exit)
            (lenTape xsM u1 c) (currentTapeSymbol_at [] 3 _)
          have hlenM : lenTape xsM u1 c =
              [3] ++ pre.map (fun bm => xSym bm.1 bm.2) ++ xSym cur.1 (cur.2 + 2 ^ k) :: sufC u1 := by
            simp [lenTape, xsM, sufC, List.append_assoc]
          have hbr' : ExactRun (forEachTM7 d k body.M body.exit)
              (shiftCfg 7 ⟨body.exit, [([], 0, lenTape xsM u1 c)]⟩)
              ⟨2, [([], ([3] : List ℕ).length,
                [3] ++ pre.map (fun bm => xSym bm.1 bm.2) ++ xSym cur.1 (cur.2 + 2 ^ k) :: sufC u1)]⟩ 1 := by
            rw [← hlenM]; exact hbr
          -- Scan pre (all bit k = 0)
          have hpre_ok : ∀ bm ∈ pre, bm.2 < 2 ^ d ∧ (bm.2 / 2 ^ k) % 2 = 0 ∧ bm.2 + 2 ^ k < 2 ^ d := by
            intro bm hbm
            have hb := hok' bm (by simp [hbm])
            exact ⟨hb.1, hb.2 k (by omega), (bit_set_props hb.1 hk (hb.2 k (by omega))).1⟩
          have hsc := forEachTM7_scan_zero d k body.M body.exit pre [3]
            (xSym cur.1 (cur.2 + 2 ^ k) :: sufC u1) hpre_ok
          -- Clear bit k on cur and move R to 0 (state 3)
          let preL := [3] ++ pre.map (fun bm => xSym bm.1 bm.2)
          have hclr_mem : mk1 2 (some (xSym cur.1 (cur.2 + 2 ^ k))) 3 (some (xSym cur.1 cur.2)) .Rmove ∈
              (forEachTM7 d k body.M body.exit).trans := by
            simp only [forEachTM7, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
            left; left; right
            refine ⟨(cur.1, cur.2 + 2 ^ k), ⟨mem_allXSyms hbit.1, hbit.2.1⟩, ?_⟩
            simp [mk1]
          have hclr : ExactRun (forEachTM7 d k body.M body.exit)
              ⟨2, [([], preL.length, preL ++ xSym cur.1 (cur.2 + 2 ^ k) :: sufC u1)]⟩
              ⟨3, [([], (preL ++ [xSym cur.1 cur.2]).length, (preL ++ [xSym cur.1 cur.2]) ++ sufC u1)]⟩ 1 := by
            have hs := forEachTM7_wrap_step d k body.M body.exit 2 3 preL.length
              (preL ++ xSym cur.1 (cur.2 + 2 ^ k) :: sufC u1) (some (xSym cur.1 (cur.2 + 2 ^ k)))
              (some (xSym cur.1 cur.2)) .Rmove (by omega) hclr_mem
              (currentTapeSymbol_at preL (xSym cur.1 (cur.2 + 2 ^ k)) (sufC u1))
            rw [tapeStep_write_at] at hs
            simpa [moveTapeHead, List.append_assoc] using hs
          -- State 3 reads 0 -> move L to state 5
          have h0_mem : mk1 3 (some 0) 5 none .Lmove ∈ (forEachTM7 d k body.M body.exit).trans := by
            simp [forEachTM7]
          have h3to5 : ExactRun (forEachTM7 d k body.M body.exit)
              ⟨3, [([], (preL ++ [xSym cur.1 cur.2]).length, (preL ++ [xSym cur.1 cur.2]) ++ sufC u1)]⟩
              ⟨5, [([], (pre ++ [cur]).length, 3 :: ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++ sufC u1))]⟩ 1 := by
            have hs := forEachTM7_wrap_step d k body.M body.exit 3 5 (preL ++ [xSym cur.1 cur.2]).length
              ((preL ++ [xSym cur.1 cur.2]) ++ 0 :: ((c.take u1).map cMark ++ (c.drop u1).map cUnmark ++ [0, 3]))
              (some 0) none .Lmove (by omega) h0_mem (currentTapeSymbol_at (preL ++ [xSym cur.1 cur.2]) 0 _)
            simpa [preL, sufC, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
          -- State 5 rewinds across (pre ++ [cur]) to cell 0
          have hrew := forEachTM7_rewind d k body.M body.exit 5 (Or.inr rfl) (pre ++ [cur]) (sufC u1)
            (fun bm hbm => (hok' bm (by simpa using hbm)).1)
          -- State 5 at cell 0 reading 3 -> halt state 6
          have h5to6 : ExactRun (forEachTM7 d k body.M body.exit)
              ⟨5, [([], 0, 3 :: ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++ sufC u1))]⟩
              ⟨6, [([], 0, lenTape (pre ++ [cur]) u1 c)]⟩ 1 := by
            have hmem : mk1 5 (some 3) 6 none .Nmove ∈ (forEachTM7 d k body.M body.exit).trans := by
              simp [forEachTM7]
            have hs := forEachTM7_wrap_step d k body.M body.exit 5 6 0
              ([] ++ 3 :: ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++ sufC u1)) (some 3) none .Nmove (by omega) hmem
              (currentTapeSymbol_at [] 3 ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++ sufC u1))
            simpa [lenTape, sufC, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
          have htot := (((((hl1.trans hbr').trans hsc).trans hclr).trans h3to5).trans hrew).trans h5to6
          refine ⟨tb + 1 + pre.length + 1 + 1 + (pre ++ [cur]).length + 1, ?_, ?_⟩
          · rw [hxsM_len] at htb
            simp only [List.length_nil, List.length_append, List.length_singleton]
            omega
          · simpa [u1, hxsM_len] using htot
      | cons nxt tl ih =>
          intro pre cur u' hok' hu'
          have hcur_ok := hok' cur (by simp)
          have hnxt_ok := hok' nxt (by simp)
          have hbitC := bit_set_props hcur_ok.1 hk (hcur_ok.2 k (by omega))
          have hbitN := bit_set_props hnxt_ok.1 hk (hnxt_ok.2 k (by omega))
          let xsM := pre ++ (cur.1, cur.2 + 2 ^ k) :: nxt :: tl
          have hxsM_len : xsM.length = pre.length + 1 + (nxt :: tl).length := by simp [xsM]; omega
          have hxsM_ok : MaskOK d k xsM := by
            intro bm hbm
            simp only [xsM, List.mem_append, List.mem_cons] at hbm
            rcases hbm with hp | rfl | hnt
            · exact ⟨(hok' bm (by simp [hp])).1, fun j hj => (hok' bm (by simp [hp])).2 j (by omega)⟩
            · exact ⟨hbitC.1, fun j hj => by rw [hbitC.2.2 j hj]; exact hcur_ok.2 j (by omega)⟩
            · exact ⟨(hok' bm (by simp [hnt])).1, fun j hj => (hok' bm (by simp [hnt])).2 j (by omega)⟩
          obtain ⟨tb, htb, hrb⟩ := body.hRun xsM u' c hxsM_ok hu'
          let u1 := min (u' + K xsM.length) c.length
          have hu1_le : u1 ≤ c.length := Nat.min_le_right _ _
          have hl1 := forEachTM7_lift_body d k body.hHaltIff hrb
          have hbr := forEachTM7_bridge_exit d k (body := body.M) (bodyExit := body.exit)
            (lenTape xsM u1 c) (currentTapeSymbol_at [] 3 _)
          have hpre_ok : ∀ bm ∈ pre, bm.2 < 2 ^ d ∧ (bm.2 / 2 ^ k) % 2 = 0 ∧ bm.2 + 2 ^ k < 2 ^ d := by
            intro bm hbm
            have hb := hok' bm (by simp [hbm])
            exact ⟨hb.1, hb.2 k (by omega), (bit_set_props hb.1 hk (hb.2 k (by omega))).1⟩
          let tlMaps := tl.map (fun bm => xSym bm.1 bm.2)
          have hlenM : lenTape xsM u1 c =
              [3] ++ pre.map (fun bm => xSym bm.1 bm.2) ++
                (xSym cur.1 (cur.2 + 2 ^ k) :: xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1)) := by
            simp [lenTape, xsM, tlMaps, sufC, List.append_assoc]
          have hbr' : ExactRun (forEachTM7 d k body.M body.exit)
              (shiftCfg 7 ⟨body.exit, [([], 0, lenTape xsM u1 c)]⟩)
              ⟨2, [([], ([3] : List ℕ).length,
                [3] ++ pre.map (fun bm => xSym bm.1 bm.2) ++
                  (xSym cur.1 (cur.2 + 2 ^ k) :: xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1)))]⟩ 1 := by
            rw [← hlenM]; exact hbr
          have hsc := forEachTM7_scan_zero d k body.M body.exit pre [3]
            (xSym cur.1 (cur.2 + 2 ^ k) :: xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1)) hpre_ok
          let preL := [3] ++ pre.map (fun bm => xSym bm.1 bm.2)
          have hclr_mem : mk1 2 (some (xSym cur.1 (cur.2 + 2 ^ k))) 3 (some (xSym cur.1 cur.2)) .Rmove ∈
              (forEachTM7 d k body.M body.exit).trans := by
            simp only [forEachTM7, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
            left; left; right
            refine ⟨(cur.1, cur.2 + 2 ^ k), ⟨mem_allXSyms hbitC.1, hbitC.2.1⟩, by simp [mk1]⟩
          have hclr : ExactRun (forEachTM7 d k body.M body.exit)
              ⟨2, [([], preL.length, preL ++ xSym cur.1 (cur.2 + 2 ^ k) :: xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1))]⟩
              ⟨3, [([], (preL ++ [xSym cur.1 cur.2]).length,
                (preL ++ [xSym cur.1 cur.2]) ++ xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1))]⟩ 1 := by
            have hs := forEachTM7_wrap_step d k body.M body.exit 2 3 preL.length
              (preL ++ xSym cur.1 (cur.2 + 2 ^ k) :: xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1))
              (some (xSym cur.1 (cur.2 + 2 ^ k)))
              (some (xSym cur.1 cur.2)) .Rmove (by omega) hclr_mem
              (currentTapeSymbol_at preL (xSym cur.1 (cur.2 + 2 ^ k)) (xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1)))
            rw [tapeStep_write_at] at hs
            simpa [moveTapeHead, List.append_assoc] using hs
          -- State 3 reads nxt -> set bit k on nxt, move L to state 4
          have hset_mem : mk1 3 (some (xSym nxt.1 nxt.2)) 4 (some (xSym nxt.1 (nxt.2 + 2 ^ k))) .Lmove ∈
              (forEachTM7 d k body.M body.exit).trans := by
            simp only [forEachTM7, List.mem_append, List.mem_flatMap, List.mem_filter,
              Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false]
            left; left; left; right
            exact ⟨nxt, ⟨mem_allXSyms hnxt_ok.1, hnxt_ok.2 k (by omega), hbitN.1⟩, Or.inr (Or.inr rfl)⟩
          have h3to4 : ExactRun (forEachTM7 d k body.M body.exit)
              ⟨3, [([], (preL ++ [xSym cur.1 cur.2]).length,
                (preL ++ [xSym cur.1 cur.2]) ++ xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1))]⟩
              ⟨4, [([], (pre ++ [cur]).length,
                3 :: ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++
                  (xSym nxt.1 (nxt.2 + 2 ^ k) :: (tlMaps ++ sufC u1))))]⟩ 1 := by
            have hs := forEachTM7_wrap_step d k body.M body.exit 3 4 (preL ++ [xSym cur.1 cur.2]).length
              ((preL ++ [xSym cur.1 cur.2]) ++ xSym nxt.1 nxt.2 :: (tlMaps ++ sufC u1))
              (some (xSym nxt.1 nxt.2))
              (some (xSym nxt.1 (nxt.2 + 2 ^ k))) .Lmove (by omega) hset_mem
              (currentTapeSymbol_at (preL ++ [xSym cur.1 cur.2]) (xSym nxt.1 nxt.2) (tlMaps ++ sufC u1))
            rw [tapeStep_write_at] at hs
            simpa [preL, moveTapeHead, List.append_assoc] using hs
          -- Rewind state 4 across (pre ++ [cur]) to cell 0
          have hrew := forEachTM7_rewind d k body.M body.exit 4 (Or.inl rfl) (pre ++ [cur])
            (xSym nxt.1 (nxt.2 + 2 ^ k) :: (tlMaps ++ sufC u1))
            (fun bm hbm => (hok' bm (by simp at hbm ⊢; rcases hbm with h | rfl <;> [exact Or.inl h; exact Or.inr (Or.inl rfl)])).1)
          -- State 4 at cell 0 reading 3 -> 7 + body.start
          have h4toB : ExactRun (forEachTM7 d k body.M body.exit)
              ⟨4, [([], 0, 3 :: ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++
                (xSym nxt.1 (nxt.2 + 2 ^ k) :: (tlMaps ++ sufC u1))))]⟩
              (shiftCfg 7 ⟨body.M.start, [([], 0, lenTape ((pre ++ [cur]) ++ (nxt.1, nxt.2 + 2 ^ k) :: tl) u1 c)]⟩) 1 := by
            have hmem : mk1 4 (some 3) (7 + body.M.start) none .Nmove ∈ (forEachTM7 d k body.M body.exit).trans := by
              simp [forEachTM7]
            have hs := forEachTM7_wrap_step d k body.M body.exit 4 (7 + body.M.start) 0
              ([] ++ 3 :: ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++
                (xSym nxt.1 (nxt.2 + 2 ^ k) :: (tlMaps ++ sufC u1))))
              (some 3) none .Nmove (by omega) hmem
              (currentTapeSymbol_at [] 3 ((pre ++ [cur]).map (fun bm => xSym bm.1 bm.2) ++
                (xSym nxt.1 (nxt.2 + 2 ^ k) :: (tlMaps ++ sufC u1))))
            simpa [lenTape, tlMaps, sufC, shiftCfg, Nat.add_comm, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
          -- Inductive hypothesis on (pre ++ [cur]), nxt, tl
          have hok_next : MaskOK d (k + 1) ((pre ++ [cur]) ++ nxt :: tl) := by
            simpa [List.append_assoc] using hok'
          obtain ⟨t_ih, ht_ih, hr_ih⟩ := ih (pre ++ [cur]) nxt u1 hok_next hu1_le
          have htot := ((((((hl1.trans hbr').trans hsc).trans hclr).trans h3to4).trans hrew).trans h4toB).trans hr_ih
          have hlen_eq : (pre ++ [cur]).length + 1 + tl.length = pre.length + 1 + (nxt :: tl).length := by
            simp; omega
          have hmin_eq : min (u1 + (tl.length + 1) * K ((pre ++ [cur]).length + 1 + tl.length)) c.length =
              min (u' + ((nxt :: tl).length + 1) * K (pre.length + 1 + (nxt :: tl).length)) c.length := by
            simp only [u1, hxsM_len, hlen_eq, List.length_cons]
            have hmul : (tl.length + 1 + 1) * K (pre.length + 1 + (tl.length + 1)) =
                K (pre.length + 1 + (tl.length + 1)) + (tl.length + 1) * K (pre.length + 1 + (tl.length + 1)) := by ring
            omega
          refine ⟨tb + 1 + pre.length + 1 + 1 + (pre ++ [cur]).length + 1 + t_ih, ?_, ?_⟩
          · rw [hxsM_len] at htb
            rw [hlen_eq] at ht_ih
            simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil] at htb ht_ih ⊢
            have h1 : (tl.length + 1 + 1) * (T (pre.length + 1 + (tl.length + 1)) c.length +
                2 * (pre.length + 1 + (tl.length + 1)) + 6) =
                (T (pre.length + 1 + (tl.length + 1)) c.length + 2 * (pre.length + 1 + (tl.length + 1)) + 6) +
                (tl.length + 1) * (T (pre.length + 1 + (tl.length + 1)) c.length +
                2 * (pre.length + 1 + (tl.length + 1)) + 6) := by ring
            omega
          · rw [hmin_eq] at htot
            simpa [List.append_assoc] using htot
    -- Outer start from state 0 at cell 0
    have h0to1 : ExactRun (forEachTM7 d k body.M body.exit)
        ⟨0, [([], 0, lenTape xs u c)]⟩ ⟨1, [([], 1, lenTape xs u c)]⟩ 1 := by
      have hmem : mk1 0 (some 3) 1 none .Rmove ∈ (forEachTM7 d k body.M body.exit).trans := by
        simp [forEachTM7]
      simpa [lenTape, tapeStep, writeCurrentTapeSymbol, moveTapeHead] using
        forEachTM7_wrap_step d k body.M body.exit 0 1 0 (lenTape xs u c) _ none .Rmove (by omega) hmem
          (currentTapeSymbol_at [] 3 _)
    cases xs with
    | nil =>
        have h1to6 : ExactRun (forEachTM7 d k body.M body.exit)
            ⟨1, [([], 1, lenTape [] u c)]⟩ ⟨6, [([], 0, lenTape [] u c)]⟩ 1 := by
          have hmem : mk1 1 (some 0) 6 none .Lmove ∈ (forEachTM7 d k body.M body.exit).trans := by
            simp [forEachTM7]
          have hcur : currentTapeSymbol ([], 1, lenTape [] u c) = some 0 := by
            simpa [lenTape, List.append_assoc] using currentTapeSymbol_at [3] 0 ((c.take u).map cMark ++ ((c.drop u).map cUnmark ++ [0, 3]))
          simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead] using
            forEachTM7_wrap_step d k body.M body.exit 1 6 1 (lenTape [] u c) _ none .Lmove (by omega) hmem hcur
        have hmin : min u c.length = u := by omega
        refine ⟨2, by omega, ?_⟩
        simpa [forEachTM7, hmin] using h0to1.trans h1to6
    | cons hd tl =>
        have hhd := hok hd (List.mem_cons_self ..)
        have hbit := bit_set_props hhd.1 hk (hhd.2 k (by omega))
        have hset_mem : mk1 1 (some (xSym hd.1 hd.2)) (7 + body.M.start) (some (xSym hd.1 (hd.2 + 2 ^ k))) .Lmove ∈
            (forEachTM7 d k body.M body.exit).trans := by
          simp only [forEachTM7, List.mem_append, List.mem_flatMap, List.mem_filter,
            Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_cons]
          left; left; left; right
          exact ⟨hd, ⟨mem_allXSyms hhd.1, hhd.2 k (by omega), hbit.1⟩, Or.inl rfl⟩
        have h1toB : ExactRun (forEachTM7 d k body.M body.exit)
            ⟨1, [([], 1, lenTape (hd :: tl) u c)]⟩
            (shiftCfg 7 ⟨body.M.start, [([], 0, lenTape ([] ++ (hd.1, hd.2 + 2 ^ k) :: tl) u c)]⟩) 1 := by
          have hcfg : lenTape (hd :: tl) u c =
              [3] ++ xSym hd.1 hd.2 :: (tl.map (fun bm => xSym bm.1 bm.2) ++ sufC u) := by
            simp [lenTape, sufC, List.append_assoc]
          have hs := forEachTM7_wrap_step d k body.M body.exit 1 (7 + body.M.start) ([3] : List ℕ).length
            ([3] ++ xSym hd.1 hd.2 :: (tl.map (fun bm => xSym bm.1 bm.2) ++ sufC u))
            _ (some (xSym hd.1 (hd.2 + 2 ^ k))) .Lmove (by omega) hset_mem
            (currentTapeSymbol_at [3] _ _)
          rw [tapeStep_write_at] at hs
          rw [hcfg]
          simpa [lenTape, sufC, shiftCfg, Nat.add_comm, moveTapeHead, List.append_assoc] using hs
        obtain ⟨tlp, htlp, hrlp⟩ := hloop tl [] hd u (by simpa using hok) hu
        refine ⟨1 + 1 + tlp, ?_, ?_⟩
        · simp only [List.length_nil, List.length_cons, Nat.zero_add] at htlp ⊢
          have h1 : 1 + tl.length = tl.length + 1 := by omega
          rw [h1] at htlp; omega
        · have htot := (h0to1.trans h1toB).trans hrlp
          simp only [List.length_nil, List.length_cons, Nat.zero_add, List.nil_append] at htot ⊢
          have h1 : 1 + tl.length = tl.length + 1 := by omega
          rw [h1] at htot; exact htot

/-! ### 2e. Power & polynomial counter machines -/

def powTime : ℕ → ℕ → ℕ → ℕ
  | 0, n, m => 2 * (n + m) + 6
  | j + 1, n, m => n * (powTime j n m + 2 * n + 6) + 4

lemma powTime_mono (j : ℕ) {n₁ n₂ m₁ m₂ : ℕ} (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) :
    powTime j n₁ m₁ ≤ powTime j n₂ m₂ := by
  induction j with
  | zero => simp only [powTime]; omega
  | succ j ih =>
      simp only [powTime]
      have h1 : powTime j n₁ m₁ + 2 * n₁ + 6 ≤ powTime j n₂ m₂ + 2 * n₂ + 6 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul hn h1) 4

lemma powTime_inOPoly (j : ℕ) : inOPoly (fun s => powTime j s s) := by
  induction j with
  | zero =>
      exact inOPoly_of_le_poly (A := 4) (K := 1) (B := 6) (fun n => by simp [powTime]; omega)
  | succ j ih =>
      have h1 : inOPoly (fun s => powTime j s s + (2 * s + 6)) :=
        inOPoly_add ih (inOPoly_of_le_poly (A := 2) (K := 1) (B := 6) (fun n => by simp))
      have h2 : inOPoly (fun s => s * (powTime j s s + (2 * s + 6))) :=
        inOPoly_mul inOPoly_id h1
      have h3 : inOPoly (fun s => s * (powTime j s s + (2 * s + 6)) + 4) :=
        inOPoly_add h2 (inOPoly_const 4)
      refine inOPoly_le (fun s => ?_) h3
      simp only [powTime]
      have : powTime j s s + 2 * s + 6 = powTime j s s + (2 * s + 6) := by omega
      rw [this]

def markPowCounter (d : ℕ) : (j : ℕ) → j ≤ d → CounterSpec d j (fun n => n ^ j) (powTime j)
  | 0, _ =>
      { markOneCounter d with
        hRun := fun xs u c hok hu => by simpa [powTime] using (markOneCounter d).hRun xs u c hok hu }
  | j + 1, hjd =>
      let prev := markPowCounter d j (by omega)
      let res := forEachCounter (by omega : j < d) prev
      { res with
        hRun := fun xs u c hok hu => by
          obtain ⟨t, ht, hr⟩ := res.hRun xs u c hok hu
          refine ⟨t, ht, ?_⟩
          have hpow : xs.length ^ (j + 1) = xs.length * xs.length ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
          rwa [hpow] }

def polySumK (p : Polynomial ℕ) : ℕ → ℕ → ℕ
  | 0, _ => p.coeff 0 * 1
  | j + 1, n => polySumK p j n + p.coeff (j + 1) * n ^ (j + 1)

lemma polySumK_eq_eval (p : Polynomial ℕ) (n : ℕ) :
    polySumK p p.natDegree n = p.eval n := by
  have hsum : ∀ k : ℕ, polySumK p k n = ∑ i ∈ Finset.range (k + 1), p.coeff i * n ^ i := by
    intro k
    induction k with
    | zero => simp [polySumK]
    | succ j ih =>
        rw [polySumK, ih, ← Finset.sum_range_succ]
  rw [hsum p.natDegree, Polynomial.eval_eq_sum_range]

def polyTime (p : Polynomial ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, n, m => p.coeff 0 * (powTime 0 n m + 1)
  | j + 1, n, m => polyTime p j n m + 1 + p.coeff (j + 1) * (powTime (j + 1) n m + 1)

lemma polyTime_mono (p : Polynomial ℕ) (j : ℕ) {n₁ n₂ m₁ m₂ : ℕ} (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) :
    polyTime p j n₁ m₁ ≤ polyTime p j n₂ m₂ := by
  induction j with
  | zero =>
      simp only [polyTime]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (powTime_mono 0 hn hm) 1)
  | succ j ih =>
      simp only [polyTime]
      have h1 := Nat.mul_le_mul_left (p.coeff (j + 1)) (Nat.add_le_add_right (powTime_mono (j + 1) hn hm) 1)
      omega

lemma polyTime_inOPoly (p : Polynomial ℕ) (j : ℕ) : inOPoly (fun s => polyTime p j s s) := by
  induction j with
  | zero =>
      exact inOPoly_mul (inOPoly_const (p.coeff 0)) (inOPoly_add (powTime_inOPoly 0) (inOPoly_const 1))
  | succ j ih =>
      have hterm := inOPoly_mul (inOPoly_const (p.coeff (j + 1))) (inOPoly_add (powTime_inOPoly (j + 1)) (inOPoly_const 1))
      exact inOPoly_add (inOPoly_add ih (inOPoly_const 1)) hterm

def markPolyLoop (p : Polynomial ℕ) : (j : ℕ) → j ≤ p.natDegree →
    CounterSpec p.natDegree p.natDegree (polySumK p j) (polyTime p j)
  | 0, h0 =>
      let c0 := repeatCounter (p.coeff 0) ((markPowCounter p.natDegree 0 (by omega)).mono (Nat.zero_le _))
      { c0 with
        hRun := fun xs u c hok hu => by
          simpa [polySumK, polyTime] using c0.hRun xs u c hok hu }
  | j + 1, hjd =>
      let prev := markPolyLoop p j (by omega)
      let term := repeatCounter (p.coeff (j + 1)) ((markPowCounter p.natDegree (j + 1) hjd).mono hjd)
      let comb := seqCounter prev term
      { comb with
        hRun := fun xs u c hok hu => by
          simpa [polySumK, polyTime] using comb.hRun xs u c hok hu }

/-! ### 2f. `checkRestoreTM`: verify all `c` bits are marked, restore `4↦1, 5↦2`, rewind to 0 -/

def checkRestoreTM (d : ℕ) : FlatTM where
  sig := sigL d
  tapes := 1
  states := 6
  trans :=
    [ mk1 0 (some 3) 1 none .Rmove
    , mk1 1 (some 1) 1 none .Rmove
    , mk1 1 (some 2) 1 none .Rmove
    , mk1 1 (some 0) 2 none .Rmove
    , mk1 2 (some 4) 2 (some 1) .Rmove
    , mk1 2 (some 5) 2 (some 2) .Rmove
    , mk1 2 (some 0) 3 none .Lmove
    , mk1 2 (some 1) 5 none .Nmove
    , mk1 2 (some 2) 5 none .Nmove
    , mk1 3 (some 0) 3 none .Lmove
    , mk1 3 (some 1) 3 none .Lmove
    , mk1 3 (some 2) 3 none .Lmove
    , mk1 3 (some 3) 4 none .Nmove
    ]
  start := 0
  halt := [false, false, false, false, true, true]

lemma checkRestoreTM_valid (d : ℕ) : validFlatTM (checkRestoreTM d) := by
  have h6 : 6 ≤ sigL d := by unfold sigL; omega
  refine ⟨by simp [checkRestoreTM], rfl, ?_⟩
  intro e he
  simp only [checkRestoreTM, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (refine ⟨by simp [mk1, checkRestoreTM], by simp [mk1, checkRestoreTM], rfl, rfl, rfl, ?_, ?_⟩ <;>
    (intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; simp only [checkRestoreTM]; try omega))

lemma checkRestoreTM_halt_iff (d : ℕ) (cfg : FlatTMConfig) :
    haltingStateReached (checkRestoreTM d) cfg = true ↔ cfg.state_idx = 4 ∨ cfg.state_idx = 5 := by
  unfold haltingStateReached checkRestoreTM
  match cfg.state_idx with
  | 0 | 1 | 2 | 3 => simp
  | 4 | 5 => simp
  | n + 6 => simp

lemma checkRestoreTM_step (d st dst head : ℕ) (right : List ℕ) (rd wr : Option ℕ) (mv : TMMove)
    (hlt : st < 4)
    (hmem : mk1 st rd dst wr mv ∈ (checkRestoreTM d).trans)
    (hrd : currentTapeSymbol ([], head, right) = rd) :
    ExactRun (checkRestoreTM d) ⟨st, [([], head, right)]⟩ ⟨dst, [tapeStep ([], head, right) wr mv]⟩ 1 := by
  have hnh : haltingStateReached (checkRestoreTM d) ⟨st, [([], head, right)]⟩ = false := by
    cases hv : haltingStateReached (checkRestoreTM d) ⟨st, [([], head, right)]⟩ with
    | false => rfl
    | true => rw [checkRestoreTM_halt_iff] at hv; simp at hv; omega
  apply ExactRun.step1 _ _ _ hnh
  rw [stepFlatTM_of_unique (checkRestoreTM d) (mk1 st rd dst wr mv) _ hmem
      (by simp [entryMatchesConfig, mk1, hrd])]
  · simp [applyTransitionEntry, mk1]
  · intro e' he' hm
    simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    simp only [checkRestoreTM, List.mem_cons, List.not_mem_nil, or_false] at hmem he'
    rcases hmem with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [mk1, FlatTMTransEntry.mk.injEq, List.cons.injEq, and_true] at h1 hm ⊢;
     rcases h1 with ⟨rfl, rfl, rfl, rfl, rfl⟩;
     simp_all [hrd])

lemma checkRestore_scanX (d : ℕ) (x : List Bool) (pre suf : List ℕ) :
    ExactRun (checkRestoreTM d)
      ⟨1, [([], pre.length, pre ++ symbolsOf x ++ suf)]⟩
      ⟨1, [([], (pre ++ symbolsOf x).length, pre ++ symbolsOf x ++ suf)]⟩ x.length := by
  induction x generalizing pre with
  | nil => simp [symbolsOf]; exact ExactRun.zero _ _
  | cons b tl ih =>
      have hlen : (b :: tl).length = 1 + tl.length := by simp; omega
      rw [hlen]
      have h1 : ExactRun (checkRestoreTM d)
          ⟨1, [([], pre.length, pre ++ symbolsOf (b :: tl) ++ suf)]⟩
          ⟨1, [([], (pre ++ [if b then 2 else 1]).length, (pre ++ [if b then 2 else 1]) ++ symbolsOf tl ++ suf)]⟩ 1 := by
        cases b with
        | false =>
            have hmem : mk1 1 (some 1) 1 none .Rmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
            have hs := checkRestoreTM_step d 1 1 pre.length (pre ++ 1 :: (symbolsOf tl ++ suf)) _ none .Rmove (by omega)
              hmem (currentTapeSymbol_at pre 1 _)
            simpa [symbolsOf, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
        | true =>
            have hmem : mk1 1 (some 2) 1 none .Rmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
            have hs := checkRestoreTM_step d 1 1 pre.length (pre ++ 2 :: (symbolsOf tl ++ suf)) _ none .Rmove (by omega)
              hmem (currentTapeSymbol_at pre 2 _)
            simpa [symbolsOf, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using hs
      simpa [symbolsOf, List.append_assoc] using h1.trans (ih (pre ++ [if b then 2 else 1]))

lemma checkRestore_restoreC (d : ℕ) (cs : List Bool) (pre suf : List ℕ) :
    ExactRun (checkRestoreTM d)
      ⟨2, [([], pre.length, pre ++ cs.map cMark ++ suf)]⟩
      ⟨2, [([], (pre ++ symbolsOf cs).length, pre ++ symbolsOf cs ++ suf)]⟩ cs.length := by
  induction cs generalizing pre with
  | nil => simp [symbolsOf]; exact ExactRun.zero _ _
  | cons b tl ih =>
      have hlen : (b :: tl).length = 1 + tl.length := by simp; omega
      rw [hlen]
      have h1 : ExactRun (checkRestoreTM d)
          ⟨2, [([], pre.length, pre ++ (b :: tl).map cMark ++ suf)]⟩
          ⟨2, [([], (pre ++ [if b then 2 else 1]).length, (pre ++ [if b then 2 else 1]) ++ tl.map cMark ++ suf)]⟩ 1 := by
        cases b with
        | false =>
            have hmem : mk1 2 (some 4) 2 (some 1) .Rmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
            have hs := checkRestoreTM_step d 2 2 pre.length (pre ++ 4 :: (tl.map cMark ++ suf)) _ (some 1) .Rmove (by omega)
              hmem (currentTapeSymbol_at pre 4 _)
            rw [tapeStep_write_at] at hs
            simpa [cMark, moveTapeHead, List.append_assoc] using hs
        | true =>
            have hmem : mk1 2 (some 5) 2 (some 2) .Rmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
            have hs := checkRestoreTM_step d 2 2 pre.length (pre ++ 5 :: (tl.map cMark ++ suf)) _ (some 2) .Rmove (by omega)
              hmem (currentTapeSymbol_at pre 5 _)
            rw [tapeStep_write_at] at hs
            simpa [cMark, moveTapeHead, List.append_assoc] using hs
      simpa [symbolsOf, List.append_assoc] using h1.trans (ih (pre ++ [if b then 2 else 1]))

lemma checkRestore_rewind (d : ℕ) (mid suf : List ℕ) (hmid : ∀ s ∈ mid, s = 0 ∨ s = 1 ∨ s = 2) :
    ExactRun (checkRestoreTM d)
      ⟨3, [([], mid.length, 3 :: (mid ++ suf))]⟩ ⟨3, [([], 0, 3 :: (mid ++ suf))]⟩ mid.length := by
  induction mid using List.reverseRecOn generalizing suf with
  | nil => simp; exact ExactRun.zero _ _
  | append_singleton init s ih =>
      have hlen : (init ++ [s]).length = 1 + init.length := by simp; omega
      rw [hlen]
      have hmem : mk1 3 (some s) 3 none .Lmove ∈ (checkRestoreTM d).trans := by
        rcases hmid s (by simp) with rfl | rfl | rfl <;> simp [checkRestoreTM]
      have hcfg : 3 :: (init ++ [s] ++ suf) = (3 :: init) ++ s :: suf := by simp [List.append_assoc]
      have hidx : (init ++ [s]).length = (3 :: init).length := by simp
      have h1 : ExactRun (checkRestoreTM d)
          ⟨3, [([], (init ++ [s]).length, 3 :: (init ++ [s] ++ suf))]⟩
          ⟨3, [([], init.length, 3 :: (init ++ (s :: suf)))]⟩ 1 := by
        rw [hcfg, hidx]
        simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
          checkRestoreTM_step d 3 3 (3 :: init).length _ _ none .Lmove (by omega) hmem (currentTapeSymbol_at (3 :: init) s suf)
      simpa [List.append_assoc, Nat.add_comm] using h1.trans (ih (s :: suf) (fun z hz => hmid z (by simp [hz])))

lemma checkRestore_run (d : ℕ) (x c : List Bool) (u : ℕ) (hu : u ≤ c.length) :
    (u = c.length →
      ∃ t ≤ 2 * (x.length + c.length) + 6,
        ExactRun (checkRestoreTM d)
          ⟨0, [([], 0, lenTape (x.map (fun b => (b, 0))) u c)]⟩
          ⟨4, [([], 0, pairTape x c)]⟩ t) ∧
    (u < c.length →
      ∃ t ≤ 2 * (x.length + c.length) + 6, ∃ tp,
        ExactRun (checkRestoreTM d)
          ⟨0, [([], 0, lenTape (x.map (fun b => (b, 0))) u c)]⟩
          ⟨5, [tp]⟩ t) := by
  have hxmap : (x.map (fun b => (b, 0))).map (fun bm => xSym bm.1 bm.2) = symbolsOf x := by
    simp [symbolsOf, xSym_zero, List.map_map, Function.comp_def]
  have hltape : lenTape (x.map (fun b => (b, 0))) u c =
      [3] ++ symbolsOf x ++ (0 :: ((c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3])) := by
    simp [lenTape, hxmap, List.append_assoc]
  have h0 : ExactRun (checkRestoreTM d)
      ⟨0, [([], 0, lenTape (x.map (fun b => (b, 0))) u c)]⟩
      ⟨1, [([], 1, [3] ++ symbolsOf x ++ (0 :: ((c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3])))]⟩ 1 := by
    rw [hltape]
    have hmem : mk1 0 (some 3) 1 none .Rmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
    simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
      checkRestoreTM_step d 0 1 0 _ _ none .Rmove (by omega) hmem (currentTapeSymbol_at [] 3 _)
  have h1 := checkRestore_scanX d x [3] (0 :: ((c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3]))
  have h2 : ExactRun (checkRestoreTM d)
      ⟨1, [([], ([3] ++ symbolsOf x).length, ([3] ++ symbolsOf x) ++ 0 :: ((c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3]))]⟩
      ⟨2, [([], ([3] ++ symbolsOf x ++ [0]).length, ([3] ++ symbolsOf x ++ [0]) ++ (c.take u).map cMark ++ ((c.drop u).map cUnmark ++ [0, 3]))]⟩ 1 := by
    have hmem : mk1 1 (some 0) 2 none .Rmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
    have hs := checkRestoreTM_step d 1 2 ([3] ++ symbolsOf x).length
      (([3] ++ symbolsOf x) ++ 0 :: ((c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3]))
      (some 0) none .Rmove (by omega) hmem
      (currentTapeSymbol_at ([3] ++ symbolsOf x) 0 ((c.take u).map cMark ++ (c.drop u).map cUnmark ++ [0, 3]))
    simpa [tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.length_append, List.length_singleton, List.append_assoc] using hs
  have h3 := checkRestore_restoreC d (c.take u) ([3] ++ symbolsOf x ++ [0]) ((c.drop u).map cUnmark ++ [0, 3])
  have h03 := ((h0.trans h1).trans (by simpa [List.append_assoc] using h2)).trans (by simpa [List.append_assoc] using h3)
  constructor
  · intro heq
    subst heq
    have htk : c.take c.length = c := List.take_length
    have hdr : c.drop c.length = [] := List.drop_length
    let preAll := [3] ++ symbolsOf x ++ [0] ++ symbolsOf c
    have h4 : ExactRun (checkRestoreTM d)
        ⟨2, [([], preAll.length, preAll ++ 0 :: [3])]⟩
        ⟨3, [([], (symbolsOf x ++ [0] ++ symbolsOf c).length, 3 :: ((symbolsOf x ++ [0] ++ symbolsOf c) ++ [0, 3]))]⟩ 1 := by
      have hmem : mk1 2 (some 0) 3 none .Lmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
      simpa [preAll, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
        checkRestoreTM_step d 2 3 preAll.length _ _ none .Lmove (by omega) hmem (currentTapeSymbol_at preAll 0 [3])
    have hmid : ∀ s ∈ symbolsOf x ++ [0] ++ symbolsOf c, s = 0 ∨ s = 1 ∨ s = 2 := by
      intro s hs
      simp only [List.mem_append, List.mem_singleton, symbolsOf, List.mem_map] at hs
      rcases hs with (⟨b, _, rfl⟩ | rfl) | ⟨b, _, rfl⟩
      · cases b <;> simp
      · exact Or.inl rfl
      · cases b <;> simp
    have h5 := checkRestore_rewind d (symbolsOf x ++ [0] ++ symbolsOf c) [0, 3] hmid
    have h6 : ExactRun (checkRestoreTM d)
        ⟨3, [([], 0, 3 :: ((symbolsOf x ++ [0] ++ symbolsOf c) ++ [0, 3]))]⟩
        ⟨4, [([], 0, pairTape x c)]⟩ 1 := by
      have hmem : mk1 3 (some 3) 4 none .Nmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
      simpa [pairTape, tapeStep, writeCurrentTapeSymbol, moveTapeHead, List.append_assoc] using
        checkRestoreTM_step d 3 4 0 _ _ none .Nmove (by omega) hmem (currentTapeSymbol_at [] 3 _)
    have hdrop_map : (c.map cUnmark).drop c.length = [] := List.drop_eq_nil_of_le (by simp)
    rw [hdrop_map] at h03
    have htot := ((h03.trans (by simpa [preAll, List.append_assoc] using h4)).trans h5).trans h6
    refine ⟨_, ?_, htot⟩
    simp only [symbolsOf, List.length_append, List.length_map, List.length_take, List.length_singleton]
    omega
  · intro hlt
    have hdr : c.drop u = (c)[u] :: c.drop (u + 1) := list_drop_eq_cons c u hlt
    let preAll := [3] ++ symbolsOf x ++ [0] ++ symbolsOf (c.take u)
    have h4 : ∃ tp, ExactRun (checkRestoreTM d)
        ⟨2, [([], preAll.length, preAll ++ cUnmark (c)[u] :: ((c.drop (u + 1)).map cUnmark ++ [0, 3]))]⟩
        ⟨5, [tp]⟩ 1 := by
      cases hc : (c)[u] with
      | false =>
          have hmem : mk1 2 (some 1) 5 none .Nmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
          exact ⟨_, by simpa [cUnmark] using checkRestoreTM_step d 2 5 preAll.length _ _ none .Nmove (by omega) hmem (currentTapeSymbol_at preAll 1 _)⟩
      | true =>
          have hmem : mk1 2 (some 2) 5 none .Nmove ∈ (checkRestoreTM d).trans := by simp [checkRestoreTM]
          exact ⟨_, by simpa [cUnmark] using checkRestoreTM_step d 2 5 preAll.length _ _ none .Nmove (by omega) hmem (currentTapeSymbol_at preAll 2 _)⟩
    rcases h4 with ⟨tp, h4⟩
    have hdrop_map : (c.map cUnmark).drop u = cUnmark (c)[u] :: (c.drop (u + 1)).map cUnmark := by
      rw [← List.map_drop, hdr]; rfl
    rw [hdrop_map] at h03
    have htot := h03.trans (by simpa [preAll, List.append_assoc] using h4)
    refine ⟨_, ?_, tp, htot⟩
    omega

/-! ### 2g. Combine length-checker `(markPoly ; checkRestore)` with `simFlatTM M` -/

def combineTwoExit (LTM STM : FlatTM) (exitOk exitRej stmRej : ℕ) : FlatTM where
  sig := max LTM.sig STM.sig
  tapes := 1
  states := LTM.states + STM.states
  trans :=
    LTM.trans ++
    [ mk1 exitOk (some 3) (LTM.states + STM.start) none .Nmove ] ++
    ((List.range (max LTM.sig STM.sig)).map (fun v => mk1 exitRej (some v) (LTM.states + stmRej) none .Nmove)) ++
    [ mk1 exitRej none (LTM.states + stmRej) none .Nmove ] ++
    STM.trans.map (shiftEntry LTM.states)
  start := LTM.start
  halt := List.replicate LTM.states false ++ STM.halt

lemma combineTwoExit_valid (LTM STM : FlatTM) (exitOk exitRej stmRej : ℕ)
    (h1 : validFlatTM LTM) (h2 : validFlatTM STM) (ht1 : LTM.tapes = 1) (ht2 : STM.tapes = 1)
    (hok : exitOk < LTM.states) (hrej : exitRej < LTM.states) (hstmRej : stmRej < STM.states)
    (h3 : 3 < max LTM.sig STM.sig) :
    validFlatTM (combineTwoExit LTM STM exitOk exitRej stmRej) := by
  refine ⟨Nat.lt_of_lt_of_le h1.1 (Nat.le_add_right _ _), by simp [combineTwoExit, h2.2.1], ?_⟩
  intro e he
  simp only [combineTwoExit, List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at he
  rcases he with (((hm1 | rfl) | ⟨v, hv, rfl⟩) | rfl) | ⟨e', he', rfl⟩
  · have hv' := h1.2.2 e hm1
    refine ⟨Nat.lt_of_lt_of_le hv'.1 (Nat.le_add_right _ _),
            Nat.lt_of_lt_of_le hv'.2.1 (Nat.le_add_right _ _),
            hv'.2.2.1.trans ht1, hv'.2.2.2.1.trans ht1, hv'.2.2.2.2.1.trans ht1, ?_, ?_⟩
    · intro x hx; cases x with | none => trivial | some w => exact Nat.lt_of_lt_of_le (hv'.2.2.2.2.2.1 (some w) hx) (Nat.le_max_left _ _)
    · intro x hx; cases x with | none => trivial | some w => exact Nat.lt_of_lt_of_le (hv'.2.2.2.2.2.2 (some w) hx) (Nat.le_max_left _ _)
  · refine ⟨by simp [combineTwoExit, mk1]; omega, by simp [combineTwoExit, mk1]; have := h2.1; omega, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact h3
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; trivial
  · refine ⟨by simp [combineTwoExit, mk1]; omega, by simp [combineTwoExit, mk1]; omega, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; exact hv
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; trivial
  · refine ⟨by simp [combineTwoExit, mk1]; omega, by simp [combineTwoExit, mk1]; omega, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; trivial
    · intro x hx; simp only [mk1, List.mem_singleton] at hx; subst hx; trivial
  · have hv' := h2.2.2 e' he'
    refine ⟨by simp [combineTwoExit, shiftEntry]; have := hv'.1; omega, by simp [combineTwoExit, shiftEntry]; have := hv'.2.1; omega,
            hv'.2.2.1.trans ht2, hv'.2.2.2.1.trans ht2, hv'.2.2.2.2.1.trans ht2, ?_, ?_⟩
    · intro x hx; cases x with | none => trivial | some w => exact Nat.lt_of_lt_of_le (hv'.2.2.2.2.2.1 (some w) hx) (Nat.le_max_right _ _)
    · intro x hx; cases x with | none => trivial | some w => exact Nat.lt_of_lt_of_le (hv'.2.2.2.2.2.2 (some w) hx) (Nat.le_max_right _ _)

lemma combineTwoExit_halt_lt (LTM STM : FlatTM) (exitOk exitRej stmRej : ℕ) (cfg : FlatTMConfig)
    (hlt : cfg.state_idx < LTM.states) :
    haltingStateReached (combineTwoExit LTM STM exitOk exitRej stmRej) cfg = false := by
  unfold haltingStateReached combineTwoExit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt])]; simp [hlt]

lemma combineTwoExit_halt_shift (LTM STM : FlatTM) (exitOk exitRej stmRej : ℕ) (cfg : FlatTMConfig) :
    haltingStateReached (combineTwoExit LTM STM exitOk exitRej stmRej) (shiftCfg LTM.states cfg) =
    haltingStateReached STM cfg := by
  unfold haltingStateReached combineTwoExit shiftCfg
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_replicate]
  simp [List.getD_eq_getElem?_getD]

lemma combineTwoExit_liftL {LTM STM : FlatTM} {exitOk exitRej stmRej : ℕ}
    (h1 : validFlatTM LTM)
    (hHalt1 : ∀ cfg, haltingStateReached LTM cfg = true ↔ cfg.state_idx = exitOk ∨ cfg.state_idx = exitRej)
    {c0 c1 : FlatTMConfig} {t : ℕ}
    (h0 : c0.state_idx < LTM.states) (hrun : ExactRun LTM c0 c1 t) :
    runFlatTM t (combineTwoExit LTM STM exitOk exitRej stmRej) c0 = some c1 := by
  have hstep_eq : ∀ cfg : FlatTMConfig, cfg.state_idx < LTM.states →
      cfg.state_idx ≠ exitOk → cfg.state_idx ≠ exitRej →
      stepFlatTM (combineTwoExit LTM STM exitOk exitRej stmRej) cfg = stepFlatTM LTM cfg := by
    intro cfg hlt hne1 hne2
    unfold stepFlatTM combineTwoExit; simp only [Option.bind_eq_bind]
    cases hf : LTM.trans.find? (fun e => entryMatchesConfig e cfg) with
    | some e =>
        rw [List.append_assoc, List.append_assoc, List.append_assoc, list_find?_append_some _ _ _ hf]
    | none =>
        have hn1 : ∀ e ∈ LTM.trans, entryMatchesConfig e cfg = false := fun e he => by
          cases hv : entryMatchesConfig e cfg with | false => rfl | true => exact absurd hv (List.find?_eq_none.mp hf e he)
        have hnRest : ∀ e ∈ ([ mk1 exitOk (some 3) (LTM.states + STM.start) none .Nmove ] ++
            ((List.range (max LTM.sig STM.sig)).map (fun v => mk1 exitRej (some v) (LTM.states + stmRej) none .Nmove)) ++
            [ mk1 exitRej none (LTM.states + stmRej) none .Nmove ] ++
            STM.trans.map (shiftEntry LTM.states)), entryMatchesConfig e cfg = false := by
          intro e he
          simp only [List.mem_append, List.mem_singleton, List.mem_map] at he
          rcases he with ((rfl | ⟨v, _, rfl⟩) | rfl) | ⟨e', _, rfl⟩
          · simp [entryMatchesConfig, mk1, hne1.symm]
          · simp [entryMatchesConfig, mk1, hne2.symm]
          · simp [entryMatchesConfig, mk1, hne2.symm]
          · have : e'.src_state + LTM.states ≠ cfg.state_idx := by omega
            simp [entryMatchesConfig, shiftEntry, this]
        rw [List.append_assoc, List.append_assoc, List.append_assoc, list_find?_append_left _ _ _ hn1]
        have hf2 : ([ mk1 exitOk (some 3) (LTM.states + STM.start) none .Nmove ] ++
            ((List.range (max LTM.sig STM.sig)).map (fun v => mk1 exitRej (some v) (LTM.states + stmRej) none .Nmove)) ++
            [ mk1 exitRej none (LTM.states + stmRej) none .Nmove ] ++
            STM.trans.map (shiftEntry LTM.states)).find? (fun e => entryMatchesConfig e cfg) = none :=
          List.find?_eq_none.mpr (fun e he => by rw [hnRest e he]; decide)
        rw [← List.append_assoc, ← List.append_assoc, hf2]
  induction t generalizing c0 with
  | zero => exact hrun.1
  | succ n ih =>
      have hnh0 : haltingStateReached LTM c0 = false := hrun.2 0 (by omega) c0 rfl
      have hne1 : c0.state_idx ≠ exitOk := fun h => by have := (hHalt1 c0).mpr (Or.inl h); rw [hnh0] at this; cases this
      have hne2 : c0.state_idx ≠ exitRej := fun h => by have := (hHalt1 c0).mpr (Or.inr h); rw [hnh0] at this; cases this
      have hnhC := combineTwoExit_halt_lt LTM STM exitOk exitRej stmRej c0 h0
      have hst := hstep_eq c0 h0 hne1 hne2
      have hr := hrun.1
      change (if haltingStateReached LTM c0 = true then some c0
              else match stepFlatTM LTM c0 with | none => some c0 | some cm => runFlatTM n LTM cm) = some c1 at hr
      rw [hnh0] at hr
      show (if haltingStateReached (combineTwoExit LTM STM exitOk exitRej stmRej) c0 = true then some c0
            else match stepFlatTM (combineTwoExit LTM STM exitOk exitRej stmRej) c0 with
              | none => some c0 | some cm => runFlatTM n (combineTwoExit LTM STM exitOk exitRej stmRej) cm) = some c1
      rw [hnhC, hst]
      cases hs : stepFlatTM LTM c0 with
      | none => rw [hs] at hr; exact hr
      | some cm =>
          rw [hs] at hr
          have hcm_lt := ExactRun.state_lt h1 h0 (runFlatTM_step_one LTM c0 cm hnh0 hs)
          have hrem : ExactRun LTM cm c1 n := by
            refine ⟨hr, fun k hk ck hck => hrun.2 (k + 1) (by omega) ck ?_⟩
            show (if haltingStateReached LTM c0 = true then some c0
                  else match stepFlatTM LTM c0 with | none => some c0 | some cm' => runFlatTM k LTM cm') = some ck
            rw [hnh0, hs]; exact hck
          exact ih hcm_lt hrem

lemma combineTwoExit_liftS {LTM STM : FlatTM} {exitOk exitRej stmRej : ℕ}
    (h1 : validFlatTM LTM) (hok : exitOk < LTM.states) (hrej : exitRej < LTM.states)
    {c0 c1 : FlatTMConfig} {t : ℕ}
    (hrun : runFlatTM t STM c0 = some c1) :
    runFlatTM t (combineTwoExit LTM STM exitOk exitRej stmRej) (shiftCfg LTM.states c0) =
      some (shiftCfg LTM.states c1) := by
  have hstep_eq : ∀ cfg : FlatTMConfig,
      stepFlatTM (combineTwoExit LTM STM exitOk exitRej stmRej) (shiftCfg LTM.states cfg) =
      (stepFlatTM STM cfg).map (shiftCfg LTM.states) := by
    intro cfg
    unfold stepFlatTM combineTwoExit; simp only [Option.bind_eq_bind]
    have hnone_pre : ∀ e ∈ (LTM.trans ++
        [ mk1 exitOk (some 3) (LTM.states + STM.start) none .Nmove ] ++
        ((List.range (max LTM.sig STM.sig)).map (fun v => mk1 exitRej (some v) (LTM.states + stmRej) none .Nmove)) ++
        [ mk1 exitRej none (LTM.states + stmRej) none .Nmove ]),
        entryMatchesConfig e (shiftCfg LTM.states cfg) = false := by
      intro e he
      simp only [List.mem_append, List.mem_singleton, List.mem_map] at he
      rcases he with ((hm1 | rfl) | ⟨v, _, rfl⟩) | rfl
      · have := (h1.2.2 e hm1).1; have : e.src_state ≠ cfg.state_idx + LTM.states := by omega
        simp [entryMatchesConfig, shiftCfg, this]
      · have : exitOk ≠ cfg.state_idx + LTM.states := by omega
        simp [entryMatchesConfig, mk1, shiftCfg, this]
      · have : exitRej ≠ cfg.state_idx + LTM.states := by omega
        simp [entryMatchesConfig, mk1, shiftCfg, this]
      · have : exitRej ≠ cfg.state_idx + LTM.states := by omega
        simp [entryMatchesConfig, mk1, shiftCfg, this]
    rw [list_find?_append_left _ _ _ hnone_pre, list_find?_map_shift]
    cases hf : STM.trans.find? (fun e => entryMatchesConfig e cfg) with
    | none => rfl
    | some e =>
        simp only [Option.map_some, Option.bind_some]
        unfold applyTransitionEntry shiftEntry shiftCfg; dsimp only; split_ifs <;> simp
  induction t generalizing c0 with
  | zero =>
      have : c0 = c1 := Option.some.inj hrun; subst this; rfl
  | succ n ih =>
      change (if haltingStateReached STM c0 = true then some c0
              else match stepFlatTM STM c0 with | none => some c0 | some cm => runFlatTM n STM cm) = some c1 at hrun
      show (if haltingStateReached (combineTwoExit LTM STM exitOk exitRej stmRej) (shiftCfg LTM.states c0) = true
            then some (shiftCfg LTM.states c0)
            else match stepFlatTM (combineTwoExit LTM STM exitOk exitRej stmRej) (shiftCfg LTM.states c0) with
              | none => some (shiftCfg LTM.states c0)
              | some cm => runFlatTM n (combineTwoExit LTM STM exitOk exitRej stmRej) cm) = some (shiftCfg LTM.states c1)
      rw [combineTwoExit_halt_shift, hstep_eq]
      by_cases hh : haltingStateReached STM c0 = true
      · rw [if_pos hh] at hrun ⊢
        have : c0 = c1 := Option.some.inj hrun; subst this; rfl
      · rw [if_neg hh] at hrun ⊢
        cases hs : stepFlatTM STM c0 with
        | none =>
            rw [hs] at hrun
            simp only [Option.map_none]
            have : c0 = c1 := Option.some.inj hrun; subst this; rfl
        | some cm =>
            rw [hs] at hrun
            simp only [Option.map_some]
            exact ih hrun

lemma combineTwoExit_bridgeOk {LTM STM : FlatTM} {exitOk exitRej stmRej : ℕ}
    (hok : exitOk < LTM.states) (hno : ∀ e ∈ LTM.trans, e.src_state ≠ exitOk)
    (right : List ℕ) (h3 : currentTapeSymbol ([], 0, right) = some 3) :
    runFlatTM 1 (combineTwoExit LTM STM exitOk exitRej stmRej) ⟨exitOk, [([], 0, right)]⟩ =
      some (shiftCfg LTM.states ⟨STM.start, [([], 0, right)]⟩) := by
  apply runFlatTM_step_one _ _ _ (combineTwoExit_halt_lt LTM STM exitOk exitRej stmRej _ hok)
  unfold stepFlatTM combineTwoExit; simp only [Option.bind_eq_bind]
  have hn1 : ∀ e ∈ LTM.trans, entryMatchesConfig e ⟨exitOk, [([], 0, right)]⟩ = false := fun e he => by
    simp [entryMatchesConfig, hno e he]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, list_find?_append_left _ _ _ hn1]
  simp only [List.cons_append, List.nil_append, List.find?]
  have hm : entryMatchesConfig (mk1 exitOk (some 3) (LTM.states + STM.start) none .Nmove) ⟨exitOk, [([], 0, right)]⟩ = true := by
    simp [entryMatchesConfig, mk1, h3]
  rw [hm]
  simp [applyTransitionEntry, mk1, tapeStep, writeCurrentTapeSymbol, moveTapeHead, shiftCfg, Nat.add_comm]

lemma combineTwoExit_bridgeRej {LTM STM : FlatTM} {exitOk exitRej stmRej : ℕ}
    (hrej : exitRej < LTM.states) (hne : exitOk ≠ exitRej)
    (hno : ∀ e ∈ LTM.trans, e.src_state ≠ exitRej)
    (tp : List ℕ × ℕ × List ℕ)
    (hbnd : ∀ v, currentTapeSymbol tp = some v → v < max LTM.sig STM.sig) :
    runFlatTM 1 (combineTwoExit LTM STM exitOk exitRej stmRej) ⟨exitRej, [tp]⟩ =
      some (shiftCfg LTM.states ⟨stmRej, [tp]⟩) := by
  apply runFlatTM_step_one _ _ _ (combineTwoExit_halt_lt LTM STM exitOk exitRej stmRej _ hrej)
  unfold stepFlatTM combineTwoExit; simp only [Option.bind_eq_bind]
  have hn1 : ∀ e ∈ LTM.trans, entryMatchesConfig e ⟨exitRej, [tp]⟩ = false := fun e he => by
    simp [entryMatchesConfig, hno e he]
  have hnOk : entryMatchesConfig (mk1 exitOk (some 3) (LTM.states + STM.start) none .Nmove) ⟨exitRej, [tp]⟩ = false := by
    simp [entryMatchesConfig, mk1, hne]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, list_find?_append_left _ _ _ hn1]
  simp only [List.cons_append, List.nil_append, List.find?, hnOk]
  cases hcur : currentTapeSymbol tp with
  | none =>
      have hnRange : ∀ e ∈ (List.range (max LTM.sig STM.sig)).map
          (fun v => mk1 exitRej (some v) (LTM.states + stmRej) none .Nmove),
          entryMatchesConfig e ⟨exitRej, [tp]⟩ = false := by
        intro e he; rw [List.mem_map] at he; rcases he with ⟨v, _, rfl⟩
        simp [entryMatchesConfig, mk1, hcur]
      rw [list_find?_append_left _ _ _ hnRange]
      simp only [List.cons_append, List.nil_append, List.find?]
      have hm : entryMatchesConfig (mk1 exitRej none (LTM.states + stmRej) none .Nmove) ⟨exitRej, [tp]⟩ = true := by
        simp [entryMatchesConfig, mk1, hcur]
      rw [hm]
      simp [applyTransitionEntry, mk1, tapeStep, writeCurrentTapeSymbol, moveTapeHead, shiftCfg, Nat.add_comm]
  | some v =>
      have hv : v < max LTM.sig STM.sig := hbnd v hcur
      have hfind : ((List.range (max LTM.sig STM.sig)).map
          (fun w => mk1 exitRej (some w) (LTM.states + stmRej) none .Nmove)).find?
          (fun e => entryMatchesConfig e ⟨exitRej, [tp]⟩) =
          some (mk1 exitRej (some v) (LTM.states + stmRej) none .Nmove) := by
        apply find_entry_unique _ _ _
        · rw [List.mem_map]; exact ⟨v, List.mem_range.mpr hv, rfl⟩
        · simp [entryMatchesConfig, mk1, hcur]
        · intro e' he' hm
          rw [List.mem_map] at he'; rcases he' with ⟨w, _, rfl⟩
          simp [entryMatchesConfig, mk1, hcur] at hm
          rw [hm]
      rw [list_find?_append_some _ _ _ hfind]
      simp [applyTransitionEntry, mk1, tapeStep, writeCurrentTapeSymbol, moveTapeHead, shiftCfg, Nat.add_comm]

lemma tape_bounded_of_run {N : FlatTM} (hv : validFlatTM N) (ht : N.tapes = 1)
    {t : ℕ} {tp0 tp1 : List ℕ × ℕ × List ℕ} {s0 s1 : ℕ}
    (hb0 : ∀ x ∈ tp0.2.2, x < N.sig)
    (hrun : runFlatTM t N ⟨s0, [tp0]⟩ = some ⟨s1, [tp1]⟩) :
    ∀ x ∈ tp1.2.2, x < N.sig := by
  induction t generalizing s0 tp0 with
  | zero =>
      have : (⟨s0, [tp0]⟩ : FlatTMConfig) = ⟨s1, [tp1]⟩ := Option.some.inj hrun
      injection this with _ htp; injection htp with htp'; subst htp'; exact hb0
  | succ n ih =>
      change (if haltingStateReached N ⟨s0, [tp0]⟩ = true then some ⟨s0, [tp0]⟩
              else match stepFlatTM N ⟨s0, [tp0]⟩ with | none => some ⟨s0, [tp0]⟩ | some cm => runFlatTM n N cm) =
              some ⟨s1, [tp1]⟩ at hrun
      by_cases hh : haltingStateReached N ⟨s0, [tp0]⟩ = true
      · rw [if_pos hh] at hrun
        have : (⟨s0, [tp0]⟩ : FlatTMConfig) = ⟨s1, [tp1]⟩ := Option.some.inj hrun
        injection this with _ htp; injection htp with htp'; subst htp'; exact hb0
      · rw [if_neg hh] at hrun
        cases hs : stepFlatTM N ⟨s0, [tp0]⟩ with
        | none =>
            rw [hs] at hrun
            have : (⟨s0, [tp0]⟩ : FlatTMConfig) = ⟨s1, [tp1]⟩ := Option.some.inj hrun
            injection this with _ htp; injection htp with htp'; subst htp'; exact hb0
        | some cm =>
            rw [hs] at hrun
            unfold stepFlatTM at hs; simp only [Option.bind_eq_bind] at hs
            cases hf : N.trans.find? (fun e => entryMatchesConfig e ⟨s0, [tp0]⟩) with
            | none => rw [hf] at hs; cases hs
            | some e =>
                rw [hf] at hs
                have hev := hv.2.2 e (List.mem_of_find?_eq_some hf)
                have hdw : e.dst_write_vals.length = 1 := hev.2.2.2.1.trans ht
                have hmv : e.move_dirs.length = 1 := hev.2.2.2.2.1.trans ht
                rcases List.length_eq_one_iff.mp hdw with ⟨wr, hwr_eq⟩
                rcases List.length_eq_one_iff.mp hmv with ⟨mv, hmv_eq⟩
                unfold applyTransitionEntry at hs
                simp only [Option.bind_some, List.length_singleton, hdw, hmv, and_self, ↓reduceDIte, hwr_eq, hmv_eq,
                  List.zip_cons_cons, List.zip_nil_right, List.zipWith_cons_cons, List.zipWith_nil,
                  Option.some.injEq] at hs
                rw [← hs] at hrun
                have hb_next : ∀ x ∈ (tapeStep tp0 wr mv).2.2, x < N.sig := by
                  intro x hx
                  have hmv_eq2 : (tapeStep tp0 wr mv).2.2 = (writeCurrentTapeSymbol tp0 wr).2.2 := by
                    cases mv <;> rfl
                  rw [hmv_eq2] at hx
                  unfold writeCurrentTapeSymbol at hx
                  cases wr with
                  | none => exact hb0 x hx
                  | some w =>
                      have hw : w < N.sig := hev.2.2.2.2.2.2 (some w) (by simp [hwr_eq])
                      dsimp only at hx
                      split_ifs at hx
                      · simp only [List.mem_append, List.mem_cons] at hx
                        rcases hx with ht1 | rfl | hd1
                        · exact hb0 x (List.mem_of_mem_take ht1)
                        · exact hw
                        · exact hb0 x (List.mem_of_mem_drop hd1)
                      · simp only [List.mem_append, List.mem_singleton] at hx
                        rcases hx with h1 | rfl
                        · exact hb0 x h1
                        · exact hw
                      · exact hb0 x hx
                exact ih hb_next hrun

end LenCheck

end PvsNP.Units.m1_st_np_to_flat_np_aux

open CookLevin PvsNP.Units.m1_st_np_to_flat_np_aux

theorem PvsNP.Units.m1_st_np_to_flat_np :
    ∀ L : Language Bool, L ∈ PvsNP.SingleTape.NP → CookLevin.inNP (fun x => x ∈ L) := by
  intro L hL
  rcases hL with ⟨V, p, ⟨M, qPoly, hM⟩, hVspec⟩
  obtain ⟨A, K, B, hp⟩ := poly_eval_le p
  obtain ⟨Aq, Kq, Bq, hq⟩ := poly_eval_le qPoly
  let d := p.natDegree
  let PTM := markPolyLoop p d (le_refl d)
  let RTM := checkRestoreTM d
  let LTM := seqTM PTM.M RTM PTM.exit
  let STM := simFlatTM M
  let exitOk := 4 + PTM.M.states
  let exitRej := 5 + PTM.M.states
  let fullM := combineTwoExit LTM STM exitOk exitRej stRej
  let acc := LTM.states + stAcc
  let rej := LTM.states + stRej
  let R : List Bool → List Bool → Prop := fun x c => c.length ≤ p.eval x.length ∧ V (x, c) = true
  let t : ℕ → ℕ := fun s =>
    (polyTime p d s s + 1 + (2 * s + 6)) + 1 + (4 * s + 8 + 2 * (Aq * s ^ Kq + Bq))
  have hLTM_valid : validFlatTM LTM :=
    seqTM_valid PTM.M RTM PTM.exit PTM.hValid (checkRestoreTM_valid d) PTM.hTapes rfl PTM.hExitLt
      (by rw [PTM.hSig]; unfold sigL; omega)
  have hSTM_valid : validFlatTM STM := valid_simFlatTM M
  have hok_lt : exitOk < LTM.states := by simp [LTM, seqTM, exitOk, RTM, checkRestoreTM]; omega
  have hrej_lt : exitRej < LTM.states := by simp [LTM, seqTM, exitRej, RTM, checkRestoreTM]; omega
  have hstmRej_lt : stRej < STM.states := by dsimp only [STM, simFlatTM, stRej, numStates]; omega
  have hLTM_sig : LTM.sig = sigL d := by simp [LTM, seqTM, PTM.hSig, RTM, checkRestoreTM, d]
  have hfull_valid : validFlatTM fullM :=
    combineTwoExit_valid LTM STM exitOk exitRej stRej hLTM_valid hSTM_valid rfl rfl
      hok_lt hrej_lt hstmRej_lt (by rw [hLTM_sig]; unfold sigL; omega)
  have hLTM_halt : ∀ cfg, haltingStateReached LTM cfg = true ↔ cfg.state_idx = exitOk ∨ cfg.state_idx = exitRej := by
    intro cfg
    by_cases hlt : cfg.state_idx < PTM.M.states
    · rw [seqTM_halt_lt PTM.M RTM PTM.exit cfg hlt]; simp [exitOk, exitRej]; omega
    · have hge : PTM.M.states ≤ cfg.state_idx := Nat.le_of_not_lt hlt
      let c2 : FlatTMConfig := { cfg with state_idx := cfg.state_idx - PTM.M.states }
      have hsh : cfg = shiftCfg PTM.M.states c2 := by
        cases cfg with | mk st tp =>
          simp only [shiftCfg, c2] at hge ⊢
          congr 1; omega
      rw [hsh, seqTM_halt_shift, checkRestoreTM_halt_iff]
      simp [shiftCfg, c2, exitOk, exitRej]
  have hLTM_noOk : ∀ e ∈ LTM.trans, e.src_state ≠ exitOk := by
    intro e he
    simp only [LTM, seqTM, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (hm1 | rfl) | ⟨e', he', rfl⟩
    · have := (PTM.hValid.2.2 e hm1).1; simp [exitOk]; omega
    · simp [mk1, exitOk]; have := PTM.hExitLt; omega
    · simp only [shiftEntry, exitOk]
      simp only [RTM, checkRestoreTM, List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [mk1]; omega)
  have hLTM_noRej : ∀ e ∈ LTM.trans, e.src_state ≠ exitRej := by
    intro e he
    simp only [LTM, seqTM, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (hm1 | rfl) | ⟨e', he', rfl⟩
    · have := (PTM.hValid.2.2 e hm1).1; simp [exitRej]; omega
    · simp [mk1, exitRej]; have := PTM.hExitLt; omega
    · simp only [shiftEntry, exitRej]
      simp only [RTM, checkRestoreTM, List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [mk1]; omega)
  refine ⟨R, A, K, B, t, fullM, acc, rej, ?_, hfull_valid, rfl, ?_, ?_⟩
  · -- inOPoly t
    have hp1 := polyTime_inOPoly p d
    have hp2 : inOPoly (fun s => 2 * s + 6) := inOPoly_of_le_poly (A := 2) (K := 1) (B := 6) (fun _ => by simp)
    have hp3 : inOPoly (fun s => 4 * s + 8 + 2 * (Aq * s ^ Kq + Bq)) := by
      have ha : inOPoly (fun s => 4 * s + 8) := inOPoly_of_le_poly (A := 4) (K := 1) (B := 8) (fun _ => by simp)
      have hb : inOPoly (fun s => 2 * (Aq * s ^ Kq + Bq)) :=
        inOPoly_of_le_poly (A := 2 * Aq) (K := Kq) (B := 2 * Bq) (fun s => by rw [Nat.mul_add, Nat.mul_assoc])
      exact inOPoly_add ha hb
    exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add hp1 (inOPoly_const 1)) hp2) (inOPoly_const 1)) hp3
  · -- witness bound
    intro x
    dsimp only
    rw [hVspec x]
    constructor
    · rintro ⟨w, hw, hVw⟩
      exact ⟨w, le_trans hw (hp x.length), hw, hVw⟩
    · rintro ⟨w, _, hw, hVw⟩
      exact ⟨w, hw, hVw⟩
  · -- decidesPairInTime
    intro x c
    let s := x.length + c.length
    have hxs_ok : MaskOK d d (x.map (fun b => (b, 0))) := by
      intro bm hbm
      rw [List.mem_map] at hbm; rcases hbm with ⟨b, _, rfl⟩
      exact ⟨Nat.two_pow_pos d, fun j _ => by simp⟩
    obtain ⟨tp, htp_le, hrp⟩ := PTM.hRun (x.map (fun b => (b, 0))) 0 c hxs_ok (Nat.zero_le _)
    have hlen_x : (x.map (fun b => (b, 0))).length = x.length := by simp
    rw [hlen_x] at htp_le hrp
    have hsum_eq : polySumK p d x.length = p.eval x.length := polySumK_eq_eval p x.length
    rw [hsum_eq, Nat.zero_add] at hrp
    let u := min (p.eval x.length) c.length
    have hu_le : u ≤ c.length := Nat.min_le_right _ _
    have hliftP := seqTM_lift1_clean (M₂ := RTM) PTM.hValid (checkRestoreTM_valid d) PTM.hHaltIff PTM.hValid.1 hrp
    have hbrP := seqTM_bridge_step (M₂ := RTM) PTM.hExitLt PTM.hNoExitTrans
      (lenTape (x.map (fun b => (b, 0))) u c) (currentTapeSymbol_at [] 3 _)
    have hchk := checkRestore_run d x c u hu_le
    have htp_s : tp ≤ polyTime p d s s := le_trans htp_le (polyTime_mono p d (by omega) (by omega))
    have hpair_eq : initFlatConfig fullM [pairTape x c] = ⟨PTM.M.start, [([], 0, lenTape (x.map (fun b => (b, 0))) 0 c)]⟩ := by
      simp [initFlatConfig, fullM, combineTwoExit, LTM, seqTM, lenTape_init]
    by_cases hlen_ok : c.length ≤ p.eval x.length
    · -- Branch 1: c.length ≤ p.eval x.length -> checkRestore exits at 4 with pairTape x c -> run simFlatTM M
      have hu_eq : u = c.length := Nat.min_eq_right hlen_ok
      obtain ⟨tr, htr_le, hrr⟩ := hchk.1 hu_eq
      have hliftR := seqTM_lift2_clean (M₁ := PTM.M) PTM.hValid PTM.hExitLt hrr
      have hLrun : ExactRun LTM ⟨PTM.M.start, [([], 0, lenTape (x.map (fun b => (b, 0))) 0 c)]⟩
          ⟨exitOk, [([], 0, pairTape x c)]⟩ (tp + 1 + tr) := by
        simpa [LTM, shiftCfg, exitOk, RTM, checkRestoreTM] using (hliftP.trans hbrP).trans hliftR
      have hfullL := combineTwoExit_liftL (STM := STM) (exitOk := exitOk) (exitRej := exitRej) (stmRej := stRej)
        hLTM_valid hLTM_halt (Nat.lt_of_lt_of_le PTM.hValid.1 (Nat.le_add_right _ _)) hLrun
      have hbrOk := combineTwoExit_bridgeOk (STM := STM) (exitRej := exitRej) (stmRej := stRej)
        hok_lt hLTM_noOk (pairTape x c) (currentTapeSymbol_at [] 3 _)
      -- Run simFlatTM M on pairTape x c
      have hencLen : (PvsNP.encodePair (x, c)).length = s := by
        simp [s, PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
      have hM_xc := hM (x, c)
      rw [hencLen] at hM_xc
      obtain ⟨ts, cfgS, hts_le, hrS, hhaltS, hstS⟩ := simFlatTM_decides_pair M hM_xc
      have hfullS := combineTwoExit_liftS (LTM := LTM) (exitOk := exitOk) (exitRej := exitRej) (stmRej := stRej)
        hLTM_valid hok_lt hrej_lt hrS
      have hcomb1 := runFlatTM_compose fullM (tp + 1 + tr) 1 _ _ hfullL
      rw [hbrOk] at hcomb1
      have hcomb2 := runFlatTM_compose fullM (tp + 1 + tr + 1) ts _ _ hcomb1
      rw [show (⟨STM.start, [([], 0, pairTape x c)]⟩ : FlatTMConfig) = initFlatConfig STM [pairTape x c] from rfl] at hcomb2
      rw [hfullS] at hcomb2
      have hhalt_full : haltingStateReached fullM (shiftCfg LTM.states cfgS) = true := by
        rw [combineTwoExit_halt_shift]; exact hhaltS
      have hts_s : ts ≤ 4 * s + 8 + 2 * (Aq * s ^ Kq + Bq) := by
        have := hq s; omega
      have htot_le : (tp + 1 + tr + 1) + ts ≤ t s := by
        dsimp only [t]; omega
      obtain ⟨pad, hpad⟩ := Nat.exists_eq_add_of_le htot_le
      refine ⟨shiftCfg LTM.states cfgS, ?_, hhalt_full, ?_, ?_⟩
      · rw [hpair_eq, hpad]
        exact runFlatTM_extend hcomb2 hhalt_full
      · simp only [R, hlen_ok, true_and, shiftCfg, hstS, acc, rej]
        cases V (x, c) <;> simp [stAcc, stRej, Nat.add_comm]
      · simp only [R, hlen_ok, true_and, shiftCfg, hstS, acc, rej]
        cases V (x, c) <;> simp [stAcc, stRej, Nat.add_comm]
    · -- Branch 2: c.length > p.eval x.length -> checkRestore exits at 5 -> bridge directly to rej!
      have hu_lt : u < c.length :=
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.lt_of_not_ge hlen_ok)
      obtain ⟨tr, htr_le, tp_end, hrr⟩ := hchk.2 hu_lt
      have hliftR := seqTM_lift2_clean (M₁ := PTM.M) PTM.hValid PTM.hExitLt hrr
      have hLrun : ExactRun LTM ⟨PTM.M.start, [([], 0, lenTape (x.map (fun b => (b, 0))) 0 c)]⟩
          ⟨exitRej, [tp_end]⟩ (tp + 1 + tr) := by
        simpa [LTM, shiftCfg, exitRej, RTM, checkRestoreTM] using (hliftP.trans hbrP).trans hliftR
      have hfullL := combineTwoExit_liftL (STM := STM) (exitOk := exitOk) (exitRej := exitRej) (stmRej := stRej)
        hLTM_valid hLTM_halt (Nat.lt_of_lt_of_le PTM.hValid.1 (Nat.le_add_right _ _)) hLrun
      have hb0 : ∀ v ∈ (lenTape (x.map (fun b => (b, 0))) 0 c), v < LTM.sig := by
        intro v hv
        rw [lenTape_init] at hv
        rw [hLTM_sig]; unfold sigL
        simp only [pairTape, symbolsOf, List.mem_cons, List.mem_append, List.mem_map,
          List.mem_singleton, List.not_mem_nil, or_false, or_assoc] at hv
        rcases hv with rfl | ⟨b, _, rfl⟩ | rfl | ⟨b, _, rfl⟩ | rfl | rfl <;>
          (try (cases b <;> simp only [↓reduceIte, Bool.false_eq_true])) <;> omega
      have hb_end := tape_bounded_of_run hLTM_valid rfl hb0 hLrun.1
      have hsym_bnd : ∀ v, currentTapeSymbol tp_end = some v → v < max LTM.sig STM.sig := by
        intro v hv
        unfold currentTapeSymbol at hv
        split_ifs at hv with hlt
        have heq := Option.some.inj hv
        subst heq
        exact Nat.lt_of_lt_of_le (hb_end _ (List.getElem_mem hlt)) (Nat.le_max_left _ _)
      have hbrRej := combineTwoExit_bridgeRej (STM := STM) (exitOk := exitOk) (stmRej := stRej)
        hrej_lt (by simp [exitOk, exitRej]) hLTM_noRej tp_end hsym_bnd
      have hcomb := runFlatTM_compose fullM (tp + 1 + tr) 1 _ _ hfullL
      rw [hbrRej] at hcomb
      have hhalt_rej : haltingStateReached fullM (shiftCfg LTM.states ⟨stRej, [tp_end]⟩) = true := by
        rw [combineTwoExit_halt_shift, halting_iff]; exact Or.inr rfl
      have htot_le : (tp + 1 + tr) + 1 ≤ t s := by
        dsimp only [t]; omega
      obtain ⟨pad, hpad⟩ := Nat.exists_eq_add_of_le htot_le
      refine ⟨shiftCfg LTM.states ⟨stRej, [tp_end]⟩, ?_, hhalt_rej, ?_, ?_⟩
      · rw [hpair_eq, hpad]
        exact runFlatTM_extend hcomb hhalt_rej
      · simp only [R, hlen_ok, false_and, shiftCfg, acc, rej, stAcc, stRej]
        constructor
        · intro h; cases h
        · intro h; omega
      · simp only [R, hlen_ok, false_and, not_false_eq_true, shiftCfg, rej]
        simp [Nat.add_comm]

