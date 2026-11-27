import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_iff_padded_p
import PvsNP.Units.m2_p_concat
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_some_prefix
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_reverse_polytime

namespace PvsNP.Units.tc_exp_some_factor

/-- Decidable within `2 ^ (n ^ K) + K` steps. -/
def IsExpK (K : ℕ) (L : Language Bool) : Prop :=
  ∃ (f : List Bool → Bool)
    (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
    (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ K) + K

def padOf (K : ℕ) (x : List Bool) : List Bool :=
  List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: x

def PadSet (K : ℕ) (S : Language Bool) : Language Bool :=
  {s | ∃ x : List Bool, x ∈ S ∧ s = padOf K x}

def Ones : Language Bool := {u | false ∉ u}

def SP (L : Language Bool) : Language Bool := {x | ∃ y : List Bool, y <+: x ∧ y ∈ L}

def SS (L : Language Bool) : Language Bool := {x | ∃ y : List Bool, y <:+ x ∧ y ∈ L}

def Rev (L : Language Bool) : Language Bool := {x | x.reverse ∈ L}

theorem bound_mono (k K n : ℕ) (hK : 1 ≤ K) (hk : k ≤ K) :
    2 ^ (n ^ k) + k ≤ 2 ^ (n ^ K) + K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2 : (0 : ℕ) ^ K = 0 := Nat.zero_pow (by omega)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h2]
      simp
      omega
    · have h1 : (0 : ℕ) ^ k = 0 := Nat.zero_pow hk0
      rw [h1, h2]
      simp
      omega
  · have h1 : n ^ k ≤ n ^ K := Nat.pow_le_pow_right hn hk
    have h2 : 2 ^ (n ^ k) ≤ 2 ^ (n ^ K) := Nat.pow_le_pow_right (by norm_num) h1
    omega

theorem expK_mono {k K : ℕ} {L : Language Bool} (h : IsExpK k L) (hk : k ≤ K) (hK : 1 ≤ K) :
    IsExpK K L := by
  obtain ⟨f, M, h1, h2⟩ := h
  exact ⟨f, M, h1, fun n => (h2 n).trans (bound_mono k K n hK hk)⟩

theorem foldl_seen_false (x : List Bool) :
    ∀ q : Bool, x.foldl (fun (q : Bool) (b : Bool) => q || !b) q = (q || decide (false ∈ x)) := by
  induction x with
  | nil => intro q; simp
  | cons b x ih =>
    intro q
    rw [List.foldl_cons, ih]
    cases b <;> cases q <;> simp

theorem ones_p : Ones ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_dfa_in_p Bool (fun (q : Bool) (b : Bool) => q || !b) false
    (fun q => !q)
  have e : Ones = ({x : List Bool | (fun q : Bool => !q)
      (x.foldl (fun (q : Bool) (b : Bool) => q || !b) false) = true} : Language Bool) := by
    ext x
    show false ∉ x ↔ (!(x.foldl (fun (q : Bool) (b : Bool) => q || !b) false)) = true
    rw [foldl_seen_false]
    simp
  rw [e]
  exact h

theorem someprefix_exp {L : Language Bool} (hL : ∃ k, IsExpK k L) : ∃ k, IsExpK k (SP L) := by
  obtain ⟨k, hk⟩ := hL
  obtain ⟨k0, f0, M0, h0, t0⟩ :=
    PvsNP.Units.m2_p_subset_exp (Set.univ : Language Bool) PvsNP.Units.m2_p_trivial.2
  set K := max (max k k0) 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hL' : IsExpK K L := expK_mono hk (le_trans (le_max_left _ _) (le_max_left _ _)) hK1
  have hU' : IsExpK K (Set.univ : Language Bool) :=
    expK_mono ⟨f0, M0, h0, t0⟩ (le_trans (le_max_right _ _) (le_max_left _ _)) hK1
  have hPadL : PadSet K L ∈ PvsNP.P := PvsNP.Units.m2_upward_padding L K hL'
  have hPadU : PadSet K (Set.univ : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_upward_padding _ K hU'
  have hQ := PvsNP.Units.m2_p_concat Ones (PadSet K L) ones_p hPadL
  have hSQ := PvsNP.Units.m2_p_some_prefix _ hQ
  have hI := PvsNP.Units.m2_p_inter _ _ hPadU hSQ
  have e : PadSet K (SP L) = PadSet K (Set.univ : Language Bool) ⊓
      {x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈
        ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ Ones ∧ v ∈ PadSet K L} :
          Language Bool)} := by
    ext s
    constructor
    · rintro ⟨x, ⟨y, ⟨t, hyt⟩, hy⟩, rfl⟩
      refine ⟨⟨x, trivial, rfl⟩, ?_⟩
      have hle : y.length ≤ x.length := by
        rw [← hyt]; simp
      have hm : 2 ^ (y.length ^ K) + K ≤ 2 ^ (x.length ^ K) + K := by
        have := Nat.pow_le_pow_left hle K
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
        omega
      refine ⟨List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: y, ⟨t, ?_⟩,
        List.replicate (2 ^ (x.length ^ K) + K - (2 ^ (y.length ^ K) + K)) true,
        padOf K y, ?_, ?_, y, hy, rfl⟩
      · rw [← hyt]; simp [padOf]
      · simp only [padOf]
        rw [← List.append_assoc, ← List.replicate_add, Nat.sub_add_cancel hm]
      · show false ∉ List.replicate _ true
        simp [List.mem_replicate]
    · rintro ⟨⟨x, -, rfl⟩, p, ⟨t, hpt⟩, a, v, rfl, ha, y, hy, rfl⟩
      have ha' : a = List.replicate a.length true := by
        rw [List.eq_replicate_iff]
        refine ⟨rfl, fun b hb => ?_⟩
        cases b
        · exact absurd hb ha
        · rfl
      obtain ⟨n, rfl⟩ : ∃ n, a = List.replicate n true := ⟨a.length, ha'⟩
      have hpt' : List.replicate (n + (2 ^ (y.length ^ K) + K)) true ++
          false :: (y ++ t) = List.replicate (2 ^ (x.length ^ K) + K) true ++ false :: x := by
        have h := hpt
        simp only [padOf] at h
        rw [List.replicate_add]
        simpa only [List.append_assoc, List.cons_append] using h
      have := PvsNP.Units.m2_exp_iff_padded_p.rep_inj _ _ _ _ hpt'
      exact ⟨x, ⟨y, ⟨t, this.2⟩, hy⟩, rfl⟩
  have hI' : PadSet K (SP L) ∈ PvsNP.P := by
    rw [e]
    exact hI
  have hIe := (PvsNP.Units.m2_exp_iff_padded_p (SP L)).2 ⟨K, hI'⟩
  obtain ⟨k', f, M, h1, h2⟩ := hIe
  exact ⟨k', f, M, h1, h2⟩

theorem rev_exp {L : Language Bool} (hL : ∃ k, IsExpK k L) : ∃ k, IsExpK k (Rev L) := by
  obtain ⟨k, f, M, h1, h2⟩ := hL
  have hk : PvsNP.KarpReducible (Rev L) L :=
    ⟨fun x => x.reverse, PvsNP.Units.m2_reverse_polytime, fun x => Iff.rfl⟩
  obtain ⟨k', f', M', h1', h2'⟩ := PvsNP.Units.m2_exp_down_closed (Rev L) L hk ⟨k, f, M, h1, h2⟩
  exact ⟨k', f', M', h1', h2'⟩

theorem somesuffix_exp {L : Language Bool} (hL : ∃ k, IsExpK k L) : ∃ k, IsExpK k (SS L) := by
  have h1 := someprefix_exp (rev_exp hL)
  have h2 := rev_exp h1
  have e : SS L = Rev (SP (Rev L)) := by
    ext x
    constructor
    · rintro ⟨y, hy, hyL⟩
      refine ⟨y.reverse, ?_, by
        show y.reverse.reverse ∈ L
        rwa [List.reverse_reverse]⟩
      exact List.reverse_prefix.mpr hy
    · rintro ⟨y', hy', hmem⟩
      refine ⟨y'.reverse, ?_, hmem⟩
      have : y'.reverse.reverse <+: x.reverse := by rwa [List.reverse_reverse]
      exact List.reverse_prefix.mp this
  rw [e]
  exact h2

end PvsNP.Units.tc_exp_some_factor

theorem PvsNP.Units.tc_exp_some_factor :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ y : List Bool, y <:+: x ∧ y ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  obtain ⟨k, f, M, h1, h2⟩ := hL
  have h := PvsNP.Units.tc_exp_some_factor.somesuffix_exp
    (PvsNP.Units.tc_exp_some_factor.someprefix_exp (L := L) ⟨k, f, M, h1, h2⟩)
  obtain ⟨k', f', M', h1', h2'⟩ := h
  refine ⟨k', f', M', fun x => ?_, h2'⟩
  rw [← h1' x]
  constructor
  · rintro ⟨y, ⟨a, b, hab⟩, hyL⟩
    exact ⟨y ++ b, ⟨a, by rw [← hab, List.append_assoc]⟩, y, ⟨b, rfl⟩, hyL⟩
  · rintro ⟨t, ⟨a, hat⟩, y, ⟨u, hu⟩, hyL⟩
    exact ⟨y, ⟨a, u, by rw [List.append_assoc, hu, hat]⟩, hyL⟩
