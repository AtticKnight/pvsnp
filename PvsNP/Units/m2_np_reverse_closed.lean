import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_union
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_karp_trans
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m1_st_np_to_flat_np
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m1_flat_np_to_st_np
import PvsNP.Units.m3_3sat_in_np
import PvsNP.Units.m3_sat_to_3occ_sat

/-
Predicted closure statements, on settled units of github.com/makedotfun/pvsnp, imported: P, NP and coNP are
closed under polynomial-time preimages (m2_p_down_closed, m2_np_down_closed, m2_conp_down_closed) and so under
reversal (m2_reverse_polytime); P is closed under difference (m2_p_inter, m2_p_compl) and symmetric difference
(m2_p_union); NP ∩ coNP is closed under complement; 3SAT is in NP on TM2 (m3_3sat_in_np through the bridges
m1_flat_np_to_st_np and m1_st_to_tm2); SAT with each variable occurring at most three times is NP-hard on TM2
(m3_sat_to_3occ_sat through m1_tm2_to_st, m1_st_np_to_flat_np, m1_flat_to_st, m1_st_to_tm2, m2_karp_trans).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_np_reverse_closed

theorem p_preimage : ∀ (f : List Bool → List Bool) (L : Language Bool),
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → L ∈ PvsNP.P →
      ({x : List Bool | f x ∈ L} : Language Bool) ∈ PvsNP.P :=
  fun f L hf hL => PvsNP.Units.m2_p_down_closed _ L ⟨f, hf, fun _ => Iff.rfl⟩ hL

theorem np_preimage : ∀ (f : List Bool → List Bool) (L : Language Bool),
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → L ∈ PvsNP.NP →
      ({x : List Bool | f x ∈ L} : Language Bool) ∈ PvsNP.NP :=
  fun f L hf hL => PvsNP.Units.m2_np_down_closed _ L ⟨f, hf, fun _ => Iff.rfl⟩ hL

theorem conp_preimage : ∀ (f : List Bool → List Bool) (L : Language Bool),
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → L ∈ PvsNP.coNP →
      ({x : List Bool | f x ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  fun f L hf hL => PvsNP.Units.m2_conp_down_closed _ L ⟨f, hf, fun _ => Iff.rfl⟩ hL

theorem p_rev : ∀ L : Language Bool, L ∈ PvsNP.P →
    ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.P :=
  fun L hL => p_preimage _ L PvsNP.Units.m2_reverse_polytime hL

theorem np_rev : ∀ L : Language Bool, L ∈ PvsNP.NP →
    ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.NP :=
  fun L hL => np_preimage _ L PvsNP.Units.m2_reverse_polytime hL

theorem conp_rev : ∀ L : Language Bool, L ∈ PvsNP.coNP →
    ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  fun L hL => conp_preimage _ L PvsNP.Units.m2_reverse_polytime hL

theorem p_diff : ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P → L₁ \ L₂ ∈ PvsNP.P := by
  intro L₁ L₂ h1 h2
  rw [sdiff_eq]
  exact PvsNP.Units.m2_p_inter _ _ h1 (PvsNP.Units.m2_p_compl _ h2)

theorem p_symmDiff : ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
    symmDiff L₁ L₂ ∈ PvsNP.P := by
  intro L₁ L₂ h1 h2
  rw [symmDiff]
  exact PvsNP.Units.m2_p_union _ _ (p_diff _ _ h1 h2) (p_diff _ _ h2 h1)

theorem np_conp_compl : ∀ L ∈ PvsNP.NP ∩ PvsNP.coNP, Lᶜ ∈ PvsNP.NP ∩ PvsNP.coNP := by
  rintro L ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  show Lᶜᶜ ∈ PvsNP.NP
  rw [compl_compl]
  exact h1

theorem conp_iff : ∀ L : Language Bool, L ∈ PvsNP.coNP ↔ Lᶜ ∈ PvsNP.NP := fun _ => Iff.rfl

theorem np_iff_compl_conp : ∀ L : Language Bool, L ∈ PvsNP.NP ↔ Lᶜ ∈ PvsNP.coNP := by
  intro L
  show L ∈ PvsNP.NP ↔ Lᶜᶜ ∈ PvsNP.NP
  rw [compl_compl]

theorem three_in_np : ∀ L : Language Bool,
    (∀ x, x ∈ L ↔ (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) → L ∈ PvsNP.NP := by
  intro L hL
  have hin : CookLevin.inNP (fun x => x ∈ L) := by
    obtain ⟨R, a, k, b, t, M, acc, rej, ht, hM, htape, hmem, hdec⟩ := PvsNP.Units.m3_3sat_in_np
    exact ⟨R, a, k, b, t, M, acc, rej, ht, hM, htape, fun x => (hL x).trans (hmem x), hdec⟩
  obtain ⟨V, p, hV, hcond⟩ := PvsNP.Units.m1_flat_np_to_st_np L hin
  exact ⟨V, p, PvsNP.Units.m1_st_to_tm2 _ _ _ hV, hcond⟩

theorem occ3_hard : ∀ L : Language Bool,
    (∀ x, x ∈ L ↔ (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
      SAT (SATStr.cnfOf x)) → PvsNP.NPHard L := by
  intro L hL L' hL'
  obtain ⟨V, p, hV, hcond⟩ := hL'
  have hST : L' ∈ PvsNP.SingleTape.NP := ⟨V, p, PvsNP.Units.m1_tm2_to_st _ _ _ hV, hcond⟩
  have hin : CookLevin.inNP (fun x => x ∈ L') := PvsNP.Units.m1_st_np_to_flat_np L' hST
  obtain ⟨f, t, M, ht, hM, h1, hcomp, hred⟩ := CookLevin.cook_levin.1 _ hin
  have hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f :=
    PvsNP.Units.m1_st_to_tm2 _ _ _ (PvsNP.Units.m1_flat_to_st f t M ht hM h1 hcomp)
  obtain ⟨g, t', M', ht', hM', h1', hcomp', hred'⟩ := PvsNP.Units.m3_sat_to_3occ_sat
  have hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g :=
    PvsNP.Units.m1_st_to_tm2 _ _ _ (PvsNP.Units.m1_flat_to_st g t' M' ht' hM' h1' hcomp')
  have hA : PvsNP.KarpReducible L' {x | SATStr x} := ⟨f, hf, hred⟩
  have hB : PvsNP.KarpReducible {x | SATStr x} L := ⟨g, hg, fun x => (hred' x).trans (hL (g x)).symm⟩
  exact PvsNP.Units.m2_karp_trans _ _ _ hA hB



theorem h_p_preimage :
    ∀ (f : List Bool → List Bool) (L : Language Bool), PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → L ∈ PvsNP.P → ({x : List Bool | f x ∈ L} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_np_reverse_closed.p_preimage


theorem h_np_preimage :
    ∀ (f : List Bool → List Bool) (L : Language Bool), PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → L ∈ PvsNP.NP → ({x : List Bool | f x ∈ L} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_reverse_closed.np_preimage


theorem h_conp_preimage :
    ∀ (f : List Bool → List Bool) (L : Language Bool), PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → L ∈ PvsNP.coNP → ({x : List Bool | f x ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.m2_np_reverse_closed.conp_preimage


theorem h_p_rev :
    ∀ L : Language Bool, L ∈ PvsNP.P → ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_np_reverse_closed.p_rev


theorem h_np_rev :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_reverse_closed.np_rev


theorem h_conp_rev :
    ∀ L : Language Bool, L ∈ PvsNP.coNP → ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.m2_np_reverse_closed.conp_rev


theorem h_p_diff :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P → L₁ \ L₂ ∈ PvsNP.P :=
  PvsNP.Units.m2_np_reverse_closed.p_diff


theorem h_p_symmDiff :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P → symmDiff L₁ L₂ ∈ PvsNP.P :=
  PvsNP.Units.m2_np_reverse_closed.p_symmDiff


theorem h_np_conp_compl :
    ∀ L ∈ PvsNP.NP ∩ PvsNP.coNP, Lᶜ ∈ PvsNP.NP ∩ PvsNP.coNP :=
  PvsNP.Units.m2_np_reverse_closed.np_conp_compl


theorem h_conp_iff : ∀ L : Language Bool, L ∈ PvsNP.coNP ↔ Lᶜ ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_reverse_closed.conp_iff


theorem h_np_iff_compl_conp : ∀ L : Language Bool, L ∈ PvsNP.NP ↔ Lᶜ ∈ PvsNP.coNP :=
  PvsNP.Units.m2_np_reverse_closed.np_iff_compl_conp


theorem h_three_in_np :
    ∀ L : Language Bool, (∀ x, x ∈ L ↔ (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) → L ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_reverse_closed.three_in_np


end PvsNP.Units.m2_np_reverse_closed

theorem PvsNP.Units.m2_np_reverse_closed :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | x.reverse ∈ L} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_reverse_closed.h_np_rev
