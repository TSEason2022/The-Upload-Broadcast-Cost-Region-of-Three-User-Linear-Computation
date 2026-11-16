import UploadBroadcast.RankLoss
import UploadBroadcast.ProfileTransport
import UploadBroadcast.Coordination
import UploadBroadcast.AlignedRelation
import Mathlib.Tactic.FieldSimp

/-!
# Actual kernel relays for nonzero-defect components

This file proves the geometric kernel construction in Step 1 of `lem:same-chart`.
The hypotheses concern the original side/signal subspaces and relation maps,
not a desired output profile. It does not assert the dense-orbit transfer or
that every classified nonzero-defect indecomposable satisfies those hypotheses.
-/
namespace UploadBroadcast.NonzeroDefectRelays
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- A nonzero restriction of a form gives a complementary side direction. -/
theorem sup_kernel_eq_top (A : Submodule K F) (l : F →ₗ[K] K)
    (h : ∃ a ∈ A, l a ≠ 0) : A ⊔ LinearMap.ker l = ⊤ := by
  obtain ⟨a, ha, hla⟩ := h
  apply top_unique
  intro x _
  refine Submodule.mem_sup.mpr ⟨(l x / l a) • a, A.smul_mem _ ha,
    x - (l x / l a) • a, ?_, by abel⟩
  change l (x - (l x / l a) • a) = 0
  simp [map_sub, map_smul, div_mul_cancel₀ _ hla]

/-- Relation correction proves local generation of the actual hyperplane.
The first arm is killed by the form; a relation with nonzero second-arm
value simultaneously corrects the two remote uploads. -/
theorem hyperplane_locally_generated
    (A B C : Submodule K F) (l : F →ₗ[K] K)
    (hspan : (A ⊔ B) ⊔ C = ⊤) (hA : A ≤ LinearMap.ker l)
    (a b c : F) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hrel : a + b + c = 0) (hlb : l b ≠ 0) :
    LinearMap.ker l =
      ((LinearMap.ker l ⊓ A) ⊔ (LinearMap.ker l ⊓ B)) ⊔
        (LinearMap.ker l ⊓ C) := by
  apply le_antisymm
  · intro x hx
    have hxs : x ∈ (A ⊔ B) ⊔ C := by rw [hspan]; trivial
    obtain ⟨ab, hab, z, hz, hxz⟩ := Submodule.mem_sup.mp hxs
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hab
    have hsum : u + v + z = x := by rw [huv, hxz]
    have hla : l a = 0 := hA ha
    have hlu : l u = 0 := hA hu
    have hlx : l x = 0 := hx
    have hlc : l c = -l b := by
      have hh := congrArg l hrel
      simp only [map_add, map_zero, hla, zero_add] at hh
      exact eq_neg_of_add_eq_zero_right hh
    have hlz : l z = -l v := by
      have hh := congrArg l hsum
      simp only [map_add, hlu, zero_add, hlx] at hh
      exact eq_neg_of_add_eq_zero_right hh
    let t := l v / l b
    have htv : t * l b = l v := div_mul_cancel₀ _ hlb
    have h1 : u - t • a ∈ LinearMap.ker l ⊓ A := by
      exact ⟨by change l (u - t • a) = 0; simp [hlu, hla],
        A.sub_mem hu (A.smul_mem _ ha)⟩
    have h2 : v - t • b ∈ LinearMap.ker l ⊓ B := by
      exact ⟨by change l (v - t • b) = 0; simp [htv],
        B.sub_mem hv (B.smul_mem _ hb)⟩
    have h3 : z - t • c ∈ LinearMap.ker l ⊓ C := by
      exact ⟨by change l (z - t • c) = 0; simp [hlz, hlc, htv],
        C.sub_mem hz (C.smul_mem _ hc)⟩
    have heq : (u - t • a) + (v - t • b) + (z - t • c) = x := by
      calc
        _ = (u + v + z) - t • (a + b + c) := by simp [smul_add]; abel
        _ = x := by rw [hrel, hsum]; simp
    rw [← heq]
    exact Submodule.mem_sup.mpr ⟨_, Submodule.mem_sup.mpr ⟨_, h1, _, h2, rfl⟩,
      _, h3, rfl⟩
  · exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left

/-- Canonically indexed hyperplane construction: actual local generation and
relay feasibility. No optimality or generic-rank claim is assumed here. -/
theorem hyperplane_relay (T : Task K F) (l : F →ₗ[K] K)
    (hspan : T.Spanning) (hU : T.U 0 ≤ LinearMap.ker l)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a + b + c = 0) (hlb : l b ≠ 0) :
    T.LocallyGenerated (LinearMap.ker l) ∧ T.RelayFeasible (LinearMap.ker l) := by
  have hA : T.A 0 ≤ LinearMap.ker l := (T.side_le_signal 0).trans hU
  have hlc : l c ≠ 0 := by
    intro hc0
    have hh := congrArg l hrel
    have ha0 : l a = 0 := hA ha
    simp [ha0, hc0] at hh
    exact hlb hh
  constructor
  · rw [Task.LocallyGenerated, Profile.three_iSup]
    exact hyperplane_locally_generated _ _ _ _
      (by simpa [Task.Spanning, Profile.three_iSup] using hspan) hA a b c ha hb hc hrel hlb
  · intro i
    fin_cases i
    · exact hU.trans le_sup_right
    · change T.U 1 ≤ T.A 1 ⊔ LinearMap.ker l
      rw [sup_kernel_eq_top (T.A 1) l ⟨b, hb, hlb⟩]; exact le_top
    · change T.U 2 ≤ T.A 2 ⊔ LinearMap.ker l
      rw [sup_kernel_eq_top (T.A 2) l ⟨c, hc, hlc⟩]; exact le_top


/-- The actual task induced by a locally generated relay, in the same ambient
coefficient space. Its side and signal subspaces are literal intersections. -/
def inducedTask (T : Task K F) (P : Submodule K F) (hP : T.LocallyGenerated P) :
    Task K F where
  A i := T.A i ⊓ P
  U i := T.U i ⊓ P
  side_le_signal i := inf_le_inf (T.side_le_signal i) le_rfl
  feasible i := by
    have hh : (⨆ j, T.A j ⊓ P) = P := by
      simpa only [inf_comm] using hP.symm
    rw [hh]
    exact inf_le_right


/-- Local generation is invariant under permutation of the user arms. -/
theorem reindex_locallyGenerated (T : Task K F) (p : Equiv.Perm Three)
    (P : Submodule K F) :
    (Profile.reindexTask p T).LocallyGenerated P ↔ T.LocallyGenerated P := by
  unfold Task.LocallyGenerated
  change (P = ⨆ i, P ⊓ T.A (p i)) ↔ (P = ⨆ i, P ⊓ T.A i)
  rw [Equiv.iSup_comp (g := fun i => P ⊓ T.A i) p]

/-- Decoder feasibility is invariant under the same arm permutation. -/
theorem reindex_relayFeasible (T : Task K F) (p : Equiv.Perm Three)
    (P : Submodule K F) :
    (Profile.reindexTask p T).RelayFeasible P ↔ T.RelayFeasible P := by
  constructor
  · intro h i
    simpa only [Profile.reindexTask, p.apply_symm_apply] using h (p.symm i)
  · intro h i
    exact h (p i)

/-- The hyperplane construction works for every designated arm, via a
simultaneous permutation of the side and signal subspaces. -/
theorem hyperplane_relay_permuted (T : Task K F) (p : Equiv.Perm Three)
    (l : F →ₗ[K] K) (hspan : T.Spanning) (hU : T.U (p 0) ≤ LinearMap.ker l)
    (a b c : F) (ha : a ∈ T.A (p 0)) (hb : b ∈ T.A (p 1)) (hc : c ∈ T.A (p 2))
    (hrel : a + b + c = 0) (hlb : l b ≠ 0) :
    T.LocallyGenerated (LinearMap.ker l) ∧ T.RelayFeasible (LinearMap.ker l) := by
  have hs : (Profile.reindexTask p T).Spanning := by
    simpa only [Task.Spanning, Profile.reindexTask, Equiv.iSup_comp p] using hspan
  have hh := hyperplane_relay (Profile.reindexTask p T) l hs hU a b c ha hb hc hrel hlb
  exact ⟨(reindex_locallyGenerated T p _).mp hh.1, (reindex_relayFeasible T p _).mp hh.2⟩

/-- The relation evaluations whose full rank is the codimension-two wedge
condition in Step 1 of `lem:same-chart`. -/
def relationEvaluation (A : Three → Submodule K F) (l₁ l₂ : F →ₗ[K] K) :
    LinearMap.ker (AlignedRelation.signalSum A) →ₗ[K] (K × K) :=
  (((l₂.comp (A 0).subtype).comp (LinearMap.proj 0)).comp
      (LinearMap.ker (AlignedRelation.signalSum A)).subtype).prod
    (((l₁.comp (A 1).subtype).comp (LinearMap.proj 1)).comp
      (LinearMap.ker (AlignedRelation.signalSum A)).subtype)


/-- A nonzero two-vector determinant gives surjectivity onto the pair of
form values. This turns an actual wedge witness into `relationEvaluation`'s
full-rank hypothesis without assuming a rank formula. -/
theorem surjective_of_wedge {X : Type*} [AddCommGroup X] [Module K X]
    (f : X →ₗ[K] (K × K)) (v w : X)
    (hdet : (f v).1 * (f w).2 - (f w).1 * (f v).2 ≠ 0) :
    Function.Surjective f := by
  intro y
  let d := (f v).1 * (f w).2 - (f w).1 * (f v).2
  refine ⟨(((f w).2*y.1 - (f w).1*y.2)/d) • v +
    (((f v).1*y.2 - (f v).2*y.1)/d) • w, ?_⟩
  apply Prod.ext <;> simp only [map_add, map_smul] <;>
    dsimp [d] <;> field_simp <;> ring

/-- Evaluation of the relation sum in the original ambient space. -/
theorem relation_sum_eq_zero (A : Three → Submodule K F)
    (r : LinearMap.ker (AlignedRelation.signalSum A)) :
    ((r.1 0 : A 0) : F) + (r.1 1 : F) + (r.1 2 : F) = 0 := by
  have hh := r.property
  change AlignedRelation.signalSum A r.1 = 0 at hh
  simpa [AlignedRelation.signalSum, Fin.sum_univ_succ, add_assoc] using hh

/-- Full-rank relation evaluation corrects both local form values and yields
local generation of the actual codimension-two kernel. -/
theorem codimTwo_locally_generated (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (hspan : T.Spanning) (h₁ : T.U 0 ≤ LinearMap.ker l₁)
    (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂)) :
    T.LocallyGenerated (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) := by
  let P := LinearMap.ker l₁ ⊓ LinearMap.ker l₂
  rw [Task.LocallyGenerated, Profile.three_iSup]
  apply le_antisymm
  · intro x hx
    have hxs : x ∈ (T.A 0 ⊔ T.A 1) ⊔ T.A 2 := by
      have hs : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤ := by
        simpa [Task.Spanning, Profile.three_iSup] using hspan
      rw [hs]; trivial
    obtain ⟨ab, hab, z, hz, hxz⟩ := Submodule.mem_sup.mp hxs
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hab
    have hsum : u + v + z = x := by rw [huv, hxz]
    obtain ⟨r, hr⟩ := hwedge (l₂ u, l₁ v)
    have hr₀ : l₂ (r.1 0 : F) = l₂ u := congrArg Prod.fst hr
    have hr₁ : l₁ (r.1 1 : F) = l₁ v := congrArg Prod.snd hr
    have hz₀ : l₁ (r.1 0 : F) = 0 := h₁ (T.side_le_signal 0 (r.1 0).property)
    have hz₁ : l₂ (r.1 1 : F) = 0 := h₂ (T.side_le_signal 1 (r.1 1).property)
    have hu₀ : l₁ u = 0 := h₁ (T.side_le_signal 0 hu)
    have hv₁ : l₂ v = 0 := h₂ (T.side_le_signal 1 hv)
    have hx₀ : l₁ x = 0 := hx.1
    have hx₁ : l₂ x = 0 := hx.2
    have hrs := relation_sum_eq_zero T.A r
    have h₀ := congrArg l₁ hrs
    have h₃ := congrArg l₂ hrs
    have hs₀ := congrArg l₁ hsum
    have hs₁ := congrArg l₂ hsum
    simp only [map_add, map_zero, hz₀, hz₁, hr₀, hr₁, hu₀, hv₁,
      hx₀, hx₁, zero_add, add_zero] at h₀ h₃ hs₀ hs₁
    have h1 : u - (r.1 0 : F) ∈ P ⊓ T.A 0 := by
      refine ⟨⟨?_, ?_⟩, (T.A 0).sub_mem hu (r.1 0).property⟩
      · change l₁ (u - (r.1 0 : F)) = 0; simp [hu₀, hz₀]
      · change l₂ (u - (r.1 0 : F)) = 0; simp [hr₀]
    have h2 : v - (r.1 1 : F) ∈ P ⊓ T.A 1 := by
      refine ⟨⟨?_, ?_⟩, (T.A 1).sub_mem hv (r.1 1).property⟩
      · change l₁ (v - (r.1 1 : F)) = 0; simp [hr₁]
      · change l₂ (v - (r.1 1 : F)) = 0; simp [hv₁, hz₁]
    have h3 : z - (r.1 2 : F) ∈ P ⊓ T.A 2 := by
      refine ⟨⟨?_, ?_⟩, (T.A 2).sub_mem hz (r.1 2).property⟩
      · change l₁ (z - (r.1 2 : F)) = 0
        rw [map_sub]; linear_combination hs₀ - h₀
      · change l₂ (z - (r.1 2 : F)) = 0
        rw [map_sub]; linear_combination hs₁ - h₃
    have heq : (u - (r.1 0 : F)) + (v - (r.1 1 : F)) +
        (z - (r.1 2 : F)) = x := by
      calc
        _ = (u + v + z) - ((r.1 0 : F) + (r.1 1 : F) + (r.1 2 : F)) := by abel
        _ = x := by rw [hrs, hsum]; simp
    rw [← heq]
    exact Submodule.mem_sup.mpr ⟨_, Submodule.mem_sup.mpr ⟨_, h1, _, h2, rfl⟩,
      _, h3, rfl⟩
  · exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left


/-- The same full-rank wedge gives all three decoder feasibility inclusions. -/
theorem codimTwo_feasible (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂)) :
    T.RelayFeasible (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) := by
  intro i x hx
  fin_cases i
  · obtain ⟨r, hr⟩ := hwedge (l₂ x, 0)
    have hr₀ : l₂ (r.1 0 : F) = l₂ x := congrArg Prod.fst hr
    refine Submodule.mem_sup.mpr ⟨_, (r.1 0).property, x - (r.1 0 : F), ?_, by abel⟩
    refine ⟨?_, ?_⟩
    · change l₁ (x - (r.1 0 : F)) = 0
      have ha : l₁ (r.1 0 : F) = 0 := h₁ (T.side_le_signal 0 (r.1 0).property)
      have hxx : l₁ x = 0 := h₁ hx
      simp [ha, hxx]
    · change l₂ (x - (r.1 0 : F)) = 0
      simp [hr₀]
  · obtain ⟨r, hr⟩ := hwedge (0, l₁ x)
    have hr₁ : l₁ (r.1 1 : F) = l₁ x := congrArg Prod.snd hr
    refine Submodule.mem_sup.mpr ⟨_, (r.1 1).property, x - (r.1 1 : F), ?_, by abel⟩
    refine ⟨?_, ?_⟩
    · change l₁ (x - (r.1 1 : F)) = 0
      simp [hr₁]
    · change l₂ (x - (r.1 1 : F)) = 0
      have ha : l₂ (r.1 1 : F) = 0 := h₂ (T.side_le_signal 1 (r.1 1).property)
      have hxx : l₂ x = 0 := h₂ hx
      simp [ha, hxx]
  · obtain ⟨r, hr⟩ := hwedge (-l₂ x, -l₁ x)
    have hr₀ : l₂ (r.1 0 : F) = -l₂ x := congrArg Prod.fst hr
    have hr₁ : l₁ (r.1 1 : F) = -l₁ x := congrArg Prod.snd hr
    have hz₀ : l₁ (r.1 0 : F) = 0 := h₁ (T.side_le_signal 0 (r.1 0).property)
    have hz₁ : l₂ (r.1 1 : F) = 0 := h₂ (T.side_le_signal 1 (r.1 1).property)
    have hrs := relation_sum_eq_zero T.A r
    have hs₀ := congrArg l₁ hrs
    have hs₁ := congrArg l₂ hrs
    simp only [map_add, map_zero, hz₀, hz₁, hr₀, hr₁, zero_add, add_zero] at hs₀ hs₁
    refine Submodule.mem_sup.mpr ⟨_, (r.1 2).property, x - (r.1 2 : F), ?_, by abel⟩
    refine ⟨?_, ?_⟩
    · change l₁ (x - (r.1 2 : F)) = 0
      rw [map_sub]; linear_combination -hs₀
    · change l₂ (x - (r.1 2 : F)) = 0
      rw [map_sub]; linear_combination -hs₁

/-- The wedge gives a surjective stacked form already on the third arm. -/
theorem codimTwo_third_restriction_surjective (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂)) :
    Function.Surjective ((l₁.prod l₂).comp (T.A 2).subtype) := by
  intro y
  obtain ⟨r, hr⟩ := hwedge (-y.2, -y.1)
  have hr₀ : l₂ (r.1 0 : F) = -y.2 := congrArg Prod.fst hr
  have hr₁ : l₁ (r.1 1 : F) = -y.1 := congrArg Prod.snd hr
  have hz₀ : l₁ (r.1 0 : F) = 0 := h₁ (T.side_le_signal 0 (r.1 0).property)
  have hz₁ : l₂ (r.1 1 : F) = 0 := h₂ (T.side_le_signal 1 (r.1 1).property)
  have hs₀ := congrArg l₁ (relation_sum_eq_zero T.A r)
  have hs₁ := congrArg l₂ (relation_sum_eq_zero T.A r)
  simp only [map_add, map_zero, hz₀, hz₁, hr₀, hr₁, zero_add, add_zero] at hs₀ hs₁
  refine ⟨r.1 2, Prod.ext ?_ ?_⟩
  · change l₁ (r.1 2 : F) = y.1; linear_combination hs₀
  · change l₂ (r.1 2 : F) = y.2; linear_combination hs₁

section Dimensions
variable [FiniteDimensional K F]

/-- Rank-nullity for a nonzero restricted form, stated in the ambient space. -/
theorem hyperplane_intersection_finrank (A : Submodule K F) (l : F →ₗ[K] K)
    (h : ∃ a ∈ A, l a ≠ 0) :
    finrank K ↥(A ⊓ LinearMap.ker l) + 1 = finrank K A := by
  obtain ⟨a, ha, hla⟩ := h
  have hn : l.comp A.subtype ≠ 0 := by
    intro hh
    have hz := LinearMap.congr_fun hh ⟨a, ha⟩
    exact hla (by simpa using hz)
  have hr : LinearMap.range (l.comp A.subtype) = ⊤ :=
    LinearMap.range_eq_top.mpr (by
      intro y
      refine ⟨(y / l a) • ⟨a, ha⟩, ?_⟩
      simp [div_mul_cancel₀ _ hla])
  have hh := restriction_rank_add_kernel l A
  rw [hr, finrank_top, Module.finrank_self] at hh
  omega

/-- The codimension is exactly two, from the actual wedge rank. -/
theorem codimTwo_finrank (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂)) :
    finrank K ↥(LinearMap.ker l₁ ⊓ LinearMap.ker l₂) + 2 = finrank K F := by
  have hs := codimTwo_third_restriction_surjective T l₁ l₂ h₁ h₂ hwedge
  have hs' : Function.Surjective (l₁.prod l₂) := by
    intro y; obtain ⟨a, ha⟩ := hs y; exact ⟨a, ha⟩
  have hh := (l₁.prod l₂).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs', LinearMap.ker_prod, finrank_top,
    Module.finrank_prod, Module.finrank_self] at hh
  omega

/-- The third side loses exactly two dimensions. -/
theorem codimTwo_third_side_finrank (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂)) :
    finrank K ↥(T.A 2 ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂)) + 2 =
      finrank K (T.A 2) := by
  have hs := codimTwo_third_restriction_surjective T l₁ l₂ h₁ h₂ hwedge
  have hh := restriction_rank_add_kernel (l₁.prod l₂) (T.A 2)
  rw [LinearMap.range_eq_top.mpr hs, LinearMap.ker_prod, finrank_top,
    Module.finrank_prod, Module.finrank_self] at hh
  omega

/-- The first two sides each lose exactly one dimension in the wedge construction. -/
theorem codimTwo_first_two_side_finrank (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂)) :
    finrank K ↥(T.A 0 ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂)) + 1 =
        finrank K (T.A 0) ∧
      finrank K ↥(T.A 1 ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂)) + 1 =
        finrank K (T.A 1) := by
  have hA₀ : T.A 0 ≤ LinearMap.ker l₁ := (T.side_le_signal 0).trans h₁
  have hA₁ : T.A 1 ≤ LinearMap.ker l₂ := (T.side_le_signal 1).trans h₂
  have he₀ : T.A 0 ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) =
      T.A 0 ⊓ LinearMap.ker l₂ := by rw [← inf_assoc, inf_eq_left.mpr hA₀]
  have he₁ : T.A 1 ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) =
      T.A 1 ⊓ LinearMap.ker l₁ := by
    rw [inf_comm (LinearMap.ker l₁), ← inf_assoc, inf_eq_left.mpr hA₁]
  rw [he₀, he₁]
  obtain ⟨r, hr⟩ := hwedge (1,1)
  have hr₀ : l₂ (r.1 0 : F) = 1 := congrArg Prod.fst hr
  have hr₁ : l₁ (r.1 1 : F) = 1 := congrArg Prod.snd hr
  exact ⟨hyperplane_intersection_finrank _ _ ⟨_, (r.1 0).property, by rw [hr₀]; exact one_ne_zero⟩,
    hyperplane_intersection_finrank _ _ ⟨_, (r.1 1).property, by rw [hr₁]; exact one_ne_zero⟩⟩

/-- Relay feasibility preserves every user's conditioned demand dimension. -/
theorem relay_signal_dimension (T : Task K F) (P : Submodule K F)
    (hP : T.RelayFeasible P) (i : Three) :
    finrank K ↥(T.U i ⊓ P) - finrank K ↥(T.A i ⊓ P) =
      finrank K (T.U i) - finrank K (T.A i) := by
  have h := relay_condRank (T.A i) (T.U i) P (T.side_le_signal i) (hP i)
  unfold condRank at h
  rw [sup_eq_right.mpr (T.side_le_signal i),
    sup_eq_right.mpr (inf_le_inf (T.side_le_signal i) le_rfl)] at h
  exact h



/-- The three hyperplane side-space dimensions, with the untouched arm first. -/
theorem hyperplane_side_dimensions (T : Task K F) (l : F →ₗ[K] K)
    (hU : T.U 0 ≤ LinearMap.ker l)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a + b + c = 0) (hlb : l b ≠ 0) :
    finrank K ↥(T.A 0 ⊓ LinearMap.ker l) = finrank K (T.A 0) ∧
      finrank K ↥(T.A 1 ⊓ LinearMap.ker l) + 1 = finrank K (T.A 1) ∧
      finrank K ↥(T.A 2 ⊓ LinearMap.ker l) + 1 = finrank K (T.A 2) := by
  have hA : T.A 0 ≤ LinearMap.ker l := (T.side_le_signal 0).trans hU
  have hlc : l c ≠ 0 := by
    intro hc0
    have hh := congrArg l hrel
    have ha0 : l a = 0 := hA ha
    simp [ha0, hc0] at hh
    exact hlb hh
  exact ⟨by rw [inf_eq_left.mpr hA],
    hyperplane_intersection_finrank _ _ ⟨b,hb,hlb⟩,
    hyperplane_intersection_finrank _ _ ⟨c,hc,hlc⟩⟩

/-- For excess one, the total dimension of the actual local uploads equals
the relay dimension. This proves that no redundant upload is being counted. -/
theorem hyperplane_upload_dimension (T : Task K F) (l : F →ₗ[K] K)
    (hU : T.U 0 ≤ LinearMap.ker l)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a + b + c = 0) (hlb : l b ≠ 0)
    (hexcess : (∑ i, finrank K (T.A i)) = finrank K F + 1) :
    (∑ i, finrank K ↥(LinearMap.ker l ⊓ T.A i)) = finrank K (LinearMap.ker l) := by
  obtain ⟨h₀,h₁,h₂⟩ := hyperplane_side_dimensions T l hU a b c ha hb hc hrel hlb
  have hn : l ≠ 0 := by intro hz; exact hlb (by simp [hz])
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  simp only [Fin.sum_univ_three] at hexcess ⊢
  rw [inf_comm (T.A 0)] at h₀
  rw [inf_comm (T.A 1)] at h₁
  rw [inf_comm (T.A 2)] at h₂
  omega

/-- For excess two, the wedge construction likewise uses exactly the relay
space's dimension in local uploads. -/
theorem codimTwo_upload_dimension (T : Task K F) (l₁ l₂ : F →ₗ[K] K)
    (h₁ : T.U 0 ≤ LinearMap.ker l₁) (h₂ : T.U 1 ≤ LinearMap.ker l₂)
    (hwedge : Function.Surjective (relationEvaluation T.A l₁ l₂))
    (hexcess : (∑ i, finrank K (T.A i)) = finrank K F + 2) :
    (∑ i, finrank K ↥((LinearMap.ker l₁ ⊓ LinearMap.ker l₂) ⊓ T.A i)) =
      finrank K ↥(LinearMap.ker l₁ ⊓ LinearMap.ker l₂) := by
  have hfirst := codimTwo_first_two_side_finrank T l₁ l₂ h₁ h₂ hwedge
  have hthird := codimTwo_third_side_finrank T l₁ l₂ h₁ h₂ hwedge
  have hd := codimTwo_finrank T l₁ l₂ h₁ h₂ hwedge
  simp only [Fin.sum_univ_three] at hexcess ⊢
  rw [inf_comm (T.A 0), inf_comm (T.A 1)] at hfirst
  rw [inf_comm (T.A 2)] at hthird
  omega

/-- A pair or triple already lying in the relay has unchanged conditional
rank, even though the conditioning side space is also restricted. -/
theorem condRank_unchanged_of_le (A B P : Submodule K F) (hB : B ≤ P) :
    condRank (B ⊓ P) (A ⊓ P) = condRank B A := by
  rw [inf_eq_left.mpr hB]
  have heq : (A ⊓ P) ⊓ B = A ⊓ B := by
    rw [inf_assoc, inf_eq_right.mpr hB]
  have h₁ := condRank_add_intersection B A
  have h₂ := condRank_add_intersection B (A ⊓ P)
  rw [heq] at h₂
  omega

/-- Exact remote-pair maximal rank after cutting by a hyperplane. The form
must be nonzero on the pair and on its intersection with the side space
whenever that intersection has positive dimension. This is the rank
transport calculation in Step 4 of `lem:same-chart`. -/
theorem hyperplane_pair_maximal_rank (A B : Submodule K F)
    (l : F →ₗ[K] K) (m p : ℕ)
    (hp : finrank K B = p) (hr : condRank B A = min m p)
    (hB : ∃ b ∈ B, l b ≠ 0)
    (hAB : 0 < finrank K ↥(A ⊓ B) → ∃ b ∈ A ⊓ B, l b ≠ 0) :
    condRank (B ⊓ LinearMap.ker l) (A ⊓ LinearMap.ker l) = min m (p-1) := by
  have hd := hyperplane_intersection_finrank B l hB
  have hc := condRank_add_intersection B A
  have hc' := condRank_add_intersection (B ⊓ LinearMap.ker l) (A ⊓ LinearMap.ker l)
  have heq : (A ⊓ LinearMap.ker l) ⊓ (B ⊓ LinearMap.ker l) =
      (A ⊓ B) ⊓ LinearMap.ker l := by rw [inf_inf_inf_comm, inf_idem]
  rw [heq] at hc'
  by_cases hpos : 0 < finrank K ↥(A ⊓ B)
  · have hi := hyperplane_intersection_finrank (A ⊓ B) l (hAB hpos)
    omega
  · have hi := Submodule.finrank_mono
      (inf_le_left : (A ⊓ B) ⊓ LinearMap.ker l ≤ A ⊓ B)
    omega


/-- On a pair killed by the first form, the codimension-two conditional-rank
calculation reduces exactly to the second hyperplane calculation. -/
theorem codimTwo_condRank_reduction (A B : Submodule K F) (l₁ l₂ : F →ₗ[K] K)
    (hB : B ≤ LinearMap.ker l₁) :
    condRank (B ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂))
        (A ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂)) =
      condRank (B ⊓ LinearMap.ker l₂) (A ⊓ LinearMap.ker l₂) := by
  have h := condRank_unchanged_of_le (A ⊓ LinearMap.ker l₂)
    (B ⊓ LinearMap.ker l₂) (LinearMap.ker l₁) (inf_le_left.trans hB)
  simpa only [inf_assoc, inf_comm, inf_left_comm] using h

/-- The remote-pair maximal rank calculation for a codimension-two relay. -/
theorem codimTwo_pair_maximal_rank (A B : Submodule K F)
    (l₁ l₂ : F →ₗ[K] K) (m p : ℕ) (hB₁ : B ≤ LinearMap.ker l₁)
    (hp : finrank K B = p) (hr : condRank B A = min m p)
    (hB₂ : ∃ b ∈ B, l₂ b ≠ 0)
    (hAB : 0 < finrank K ↥(A ⊓ B) → ∃ b ∈ A ⊓ B, l₂ b ≠ 0) :
    condRank (B ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂))
        (A ⊓ (LinearMap.ker l₁ ⊓ LinearMap.ker l₂)) = min m (p-1) := by
  rw [codimTwo_condRank_reduction A B l₁ l₂ hB₁]
  exact hyperplane_pair_maximal_rank A B l₂ m p hp hr hB₂ hAB

/-- Over a field of size at least three one form can vanish on a prescribed
signal subspace while remaining nonzero on any three vectors outside it.
These vectors can be a relation projection and remote-intersection witnesses. -/
theorem exists_annihilating_form_three [Fintype K]
    (hq : 3 ≤ Fintype.card K) (U : Submodule K F) (v : Three → F)
    (hv : ∀ i, v i ∉ U) :
    ∃ l : F →ₗ[K] K, U ≤ LinearMap.ker l ∧ ∀ i, l (v i) ≠ 0 := by
  classical
  letI : Fintype U.dualAnnihilator := Fintype.ofEquiv _
    (IsNoetherian.finsetBasis K U.dualAnnihilator).equivFun.symm.toEquiv
  let e : Three → U.dualAnnihilator →ₗ[K] K := fun i =>
    (Module.Dual.eval K F (v i)).comp U.dualAnnihilator.subtype
  have he : ∀ i, e i ≠ 0 := by
    intro i hz
    apply hv i
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U (v i)).mp
    intro l hl
    have hh := LinearMap.congr_fun hz ⟨l, hl⟩
    simpa [e] using hh
  obtain ⟨l, hl⟩ := exists_forall_linearForm_ne_zero (K := K) (V := U.dualAnnihilator) (I := Three) e he (by simpa [Three] using hq)
  refine ⟨l.1, ?_, hl⟩
  intro x hx
  exact (Submodule.mem_dualAnnihilator l.1).mp l.property x hx

/-- Finite-field existence of an actual hyperplane relay, with two additional
rank-preserving nonvanishing conditions selected simultaneously. -/
theorem exists_hyperplane_relay [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F) (hspan : T.Spanning)
    (a b c v w : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a + b + c = 0)
    (hbU : b ∉ T.U 0) (hvU : v ∉ T.U 0) (hwU : w ∉ T.U 0) :
    ∃ l : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l ∧ l b ≠ 0 ∧ l v ≠ 0 ∧ l w ≠ 0 ∧
      T.LocallyGenerated (LinearMap.ker l) ∧ T.RelayFeasible (LinearMap.ker l) ∧
      finrank K (LinearMap.ker l) + 1 = finrank K F := by
  obtain ⟨l, hU, hl⟩ := exists_annihilating_form_three hq (T.U 0) ![b,v,w]
    (by intro i; fin_cases i <;> simpa using (by assumption))
  have hb' : l b ≠ 0 := hl 0
  have hv' : l v ≠ 0 := hl 1
  have hw' : l w ≠ 0 := hl 2
  have hg := hyperplane_relay T l hspan hU a b c ha hb hc hrel hb'
  have hn : l ≠ 0 := by intro hz; apply hb'; simp [hz]
  exact ⟨l, hU, hb', hv', hw', hg.1, hg.2,
    Module.Dual.finrank_ker_add_one_of_ne_zero hn⟩


/-- A witness in a nonzero transverse intersection; if that intersection is
zero, use any remote-pair witness outside the distinguished signal space. -/
theorem exists_rank_witness (C B U : Submodule K F) (hCB : C ≤ B)
    (hdisjoint : Disjoint C U) (hB : ¬ B ≤ U) :
    ∃ v ∈ B, v ∉ U ∧ (0 < finrank K C → v ∈ C) := by
  by_cases hC : C = ⊥
  · obtain ⟨v,hv,hvU⟩ := SetLike.not_le_iff_exists.mp hB
    exact ⟨v,hv,hvU,by simp [hC]⟩
  · have hCU : ¬ C ≤ U := fun h => hC (hdisjoint.eq_bot_of_le h)
    obtain ⟨v,hv,hvU⟩ := SetLike.not_le_iff_exists.mp hCU
    exact ⟨v,hCB hv,hvU,fun _ => hv⟩

/-- The hyperplane's remote maximal conditional ranks are achieved by the
same finite-field form that gives local generation and feasibility. This
combines kernel avoidance with rank transport on actual subspaces. -/
theorem exists_hyperplane_relay_with_remote_ranks [Fintype K]
    (hq : 3 ≤ Fintype.card K) (T : Task K F) (hspan : T.Spanning)
    (a b c : F) (ha : a ∈ T.A 0) (hb : b ∈ T.A 1) (hc : c ∈ T.A 2)
    (hrel : a + b + c = 0) (hbU : b ∉ T.U 0)
    (hremote : ¬ T.U 1 ⊓ T.U 2 ≤ T.U 0)
    (hC₁ : Disjoint (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 0))
    (hC₂ : Disjoint (T.A 2 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 0))
    (m₁ m₂ p : ℕ) (hp : finrank K ↥(T.U 1 ⊓ T.U 2) = p)
    (hr₁ : condRank (T.U 1 ⊓ T.U 2) (T.A 1) = min m₁ p)
    (hr₂ : condRank (T.U 1 ⊓ T.U 2) (T.A 2) = min m₂ p) :
    ∃ l : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l ∧ T.LocallyGenerated (LinearMap.ker l) ∧
      T.RelayFeasible (LinearMap.ker l) ∧
      finrank K (LinearMap.ker l) + 1 = finrank K F ∧
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)
        (T.A 1 ⊓ LinearMap.ker l) = min m₁ (p-1) ∧
      condRank ((T.U 1 ⊓ T.U 2) ⊓ LinearMap.ker l)
        (T.A 2 ⊓ LinearMap.ker l) = min m₂ (p-1) := by
  obtain ⟨v,hv,hvU,hvC⟩ := exists_rank_witness
    (T.A 1 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 1 ⊓ T.U 2) (T.U 0) inf_le_right hC₁ hremote
  obtain ⟨w,hw,hwU,hwC⟩ := exists_rank_witness
    (T.A 2 ⊓ (T.U 1 ⊓ T.U 2)) (T.U 1 ⊓ T.U 2) (T.U 0) inf_le_right hC₂ hremote
  obtain ⟨l,hU,_,hlv,hlw,hgen,hfeas,hd⟩ :=
    exists_hyperplane_relay hq T hspan a b c v w ha hb hc hrel hbU hvU hwU
  exact ⟨l,hU,hgen,hfeas,hd,
    hyperplane_pair_maximal_rank _ _ l m₁ p hp hr₁ ⟨v,hv,hlv⟩
      (fun h => ⟨v,hvC h,hlv⟩),
    hyperplane_pair_maximal_rank _ _ l m₂ p hp hr₂ ⟨w,hw,hlw⟩
      (fun h => ⟨w,hwC h,hlw⟩)⟩

/-- Sequential selection of the two forms in the codimension-two case.
Each stage avoids precisely three proper linear kernels. -/
theorem exists_bilinear_nonzero_with_two_constraints
    {X Y : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [Fintype K] (hq : 3 ≤ Fintype.card K)
    (B : X →ₗ[K] Y →ₗ[K] K) (hB : B ≠ 0)
    (f₀ f₁ : X →ₗ[K] K) (g₀ g₁ : Y →ₗ[K] K)
    (hf₀ : f₀ ≠ 0) (hf₁ : f₁ ≠ 0) (hg₀ : g₀ ≠ 0) (hg₁ : g₁ ≠ 0) :
    ∃ x y, f₀ x ≠ 0 ∧ f₁ x ≠ 0 ∧ g₀ y ≠ 0 ∧ g₁ y ≠ 0 ∧ B x y ≠ 0 := by
  classical
  letI : Fintype X := Fintype.ofEquiv _ (IsNoetherian.finsetBasis K X).equivFun.symm.toEquiv
  letI : Fintype Y := Fintype.ofEquiv _ (IsNoetherian.finsetBasis K Y).equivFun.symm.toEquiv
  have hw : ∃ x y, B x y ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hB
    ext x y
    exact hn x y
  obtain ⟨x₀,y₀,hxy⟩ := hw
  have hn : B.flip y₀ ≠ 0 := by
    intro hz
    have hh := LinearMap.congr_fun hz x₀
    exact hxy hh
  obtain ⟨x,hx⟩ := exists_forall_linearForm_ne_zero (K := K) (V := X) (I := Three)
    ![f₀,f₁,B.flip y₀] (by intro i; fin_cases i <;> simpa using (by assumption))
    (by simpa [Three] using hq)
  have hn' : B x ≠ 0 := by
    intro hz
    have hh : B x y₀ ≠ 0 := hx 2
    exact hh (LinearMap.congr_fun hz y₀)
  obtain ⟨y,hy⟩ := exists_forall_linearForm_ne_zero (K := K) (V := Y) (I := Three)
    ![g₀,g₁,B x] (by intro i; fin_cases i <;> simpa using (by assumption))
    (by simpa [Three] using hq)
  exact ⟨x,y,hx 0,hx 1,hy 0,hy 1,hy 2⟩

/-- Evaluation at a coefficient vector, restricted to the annihilator of U. -/
def annihilatorEvaluation (U : Submodule K F) (v : F) : U.dualAnnihilator →ₗ[K] K :=
  (Module.Dual.eval K F v).comp U.dualAnnihilator.subtype

omit [FiniteDimensional K F] in
theorem annihilatorEvaluation_ne_zero (U : Submodule K F) (v : F) (hv : v ∉ U) :
    annihilatorEvaluation U v ≠ 0 := by
  intro hz
  apply hv
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U v).mp
  intro l hl
  have hh := LinearMap.congr_fun hz ⟨l,hl⟩
  exact hh

/-- The actual relation determinant as a bilinear form on the two signal
annihilators. Its nonzeroness is the geometric open-condition input, not a
hypothesis about the relay's output profile. -/
def relationWedge (T : Task K F)
    (r w : LinearMap.ker (AlignedRelation.signalSum T.A)) :
    (T.U 0).dualAnnihilator →ₗ[K] (T.U 1).dualAnnihilator →ₗ[K] K where
  toFun l₁ :=
    { toFun := fun l₂ => l₂.1 (r.1 0 : F) * l₁.1 (w.1 1 : F) -
        l₂.1 (w.1 0 : F) * l₁.1 (r.1 1 : F)
      map_add' := by intro a b; simp; ring
      map_smul' := by intro a b; simp; ring }
  map_add' := by intro a b; ext c; simp; ring
  map_smul' := by intro a b; ext c; simp; ring

/-- Actual finite-field codimension-two relay existence. The four vectors
can be chosen in the remote side/signal intersections used by the source.
The only wedge assumption is nonzeroness on the two signal annihilators. -/
theorem exists_codimTwo_relay [Fintype K] (hq : 3 ≤ Fintype.card K)
    (T : Task K F) (hspan : T.Spanning)
    (r w : LinearMap.ker (AlignedRelation.signalSum T.A))
    (hB : relationWedge T r w ≠ 0)
    (v₀ v₁ w₀ w₁ : F)
    (hv₀ : v₀ ∉ T.U 0) (hv₁ : v₁ ∉ T.U 0)
    (hw₀ : w₀ ∉ T.U 1) (hw₁ : w₁ ∉ T.U 1) :
    ∃ l₁ l₂ : F →ₗ[K] K,
      T.U 0 ≤ LinearMap.ker l₁ ∧ T.U 1 ≤ LinearMap.ker l₂ ∧
      l₁ v₀ ≠ 0 ∧ l₁ v₁ ≠ 0 ∧ l₂ w₀ ≠ 0 ∧ l₂ w₁ ≠ 0 ∧
      T.LocallyGenerated (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) ∧
      T.RelayFeasible (LinearMap.ker l₁ ⊓ LinearMap.ker l₂) ∧
      finrank K ↥(LinearMap.ker l₁ ⊓ LinearMap.ker l₂) + 2 = finrank K F := by
  obtain ⟨l₁,l₂,hv₀',hv₁',hw₀',hw₁',hwedge⟩ :=
    exists_bilinear_nonzero_with_two_constraints (K := K)
      (X := (T.U 0).dualAnnihilator) (Y := (T.U 1).dualAnnihilator)
      hq (relationWedge T r w) hB
      (annihilatorEvaluation (T.U 0) v₀) (annihilatorEvaluation (T.U 0) v₁)
      (annihilatorEvaluation (T.U 1) w₀) (annihilatorEvaluation (T.U 1) w₁)
      (annihilatorEvaluation_ne_zero _ _ hv₀) (annihilatorEvaluation_ne_zero _ _ hv₁)
      (annihilatorEvaluation_ne_zero _ _ hw₀) (annihilatorEvaluation_ne_zero _ _ hw₁)
  have h₁ : T.U 0 ≤ LinearMap.ker l₁.1 := by
    intro x hx; exact (Submodule.mem_dualAnnihilator l₁.1).mp l₁.property x hx
  have h₂ : T.U 1 ≤ LinearMap.ker l₂.1 := by
    intro x hx; exact (Submodule.mem_dualAnnihilator l₂.1).mp l₂.property x hx
  have hs : Function.Surjective (relationEvaluation T.A l₁.1 l₂.1) :=
    surjective_of_wedge (relationEvaluation T.A l₁.1 l₂.1) r w hwedge
  exact ⟨l₁.1,l₂.1,h₁,h₂,hv₀',hv₁',hw₀',hw₁',
    codimTwo_locally_generated T l₁.1 l₂.1 hspan h₁ h₂ hs,
    codimTwo_feasible T l₁.1 l₂.1 h₁ h₂ hs,
    codimTwo_finrank T l₁.1 l₂.1 h₁ h₂ hs⟩

end Dimensions
end UploadBroadcast.NonzeroDefectRelays
