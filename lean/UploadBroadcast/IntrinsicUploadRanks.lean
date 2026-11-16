import UploadBroadcast.OriginalUploadTheorem
import UploadBroadcast.ResidualIntrinsicGeometry
import UploadBroadcast.RelayProfileTransport

/-!
# Intrinsic upload ranks and arbitrary chart choices

The intrinsic row spaces below live in the first tripod side core. They align
all three users' pure rows without choosing a basis, a complement, or a lift.
-/
namespace UploadBroadcast.IntrinsicUploadRanks
open ResidualUpload ResidualTaskAssembly Module
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F V P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

def pure₀ (T : Task K F) : Submodule K F :=
  T.A 0 ⊓ ((T.A 1 ⊓ T.U 0) ⊔ T.A 2)
def pure₁ (T : Task K F) : Submodule K F :=
  (T.A 0 ⊓ (T.A 1 ⊔ T.A 2)) ⊓ T.U 1
def pure₂ (T : Task K F) : Submodule K F :=
  (T.A 0 ⊓ (T.A 1 ⊔ T.A 2)) ⊓ T.U 2

/-- All three aligned pure spaces are natural under every ambient equivalence. -/
theorem pure_map (T : Task K F) (e : F ≃ₗ[K] V) :
    pure₀ (Profile.mapTask e T) = (pure₀ T).map e.toLinearMap ∧
    pure₁ (Profile.mapTask e T) = (pure₁ T).map e.toLinearMap ∧
    pure₂ (Profile.mapTask e T) = (pure₂ T).map e.toLinearMap := by
  simp only [pure₀,pure₁,pure₂,Profile.mapTask,Submodule.map_inf e.toLinearMap e.injective,
    Submodule.map_sup,and_self]

variable (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

include h₀ h₁ h₂
/-- Exact coordinate-free realizations of each pure demand row space. -/
theorem pure_eq_images :
    pure₀ task = (pureRows₁ task).map (embedV (K := K)) ∧
    pure₁ task = (pureRows₂ task).map (embedV (K := K)) ∧
    pure₂ task = (pureRows₃ task).map (embedV (K := K)) := by
  let g := selectedDemandData task h₀ h₁ h₂
  obtain ⟨hd₀,hd₁,hd₂⟩ := g.pureRows_iff
  have hcore := ResidualIntrinsicGeometry.tripod_side_core task h₀ h₁ h₂
  refine ⟨?_,?_,?_⟩
  · apply le_antisymm
    · rintro x ⟨ha,hx⟩
      rw [h₀] at ha
      obtain ⟨⟨p,d⟩,rfl⟩ := ha
      obtain ⟨b,⟨hbA,hbU⟩,c,hcA,he⟩ := Submodule.mem_sup.mp hx
      rw [h₁] at hbA
      rw [h₂] at hcA
      obtain ⟨⟨q,e⟩,rfl⟩ := hbA
      obtain ⟨⟨r,f⟩,rfl⟩ := hcA
      have hp : p = 0 := by
        simpa [side₁,side₂,side₃] using
          (congrArg (fun z : Ambient P₁ P₂ P₃ D => z.1.1.1) he).symm
      have hq : q = 0 := by
        simpa [side₁,side₂,side₃] using
          congrArg (fun z : Ambient P₁ P₂ P₃ D => z.1.1.2) he
      have hf : -f = d := by
        simpa [side₁,side₂,side₃] using
          congrArg (fun z : Ambient P₁ P₂ P₃ D => z.2.1) he
      have hef : e + f = 0 := by
        simpa [side₁,side₂,side₃] using
          congrArg (fun z : Ambient P₁ P₂ P₃ D => z.2.2) he
      have hed : e = d := (eq_neg_of_add_eq_zero_left hef).trans hf
      refine ⟨d,(hd₀ d).mpr ?_,?_⟩
      · simpa [hq,hed,side₂,embedR] using hbU
      · simp [hp,side₁,embedV]
    · rintro x ⟨d,hd,rfl⟩
      refine ⟨?_,?_⟩
      · rw [h₀]; exact ⟨(0,d),rfl⟩
      · apply Submodule.mem_sup.mpr
        refine ⟨embedR (K := K) d,⟨?_,(hd₀ d).mp hd⟩,
          side₃ (K := K) (0,-d),?_,?_⟩
        · rw [h₁]; exact ⟨(0,d),rfl⟩
        · rw [h₂]; exact ⟨(0,-d),rfl⟩
        · ext <;> simp [embedR,embedV,side₁,side₂,side₃]
  · unfold pure₁
    rw [hcore]
    ext x
    constructor
    · rintro ⟨⟨d,rfl⟩,hd⟩
      exact ⟨d,(hd₁ d).mpr hd,rfl⟩
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,rfl⟩,(hd₁ d).mp hd⟩
  · unfold pure₂
    rw [hcore]
    ext x
    constructor
    · rintro ⟨⟨d,rfl⟩,hd⟩
      exact ⟨d,(hd₂ d).mpr hd,rfl⟩
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,rfl⟩,(hd₂ d).mp hd⟩

omit h₀ h₁ h₂ in
lemma embedV_injective : Function.Injective
    (embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) := by
  intro x y h
  exact congrArg (fun z : Ambient P₁ P₂ P₃ D => z.2.1) h

noncomputable def commonRank (T : Task K F) : ℕ :=
  finrank K ↥(pure₀ T ⊓ pure₁ T ⊓ pure₂ T)
noncomputable def pureRank (T : Task K F) : ℕ :=
  finrank K ↥(pure₀ T ⊔ pure₁ T ⊔ pure₂ T) - commonRank T
noncomputable def privateRank [FiniteDimensional K F] (T : Task K F) : ℕ :=
  condRank (T.U 1 ⊔ T.U 2) (T.A 1 ⊔ T.A 2) +
  condRank (T.U 0 ⊔ T.U 2) (T.A 0 ⊔ T.A 2) +
  condRank (T.U 0 ⊔ T.U 1) (T.A 0 ⊔ T.A 1)

/-- The common pure count is the dimension of an intrinsic triple intersection. -/
theorem commonDimension_eq_intrinsic [FiniteDimensional K D] :
    commonDimension task = commonRank task := by
  obtain ⟨ha,hb,hc⟩ := pure_eq_images task h₀ h₁ h₂
  obtain ⟨ht₀,ht₁,ht₂⟩ := privateTrim_pureRows task h₀ h₁ h₂
  unfold commonDimension CommonTripodAssembly.commonRows commonRank
  rw [ht₀,ht₁,ht₂,ha,hb,hc,← Submodule.map_inf _ embedV_injective,
    ← Submodule.map_inf _ embedV_injective]
  exact (Submodule.equivMapOfInjective (embedV (K := K)) embedV_injective _).finrank_eq

/-- The pure noncommon count is an intrinsic aligned-sum quotient dimension. -/
theorem pureRank_eq [FiniteDimensional K D] :
    pureRank task = finrank K ↥(pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task) -
      commonDimension task := by
  obtain ⟨ha,hb,hc⟩ := pure_eq_images task h₀ h₁ h₂
  unfold pureRank
  rw [ha,hb,hc,← Submodule.map_sup,← Submodule.map_sup,
    ← commonDimension_eq_intrinsic task h₀ h₁ h₂,
    ← (Submodule.equivMapOfInjective (embedV (K := K)) embedV_injective _).finrank_eq]

omit h₀ h₁ h₂
/-- These definitions contain only subspaces of the original ambient task. -/
theorem ranks_map [FiniteDimensional K F] [FiniteDimensional K V]
    (T : Task K F) (e : F ≃ₗ[K] V) :
    commonRank (Profile.mapTask e T) = commonRank T ∧
    pureRank (Profile.mapTask e T) = pureRank T ∧
    privateRank (Profile.mapTask e T) = privateRank T := by
  obtain ⟨h₀,h₁,h₂⟩ := pure_map T e
  have hc : commonRank (Profile.mapTask e T) = commonRank T := by
    unfold commonRank
    rw [h₀,h₁,h₂,← Submodule.map_inf e.toLinearMap e.injective,← Submodule.map_inf e.toLinearMap e.injective,
      e.finrank_map_eq]
  refine ⟨hc,?_,?_⟩
  · unfold pureRank
    rw [h₀,h₁,h₂,← Submodule.map_sup,← Submodule.map_sup,e.finrank_map_eq,hc]
  · simp only [privateRank,Profile.mapTask,←Submodule.map_sup,Profile.condRank_map]


/-- Rank of any linear projection is the conditional rank modulo its kernel. -/
theorem map_finrank_eq_condRank [FiniteDimensional K F]
    (A : Submodule K F) (f : F →ₗ[K] V) :
    finrank K (A.map f) = condRank A (LinearMap.ker f) := by
  have hr := restriction_rank_add_kernel f A
  rw [LinearMap.range_comp,Submodule.range_subtype,inf_comm] at hr
  have hs := condRank_add_intersection A (LinearMap.ker f)
  omega

/-- Private projection kernels are exactly the sum of the two remote sides. -/
theorem private_kernels :
    LinearMap.ker (private₁ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) =
      A₂ K P₁ P₂ P₃ D ⊔ A₃ K P₁ P₂ P₃ D ∧
    LinearMap.ker (private₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) =
      A₁ K P₁ P₂ P₃ D ⊔ A₃ K P₁ P₂ P₃ D ∧
    LinearMap.ker (private₃ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) =
      A₁ K P₁ P₂ P₃ D ⊔ A₂ K P₁ P₂ P₃ D := by
  refine ⟨?_,?_,?_⟩
  · ext x
    constructor
    · intro hx
      have hz : x.1.1.1 = 0 := hx
      refine Submodule.mem_sup.mpr ⟨side₂ (x.1.1.2,x.2.2+x.2.1),⟨_,rfl⟩,
        side₃ (x.1.2,-x.2.1),⟨_,rfl⟩,?_⟩
      ext <;> simp [side₂,side₃,hz]
    · intro hx
      obtain ⟨a,⟨p,rfl⟩,b,⟨q,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
      change (0 : P₁) + 0 = 0
      simp
  · ext x
    constructor
    · intro hx
      have hz : x.1.1.2 = 0 := hx
      refine Submodule.mem_sup.mpr ⟨side₁ (x.1.1.1,x.2.1+x.2.2),⟨_,rfl⟩,
        side₃ (x.1.2,x.2.2),⟨_,rfl⟩,?_⟩
      ext <;> simp [side₁,side₃,hz]
    · intro hx
      obtain ⟨a,⟨p,rfl⟩,b,⟨q,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
      change (0 : P₂) + 0 = 0
      simp
  · ext x
    constructor
    · intro hx
      have hz : x.1.2 = 0 := hx
      refine Submodule.mem_sup.mpr ⟨side₁ (x.1.1.1,x.2.1),⟨_,rfl⟩,
        side₂ (x.1.1.2,x.2.2),⟨_,rfl⟩,?_⟩
      ext <;> simp [side₁,side₂,hz]
    · intro hx
      obtain ⟨a,⟨p,rfl⟩,b,⟨q,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
      change (0 : P₃) + 0 = 0
      simp


include h₀ h₁ h₂
/-- Every legal chart's retained private dimension equals an intrinsic formula. -/
theorem privateDimension_eq_intrinsic
    [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K D] :
    privateDimension task = privateRank task := by
  unfold privateDimension used₁ used₂ used₃ privateRank
  rw [←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,
    map_finrank_eq_condRank,map_finrank_eq_condRank,map_finrank_eq_condRank,
    private_kernels.1,private_kernels.2.1,private_kernels.2.2,h₀,h₁,h₂]

omit h₀ h₁ h₂ in
/-- Arbitrary choices of demand-graph lifts induce exactly the same quotient
row map, before restricting to the private-cancellation kernel. -/
theorem quotient_relationRows_eq (g h : DemandData task) :
    (pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task).mkQ.comp g.relationRows =
      (pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task).mkQ.comp h.relationRows := by
  apply LinearMap.ext
  intro x
  apply (Submodule.Quotient.eq _).mpr
  have h₁ (p : privateDomain₁ task) : g.φ₁ p - h.φ₁ p ∈ pureRows₁ task := by
    have hg := (g.mem₁ (((0,p.val.1),p.val.2),(0,g.φ₁ p))).mpr
      ⟨p.property,by simp⟩
    exact ((h.mem₁ _).mp hg).2
  have h₂ (p : privateDomain₂ task) : g.φ₂ p - h.φ₂ p ∈ pureRows₂ task := by
    have hg := (g.mem₂ (((p.val.1,0),p.val.2),(g.φ₂ p,0))).mpr
      ⟨p.property,by simp⟩
    exact ((h.mem₂ _).mp hg).2
  have h₃ (p : privateDomain₃ task) : g.φ₃ p - h.φ₃ p ∈ pureRows₃ task := by
    have hg := (g.mem₃ (((p.val.1,p.val.2),0),(g.φ₃ p,0))).mpr
      ⟨p.property,by simp⟩
    simpa only [add_zero] using ((h.mem₃ _).mp hg).2
  have hh := Submodule.add_mem_sup (Submodule.add_mem_sup (h₁ x.1.1) (h₂ x.1.2)) (h₃ x.2)
  convert hh using 1
  simp only [LinearMap.comp_apply,DemandData.relationRows,LinearMap.coe_mk,AddHom.coe_mk]
  abel

omit h₀ h₁ h₂ in
/-- Consequently the mixed rank is independent of all graph-lift choices. -/
theorem mixedRank_lift_independent (g h : DemandData task) :
    finrank K ((LinearMap.ker (DemandData.incidence (task := task))).map
      ((pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task).mkQ.comp g.relationRows)) =
    finrank K ((LinearMap.ker (DemandData.incidence (task := task))).map
      ((pureRows₁ task ⊔ pureRows₂ task ⊔ pureRows₃ task).mkQ.comp h.relationRows)) := by
  rw [quotient_relationRows_eq task g h]

end UploadBroadcast.IntrinsicUploadRanks

namespace UploadBroadcast.Task.PrivateTripodChart
open Module ResidualTaskAssembly IntrinsicUploadRanks
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] {S : Task K F} (c d : S.PrivateTripodChart)

/-- Noncommon pure rank evaluated in an arbitrary legal side chart. -/
noncomputable def pureDimension : ℕ :=
  finrank K ↥(pureRows₁ (privateTrim c.toTask) ⊔ pureRows₂ (privateTrim c.toTask) ⊔
    pureRows₃ (privateTrim c.toTask)) - c.commonDimension

/-- Mixed rank evaluated from the actual selected graph presentation. -/
noncomputable def mixedDimension : ℕ :=
  let T := privateTrim c.toTask
  let g := selectedTrimData c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  finrank K ((LinearMap.ker (DemandData.incidence (task := T))).map
    ((pureRows₁ T ⊔ pureRows₂ T ⊔ pureRows₃ T).mkQ.comp g.relationRows))

/-- Private and pure ranks in every legal chart equal fixed intrinsic ranks
of the same original pair-free task. -/
theorem dimensions_eq_intrinsic :
    c.privateDimension = privateRank S ∧ c.commonDimension = commonRank S ∧
      c.pureDimension = pureRank S := by
  have hm := ranks_map S c.chart.symm
  have hc := commonDimension_eq_intrinsic c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  have hp := privateDimension_eq_intrinsic c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  have hd := pureRank_eq c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  obtain ⟨ht₀,ht₁,ht₂⟩ := privateTrim_pureRows c.toTask c.sides.1 c.sides.2.1 c.sides.2.2
  refine ⟨hp.trans hm.2.2,hc.trans hm.1,?_⟩
  unfold pureDimension
  rw [ht₀,ht₁,ht₂]
  exact hd.symm.trans hm.2.1

/-- Pairwise chart independence, without selecting a preferred chart. -/
theorem private_common_pure_independent :
    c.privateDimension = d.privateDimension ∧ c.commonDimension = d.commonDimension ∧
      c.pureDimension = d.pureDimension := by
  obtain ⟨hc₀,hc₁,hc₂⟩ := c.dimensions_eq_intrinsic
  obtain ⟨hd₀,hd₁,hd₂⟩ := d.dimensions_eq_intrinsic
  exact ⟨hc₀.trans hd₀.symm,hc₁.trans hd₁.symm,hc₂.trans hd₂.symm⟩

/-- The source's pure-plus-mixed decomposition in every legal chart. -/
theorem tripod_eq_pure_add_mixed :
    c.tripodDimension = c.pureDimension + c.mixedDimension :=
  tripodDimension_eq_pure_mixed c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

end UploadBroadcast.Task.PrivateTripodChart
