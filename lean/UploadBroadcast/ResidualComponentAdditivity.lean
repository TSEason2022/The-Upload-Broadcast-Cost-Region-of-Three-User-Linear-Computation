import UploadBroadcast.FiniteComponentCoordinates
import UploadBroadcast.OriginalUploadOptimum
import UploadBroadcast.ResidualRelayAssembly
import UploadBroadcast.OperationalBounds
import UploadBroadcast.GeometricUploadConverse
import UploadBroadcast.ResidualOperational
import UploadBroadcast.CommonTripodRanks
import UploadBroadcast.ResidualIntrinsicGeometry
import UploadBroadcast.OriginalUploadRanks

/-!
# Actual active-residual components and upload additivity

Activity is expressed through the actual six coefficient subspaces. These
conditions commute with simultaneous direct sums; no component activity or
component upload optimum is postulated.
-/
namespace UploadBroadcast.ResidualComponentAdditivity
open Module
open scoped BigOperators
variable {K F V I : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096

/-- The first side of the fully demanded common tripod, expressed without
choosing tripod or private coordinates. -/
def commonSeed (T : Task K F) : Submodule K F :=
  (T.A 0 ⊓ (T.U 0 ⊓ T.U 1 ⊓ T.U 2)) ⊓
    ((T.A 1 ⊓ (T.U 0 ⊓ T.U 1 ⊓ T.U 2)) ⊔
      (T.A 2 ⊓ (T.U 0 ⊓ T.U 1 ⊓ T.U 2)))

/-- Intrinsic active residual geometry: no pair-known coefficients, full
private use, the active-tripod signal bridge, and no common omniscience rows. -/
structure ActiveResidual (T : Task K F) : Prop where
  disjoint₀₁ : Disjoint (T.A 0) (T.A 1)
  disjoint₀₂ : Disjoint (T.A 0) (T.A 2)
  disjoint₁₂ : Disjoint (T.A 1) (T.A 2)
  spanning : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤
  private_active : ∀ i j, i ≠ j → T.U i ⊔ T.U j = ⊤
  tripod_active : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) ≤ T.U 2 ⊔ (T.U 0 ⊓ T.U 1)
  common_zero : commonSeed T = ⊥

/-- Exact transport of the common fully-demanded tripod seed. -/
theorem commonSeed_map (T : Task K F) (e : F ≃ₗ[K] V) :
    commonSeed (Profile.mapTask e T) = (commonSeed T).map e.toLinearMap := by
  simp only [commonSeed,Profile.mapTask,Submodule.map_inf e.toLinearMap e.injective,
    Submodule.map_sup]

/-- Every intrinsic activity condition is unchanged by coefficient coordinates. -/
theorem ActiveResidual.map {T : Task K F} (h : ActiveResidual T) (e : F ≃ₗ[K] V) :
    ActiveResidual (Profile.mapTask e T) := by
  have hb : (⊥ : Submodule K F).map e.toLinearMap = ⊥ := Submodule.map_bot _
  have ht : (⊤ : Submodule K F).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  constructor
  · rw [disjoint_iff]
    change (T.A 0).map e.toLinearMap ⊓ (T.A 1).map e.toLinearMap = ⊥
    rw [←Submodule.map_inf e.toLinearMap e.injective,h.disjoint₀₁.eq_bot,hb]
  · rw [disjoint_iff]
    change (T.A 0).map e.toLinearMap ⊓ (T.A 2).map e.toLinearMap = ⊥
    rw [←Submodule.map_inf e.toLinearMap e.injective,h.disjoint₀₂.eq_bot,hb]
  · rw [disjoint_iff]
    change (T.A 1).map e.toLinearMap ⊓ (T.A 2).map e.toLinearMap = ⊥
    rw [←Submodule.map_inf e.toLinearMap e.injective,h.disjoint₁₂.eq_bot,hb]
  · change (T.A 0).map _ ⊔ (T.A 1).map _ ⊔ (T.A 2).map _ = ⊤
    rw [←Submodule.map_sup,←Submodule.map_sup,h.spanning,ht]
  · intro i j hij
    change (T.U i).map _ ⊔ (T.U j).map _ = ⊤
    rw [←Submodule.map_sup,h.private_active i j hij,ht]
  · change (T.A 0).map _ ⊓ ((T.A 1).map _ ⊔ (T.A 2).map _) ≤
      (T.U 2).map _ ⊔ ((T.U 0).map _ ⊓ (T.U 1).map _)
    rw [←Submodule.map_sup,←Submodule.map_inf e.toLinearMap e.injective,
      ←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_sup]
    exact Submodule.map_mono h.tripod_active
  · rw [commonSeed_map,h.common_zero,hb]

section Products
variable {G : I → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
open FiniteRelayAssembly FiniteComponentCoordinates

/-- The common seed splits on the actual product coefficient space. -/
theorem commonSeed_product (T : ∀ i, Task K (G i)) :
    commonSeed (task T) = space (fun i => commonSeed (T i)) := by
  simp only [commonSeed,task,←space_inf,←space_sup]

/-- Product geometry restricts to each actual coordinate factor. -/
theorem ActiveResidual.component (T : ∀ i, Task K (G i))
    (h : ActiveResidual (task T)) (a : I) : ActiveResidual (T a) := by
  classical
  have hbot (A : ∀ i, Submodule K (G i)) (hh : space A = ⊥) : A a = ⊥ := by
    have he := congrArg (Submodule.map (LinearMap.proj a)) hh
    simpa only [pi_map_proj,Submodule.map_bot] using he
  have htop (A : ∀ i, Submodule K (G i)) (hh : space A = ⊤) : A a = ⊤ := by
    have he := congrArg (Submodule.map (LinearMap.proj a)) hh
    rw [pi_map_proj,Submodule.map_top,
      LinearMap.range_eq_top.mpr (LinearMap.proj_surjective a)] at he
    exact he
  have hle (A B : ∀ i, Submodule K (G i)) (hh : space A ≤ space B) : A a ≤ B a := by
    have he := Submodule.map_mono (f := LinearMap.proj a) hh
    simpa only [pi_map_proj] using he
  constructor
  · rw [disjoint_iff]
    apply hbot
    simpa only [task,←space_inf] using h.disjoint₀₁.eq_bot
  · rw [disjoint_iff]
    apply hbot
    simpa only [task,←space_inf] using h.disjoint₀₂.eq_bot
  · rw [disjoint_iff]
    apply hbot
    simpa only [task,←space_inf] using h.disjoint₁₂.eq_bot
  · apply htop
    simpa only [task,←space_sup] using h.spanning
  · intro i j hij
    apply htop
    simpa only [task,←space_sup] using h.private_active i j hij
  · apply hle
    simpa only [task,←space_inf,←space_sup] using h.tripod_active
  · apply hbot
    simpa only [commonSeed_product] using h.common_zero

/-- Activity of factors is a consequence of exact reconstruction, rather
than an additional hypothesis of the decomposition theorem. -/
theorem component_active (T : Task K F) (S : ∀ i, Task K (G i))
    (e : (∀ i, G i) ≃ₗ[K] F) (he : Profile.mapTask e (task S) = T)
    (h : ActiveResidual T) (i : I) : ActiveResidual (S i) := by
  have hh := h.map e.symm
  have ht : Profile.mapTask e.symm T = task S := by
    rw [←he]
    exact ResidualRelayAssembly.mapTask_inverse (task S) e.symm
  rw [ht] at hh
  exact hh.component S i
end Products

/-- The paper's intrinsic residual dimension expression, over the reals so
that no truncated subtraction can hide dimension inequalities. -/
noncomputable def uploadValue [FiniteDimensional K F] (T : Task K F) : ℝ :=
  2 * (finrank K F : ℝ) -
    (finrank K (T.A 0) + finrank K (T.A 1) + finrank K (T.A 2))

theorem uploadValue_map [FiniteDimensional K F] [FiniteDimensional K V]
    (T : Task K F) (e : F ≃ₗ[K] V) :
    uploadValue (Profile.mapTask e T) = uploadValue T := by
  unfold uploadValue
  simp only [Profile.mapTask,e.finrank_map_eq,e.finrank_eq]

section Canonical
open ResidualUpload ResidualTaskAssembly ResidualPrivateSplit
variable {P₁ P₂ P₃ D : Type*}
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

/-- The canonical v-line lies in the intrinsic side-space tripod core. -/
theorem canonical_tripod_le (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D) :
    LinearMap.range (tripod₁ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) ≤
      T.A 0 ⊓ (T.A 1 ⊔ T.A 2) := by
  rintro _ ⟨d,rfl⟩
  rw [h₀,h₁,h₂]
  refine ⟨⟨(0,d),rfl⟩,?_⟩
  have hr : tripod₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ A₂ K P₁ P₂ P₃ D := ⟨(0,d),rfl⟩
  have ht : tripod₃ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ A₃ K P₁ P₂ P₃ D := ⟨(0,d),rfl⟩
  have hh := (A₂ K P₁ P₂ P₃ D ⊔ A₃ K P₁ P₂ P₃ D).sub_mem
    (Submodule.mem_sup_left hr) (Submodule.mem_sup_right ht)
  convert hh using 1
  ext <;> simp [tripod₁,tripod₂,tripod₃,side₁,side₂,side₃]

/-- Vanishing intrinsic common tripod excludes every common pure-demand row. -/
theorem canonical_zero_common (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D)
    (hz : commonSeed T = ⊥) :
    pureRows₁ T ⊓ pureRows₂ T ⊓ pureRows₃ T = ⊥ := by
  apply eq_bot_iff.mpr
  intro d hd
  let g := selectedDemandData T h₀ h₁ h₂
  have hv₀ : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ T.A 0 := by
    rw [h₀]; exact ⟨(0,d),rfl⟩
  have hr₁ : embedR (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ T.A 1 := by
    rw [h₁]; exact ⟨(0,d),rfl⟩
  let t := embedR (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d - embedV (K := K) d
  have ht₂ : t ∈ T.A 2 := by
    rw [h₂]
    refine ⟨(0,d),?_⟩
    ext <;> simp [t,embedR,embedV,side₁,side₂,side₃]
  have hv : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ T.U 0 ⊓ T.U 1 ⊓ T.U 2 :=
    ⟨⟨T.side_le_signal 0 hv₀,(g.pureRows_iff.2.1 d).mp hd.1.2⟩,
      (g.pureRows_iff.2.2 d).mp hd.2⟩
  have hr : embedR (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ T.U 0 ⊓ T.U 1 ⊓ T.U 2 := by
    refine ⟨⟨(g.pureRows_iff.1 d).mp hd.1.1,T.side_le_signal 1 hr₁⟩,?_⟩
    have hh := (T.U 2).add_mem (T.side_le_signal 2 ht₂) hv.2
    simpa only [t,sub_add_cancel] using hh
  have ht : t ∈ T.U 0 ⊓ T.U 1 ⊓ T.U 2 :=
    (T.U 0 ⊓ T.U 1 ⊓ T.U 2).sub_mem hr hv
  have hh : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ commonSeed T := by
    refine ⟨⟨hv₀,hv⟩,?_⟩
    have hm := ((T.A 1 ⊓ (T.U 0 ⊓ T.U 1 ⊓ T.U 2)) ⊔
      (T.A 2 ⊓ (T.U 0 ⊓ T.U 1 ⊓ T.U 2))).sub_mem
      (Submodule.mem_sup_left ⟨hr₁,hr⟩) (Submodule.mem_sup_right ⟨ht₂,ht⟩)
    simpa only [t,sub_sub_cancel] using hm
  rw [hz] at hh
  have he : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d = 0 := hh
  exact congrArg (fun x : Ambient P₁ P₂ P₃ D => x.2.1) he

/-- The intrinsic signal bridge forces every row to have an actual signed
zero-private witness. Thus it means full retained row activity, not merely a
numerical lower-bound condition. -/
theorem canonical_rows_fully_active (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D)
    (h : ActiveResidual T) (g : DemandData T) : g.activeRows = ⊤ := by
  apply top_unique
  intro d _
  apply (CommonTripodRanks.activeRows_mem_iff g d).mpr
  have hd : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈
      T.U 2 ⊔ (T.U 0 ⊓ T.U 1) :=
    h.tripod_active (canonical_tripod_le T h₀ h₁ h₂ ⟨d,rfl⟩)
  obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp hd
  have hp₁ := congrArg (fun x : Ambient P₁ P₂ P₃ D => x.1.1.1) he
  have hp₂ := congrArg (fun x : Ambient P₁ P₂ P₃ D => x.1.1.2) he
  have hp₃ := congrArg (fun x : Ambient P₁ P₂ P₃ D => x.1.2) he
  have hv := congrArg (fun x : Ambient P₁ P₂ P₃ D => x.2.1) he
  have hr := congrArg (fun x : Ambient P₁ P₂ P₃ D => x.2.2) he
  change u.1.1.1+w.1.1.1=0 at hp₁
  change u.1.1.2+w.1.1.2=0 at hp₂
  change u.1.2+w.1.2=0 at hp₃
  change u.2.1+w.2.1=d at hv
  change u.2.2+w.2.2=0 at hr
  have hl := demandLift_remainder (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)
  refine ⟨(w.1.1.2,w.1.2),(w.1.1.1,w.1.2),(u.1.1.1,u.1.1.2),
    w.2.2,w.2.1,u.2.1+u.2.2,?_,?_,?_,?_,?_,by simp,?_⟩
  · exact quotientLift_mem _ _ (T.side_le_signal 0) demandQuotient₁ demandLift₁
      (by simpa only [h₀] using hl.1) w hw.1
  · exact quotientLift_mem _ _ (T.side_le_signal 1) demandQuotient₂ demandLift₂
      (by simpa only [h₁] using hl.2.1) w hw.2
  · exact quotientLift_mem _ _ (T.side_le_signal 2) demandQuotient₃ demandLift₃
      (by simpa only [h₂] using hl.2.2) u hu
  · simpa only [add_comm] using hp₁
  · simpa only [add_comm] using hp₂
  · calc
      d = (u.2.1+w.2.1)+(u.2.2+w.2.2) := by rw [hv,hr,add_zero]
      _ = w.2.2+w.2.1+(u.2.1+u.2.2) := by abel

variable [Finite K] [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]

/-- Nonlinear code converse using only the intrinsic tripod bridge, without
requiring the stronger and generally false full signal join identity. -/
theorem canonical_code_lower {n : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D)
    (h : ActiveResidual T)
    (c : T.Code n (fun i => Fin (m i)) (Fin s)) (hn : 0 < n) :
    uploadValue T ≤ c.uploadCost := by
  classical
  letI (i : Three) : MeasurableSpace (Fin (m i)) := ⊤
  letI (i : Three) : DiscreteMeasurableSpace (Fin (m i)) := ⟨fun _ => trivial⟩
  obtain ⟨hu₀,hu₁,hu₂⟩ := GeometricUploadConverse.fully_used_of_pair_spans T h.private_active
  let v : D →ₗ[K] Ambient P₁ P₂ P₃ D := tripod₁
  let r : D →ₗ[K] Ambient P₁ P₂ P₃ D := tripod₂
  let R : Three → Submodule K (Ambient P₁ P₂ P₃ D) :=
    ![LinearMap.range v,LinearMap.range r,LinearMap.range (r-v)]
  apply ResidualConverse.code_rank_lower_bound T c R
    (fully_used_splits T h₀ h₁ h₂ hu₀ hu₁ hu₂)
    h.disjoint₀₁ h.disjoint₀₂ h.disjoint₁₂
  · rintro _ ⟨d,rfl⟩
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨d,rfl⟩)
      (Submodule.mem_sup_left ⟨d,rfl⟩)
  · rintro _ ⟨d,rfl⟩
    have hh := Submodule.add_mem_sup
      (show v d ∈ LinearMap.range v from ⟨d,rfl⟩)
      (show (r-v) d ∈ LinearMap.range (r-v) from ⟨d,rfl⟩)
    have he : v d + (r d-v d) = r d := by abel
    simpa only [LinearMap.sub_apply,he] using hh
  · exact (canonical_tripod_le T h₀ h₁ h₂).trans h.tripod_active
  · exact h.spanning
  · exact hn
end Canonical

section Finite
variable [Finite K] [FiniteDimensional K F]

/-- The upload converse for every active residual and every nonlinear block
code, stated entirely on the original coefficient spaces. -/
theorem code_lower {n : ℕ} {m : Three → ℕ} {s : ℕ}
    (T : Task K F) (h : ActiveResidual T)
    (c : T.Code n (fun i => Fin (m i)) (Fin s)) (hn : 0 < n) :
    uploadValue T ≤ c.uploadCost := by
  obtain ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩ := ResidualTaskAssembly.exists_canonical_chart
    (T.A 0) (T.A 1) (T.A 2) h.disjoint₀₁ h.disjoint₀₂ h.disjoint₁₂ h.spanning
  let C : T.PrivateTripodChart := ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩
  have hmem := c.mem_achievableAt hn
  rw [(T.coordinateRetraction e.symm).achievableAt_eq n] at hmem
  obtain ⟨_,_,_,m',s',c',hu,_⟩ := hmem
  have hh := canonical_code_lower C.toTask C.sides.1 C.sides.2.1 C.sides.2.2
    (h.map e.symm) c' hn
  have hv : uploadValue C.toTask = uploadValue T := uploadValue_map T e.symm
  rw [hv] at hh
  exact hh.trans hu

omit [Finite K] in
/-- An actual scalar locally generated relay attains the residual dimension
expression. All graphs, row coordinates and local generators are constructed. -/
theorem exists_optimal_relay (T : Task K F) (h : ActiveResidual T) :
    ∃ Q : Submodule K F, T.LocallyGenerated Q ∧ T.RelayFeasible Q ∧
      (finrank K Q : ℝ) = uploadValue T := by
  obtain ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩ := ResidualTaskAssembly.exists_canonical_chart
    (T.A 0) (T.A 1) (T.A 2) h.disjoint₀₁ h.disjoint₀₂ h.disjoint₁₂ h.spanning
  let C : T.PrivateTripodChart := ⟨P₁,P₂,P₃,e,he₀,he₁,he₂⟩
  have hc : ActiveResidual C.toTask := h.map e.symm
  have hz := canonical_zero_common C.toTask C.sides.1 C.sides.2.1 C.sides.2.2 hc.common_zero
  obtain ⟨Q,hl,hf,hr⟩ := ResidualRelayAssembly.exists_relay_of_zero_common C.toTask
    C.sides.1 C.sides.2.1 C.sides.2.2 hz
  have hback : Profile.mapTask e C.toTask = T := ResidualRelayAssembly.mapTask_inverse T e
  obtain ⟨hl',hf'⟩ := ResidualRelayAssembly.map_relay C.toTask e Q hl hf
  rw [hback] at hl' hf'
  refine ⟨Q.map e.toLinearMap,hl',hf',?_⟩
  rw [e.finrank_map_eq,hr]
  have hg : uploadValue C.toTask =
      (finrank K P₁ : ℝ)+finrank K P₂+finrank K P₃+
        finrank K ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1)) := by
    unfold uploadValue
    rw [C.sides.1,C.sides.2.1,C.sides.2.2]
    exact_mod_cast (ResidualUpload.gamma_rank (K := K) (P₁ := P₁) (P₂ := P₂)
      (P₃ := P₃) (T := ↥(T.A 2 ⊓ (T.A 0 ⊔ T.A 1))))
  have hv : uploadValue C.toTask = uploadValue T := uploadValue_map T e.symm
  rw [hv] at hg
  simpa only [Nat.cast_add] using hg.symm

/-- Exact minimum over arbitrary nonlinear codes and the closed regularized
region. This does not assume separate component encoding. -/
theorem minimum_upload (T : Task K F) (h : ActiveResidual T) :
    T.uploadOptimum = uploadValue T := by
  obtain ⟨Q,hl,hf,hr⟩ := exists_optimal_relay T h
  obtain ⟨owner,c,hc⟩ := ResidualOperational.finiteCode_of_local_relay T Q hl hf
  letI : Finite (Q →ₗ[K] K) := c.finite_broadcast
  apply Task.uploadOptimum_eq_of_code c.toCode (by decide) (uploadValue T)
  · exact hc.trans_eq hr
  · intro L m s code hL
    exact code_lower T h code hL

/-- The exact optimum is attained by a scalar linear upload over the original
field, including characteristic two. -/
theorem scalar_upload_exact (T : Task K F) (h : ActiveResidual T) :
    ∃ (d : ℕ) (r : Three → ℕ) (c : T.LinearCode 1 r d),
      (∑ i,r i) = d ∧ (d : ℝ) = uploadValue T ∧
      c.toCode.uploadCost = uploadValue T ∧ c.toCode.broadcastCost ≤ uploadValue T := by
  obtain ⟨Q,hl,hf,hr⟩ := exists_optimal_relay T h
  obtain ⟨r,c,hs,hu,hd⟩ := RelayLinearComposition.full_relay_linear_code T Q hl hf
  refine ⟨finrank K Q,r,c,hs,hr,?_,hd.trans_eq hr⟩
  apply le_antisymm (hu.trans_eq hr)
  rw [←minimum_upload T h]
  exact c.uploadOptimum_le (by decide)
end Finite

section ProductRanks
variable {G : I → Type*} [Fintype I]
  [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
  [∀ i, FiniteDimensional K (G i)]

/-- The residual dimension expression is additive on actual coefficient
products, by ambient and all three side-space dimension equalities. -/
theorem uploadValue_product (T : ∀ i, Task K (G i)) :
    uploadValue (FiniteRelayAssembly.task T) = ∑ i, uploadValue (T i) := by
  unfold uploadValue
  simp only [Module.finrank_pi_fintype,FiniteRelayAssembly.task,
    FiniteRelayAssembly.finrank_space,Nat.cast_sum,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,Finset.mul_sum]

/-- Exact original-task decomposition implies additivity of the operational
minimum, even when competitors jointly encode all components nonlinearly. -/
theorem minimum_upload_additive [Finite K] [FiniteDimensional K F]
    (T : Task K F) (S : ∀ i, Task K (G i)) (e : (∀ i, G i) ≃ₗ[K] F)
    (he : Profile.mapTask e (FiniteRelayAssembly.task S) = T)
    (h : ActiveResidual T) :
    T.uploadOptimum = ∑ i, (S i).uploadOptimum := by
  rw [minimum_upload T h]
  have hc (i : I) : ActiveResidual (S i) := component_active T S e he h i
  simp_rw [minimum_upload _ (hc _)]
  rw [←uploadValue_product S,←uploadValue_map (FiniteRelayAssembly.task S) e,he]
end ProductRanks

section SourceResidual
open ResidualUpload ResidualTaskAssembly
variable {P₁ P₂ P₃ D : Type*}
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

/-- All intrinsic residual conditions hold on the actual post-common,
post-passive task constructed from the source demand spaces. -/
theorem finalResidual_active (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D) :
    ActiveResidual (finalResidual T h₀ h₁ h₂) := by
  let R := finalResidual T h₀ h₁ h₂
  let g := finalDemandData T h₀ h₁ h₂
  obtain ⟨ha,hb,hc⟩ := g.activeRowReduction_sides rfl rfl rfl
  obtain ⟨hu₀,hu₁,hu₂⟩ := finalResidual_fully_used T h₀ h₁ h₂
  change ActiveResidual g.activeRowReduction
  constructor
  · rw [ha,hb]; exact sides_disjoint₁₂
  · rw [ha,hc]; exact sides_disjoint₁₃
  · rw [hb,hc]; exact sides_disjoint₂₃
  · rw [ha,hb,hc]; exact sides_span
  · exact ResidualIntrinsicGeometry.all_signal_pairs_spanning R ha hb hc hu₀ hu₁ hu₂
  · rw [ResidualIntrinsicGeometry.tripod_side_core g.activeRowReduction ha hb hc]
    exact le_sup_left.trans (g.activeRowReduction_tripod_bridge rfl rfl rfl)
  · exact ResidualIntrinsicGeometry.commonSeed_eq_bot R ha hb hc
      (finalResidual_zero_common T h₀ h₁ h₂)

variable [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K D]

/-- The residual dimension expression equals the manuscript's actual retained
private rank plus noncommon pure-and-mixed tripod rank. -/
theorem finalResidual_uploadValue (T : Task K (Ambient P₁ P₂ P₃ D))
    (h₀ : T.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₁ : T.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₂ : T.A 2 = A₃ K P₁ P₂ P₃ D) :
    uploadValue (finalResidual T h₀ h₁ h₂) =
      (privateDimension T : ℝ) + tripodDimension T h₀ h₁ h₂ := by
  let g := finalDemandData T h₀ h₁ h₂
  obtain ⟨ha,hb,hc⟩ := g.activeRowReduction_sides rfl rfl rfl
  change uploadValue g.activeRowReduction = _
  unfold uploadValue
  rw [ha,hb,hc]
  have hg : 2 * (finrank K (Ambient (used₁ T) (used₂ T) (used₃ T) g.activeRows) : ℝ) -
      (finrank K (A₁ K (used₁ T) (used₂ T) (used₃ T) g.activeRows) +
       finrank K (A₂ K (used₁ T) (used₂ T) (used₃ T) g.activeRows) +
       finrank K (A₃ K (used₁ T) (used₂ T) (used₃ T) g.activeRows)) =
      (finrank K (used₁ T) : ℝ)+finrank K (used₂ T)+finrank K (used₃ T)+finrank K g.activeRows := by
    exact_mod_cast (gamma_rank (K := K) (P₁ := used₁ T) (P₂ := used₂ T)
      (P₃ := used₃ T) (T := g.activeRows))
  rw [hg]
  have hr : finrank K g.activeRows = tripodDimension T h₀ h₁ h₂ :=
    finalRows_finrank T h₀ h₁ h₂
  rw [hr]
  simp only [privateDimension,Nat.cast_add]
end SourceResidual

section Decomposition
variable [Finite K] [FiniteDimensional K F]
open FiniteComponentCoordinates

/-- Source `prop:exhaustion` for any exact finite decomposition. Component
activity and component formulas are conclusions. Indecomposability is not
needed for additivity, so this also covers every refinement. -/
theorem residual_decomposition {G : I → Type*} [Fintype I]
    [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
    [∀ i, FiniteDimensional K (G i)]
    (T : Task K F) (S : ∀ i, Task K (G i)) (e : (∀ i, G i) ≃ₗ[K] F)
    (he : Profile.mapTask e (FiniteRelayAssembly.task S) = T)
    (h : ActiveResidual T) :
    (∀ i, ActiveResidual (S i)) ∧
    T.uploadOptimum = uploadValue T ∧
    (∀ i, (S i).uploadOptimum = uploadValue (S i)) ∧
    T.uploadOptimum = ∑ i, (S i).uploadOptimum := by
  have hc : ∀ i, ActiveResidual (S i) := component_active T S e he h
  exact ⟨hc,minimum_upload T h,fun i => minimum_upload (S i) (hc i),
    minimum_upload_additive T S e he h⟩

/-- There is an actual indecomposable coefficient decomposition with every
labeled component space equal to its intersection with the original space,
and all the operational upload equalities of `prop:exhaustion`. -/
theorem exists_indecomposable_residual_decomposition (T : Task K F) (h : ActiveResidual T) :
    ∃ n : ℕ, ∃ P : Fin n → Submodule K F, ∃ e : (∀ i, P i) ≃ₗ[K] F,
      Profile.mapTask e (FiniteRelayAssembly.task (componentTask T P e)) = T ∧
      (∀ i, TaskDecomposition.Indecomposable
        (EdgeExtraction.configuration (componentTask T P e i)).spaces ⊤) ∧
      (∀ i j, (componentTask T P e i).A j = (T.A j).comap (P i).subtype) ∧
      (∀ i j, (componentTask T P e i).U j = (T.U j).comap (P i).subtype) ∧
      (∀ i, ActiveResidual (componentTask T P e i)) ∧
      T.uploadOptimum = uploadValue T ∧
      (∀ i, (componentTask T P e i).uploadOptimum = uploadValue (componentTask T P e i)) ∧
      T.uploadOptimum = ∑ i, (componentTask T P e i).uploadOptimum ∧
      (∑ i, finrank K (P i)) = finrank K F := by
  obtain ⟨n,P,e,he,hi,hA,hU,hd⟩ := exists_operational_component_coordinates T
  obtain ⟨hc,ht,hm,hs⟩ := residual_decomposition T (componentTask T P e) e he h
  exact ⟨n,P,e,he,hi,hA,hU,hc,ht,hm,hs,hd⟩
end Decomposition

section Boundary
/-- A nonzero active residual cannot have side-only signals. -/
theorem exists_nontrivial_demand (T : Task K F) (h : ActiveResidual T)
    (hn : (⊤ : Submodule K F) ≠ ⊥) : ∃ i, T.A i ≠ T.U i := by
  by_contra hh
  push_neg at hh
  have hp₀₁ : T.A 0 ⊔ T.A 1 = ⊤ := by simpa only [←hh 0,←hh 1] using h.private_active 0 1 (by decide)
  have hp₀₂ : T.A 0 ⊔ T.A 2 = ⊤ := by simpa only [←hh 0,←hh 2] using h.private_active 0 2 (by decide)
  have hp₁₂ : T.A 1 ⊔ T.A 2 = ⊤ := by simpa only [←hh 1,←hh 2] using h.private_active 1 2 (by decide)
  have hb := h.tripod_active
  rw [←hh 0,←hh 1,←hh 2,hp₁₂,inf_top_eq,h.disjoint₀₁.eq_bot,sup_bot_eq] at hb
  have ha₀ : T.A 0 = ⊥ := eq_bot_iff.mpr (fun x hx => h.disjoint₀₂.le_bot ⟨hx,hb hx⟩)
  rw [ha₀,bot_sup_eq] at hp₀₁ hp₀₂
  exact hn (by simpa only [hp₀₁,hp₀₂,inf_top_eq] using h.disjoint₁₂.eq_bot)

variable [FiniteDimensional K F]

/-- Absence of a side-space tripod gives an actual independent three-way sum. -/
theorem side_sum_dimension (T : Task K F) (h : ActiveResidual T)
    (hz : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) = ⊥) :
    finrank K F = finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) := by
  have h₁₂ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 1) (T.A 2)
  rw [h.disjoint₁₂.eq_bot,finrank_bot,add_zero] at h₁₂
  have h₀ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1 ⊔ T.A 2)
  rw [←sup_assoc,h.spanning,finrank_top,hz,finrank_bot,add_zero,h₁₂] at h₀
  omega

/-- Positive side-information excess excludes the all-omniscience endpoint
using the actual common-row geometry. -/
theorem exists_nonfull_signal (T : Task K F) (h : ActiveResidual T)
    (hpos : finrank K F < finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2)) :
    ∃ i, T.U i ≠ ⊤ := by
  by_contra hh
  push_neg at hh
  have hz : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) = ⊥ := by
    simpa only [commonSeed,hh,inf_top_eq] using h.common_zero
  have hd := side_sum_dimension T h hz
  omega

omit [FiniteDimensional K F] in
/-- Full relay is locally generated on every active residual. -/
theorem full_relay_local (T : Task K F) (h : ActiveResidual T) :
    T.LocallyGenerated ⊤ := by
  unfold Task.LocallyGenerated
  simp only [top_inf_eq,Profile.three_iSup]
  exact h.spanning.symm

/-- The full relay preserves every one of the fifteen fully informed entries. -/
theorem full_relay_profile (T : Task K F) (h : ActiveResidual T) (r : Profile.Index) :
    Profile.entry (T.inducedRelay ⊤ (full_relay_local T h)) r = Profile.entry T r := by
  rw [T.inducedRelay_entry]
  have he : NonzeroDefectRelays.inducedTask T ⊤ (full_relay_local T h) = T := by
    have ha : (NonzeroDefectRelays.inducedTask T ⊤ (full_relay_local T h)).A = T.A := by
      funext i; exact inf_top_eq _
    have hu : (NonzeroDefectRelays.inducedTask T ⊤ (full_relay_local T h)).U = T.U := by
      funext i; exact inf_top_eq _
    cases T
    cases hh : NonzeroDefectRelays.inducedTask _ ⊤ (full_relay_local _ h)
    simp_all only [Task.mk.injEq]
  rw [he]

/-- The zero-excess component requires exactly its full ambient dimension in
upload; the full relay is optimal and preserves the fully informed profile. -/
theorem zero_excess_full_relay [Finite K] (T : Task K F) (h : ActiveResidual T)
    (hz : finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F) :
    T.uploadOptimum = finrank K F ∧
    T.LocallyGenerated ⊤ ∧ T.RelayFeasible ⊤ ∧
    (∀ r : Profile.Index, Profile.entry (T.inducedRelay ⊤ (full_relay_local T h)) r = Profile.entry T r) := by
  refine ⟨?_,full_relay_local T h,fun _ => by simp [Task.RelayFeasible],full_relay_profile T h⟩
  rw [minimum_upload T h]
  unfold uploadValue
  have hz' : (finrank K (T.A 0) : ℝ)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F := by exact_mod_cast hz
  rw [hz']
  ring
end Boundary

/-- The source feasibility normalization makes side-information excess
nonnegative on every component. -/
theorem side_dimension_le [FiniteDimensional K F] (T : Task K F) (h : ActiveResidual T) :
    finrank K F ≤ finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) := by
  have h₀ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1)
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0 ⊔ T.A 1) (T.A 2)
  rw [h.spanning,finrank_top] at h₁
  omega

/-- Zero excess is the actual direct-sum side geometry, not merely an
arithmetic case distinction. -/
theorem zero_excess_side_complement [FiniteDimensional K F] (T : Task K F) (h : ActiveResidual T)
    (hz : finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F) :
    IsCompl (T.A 0) (T.A 1 ⊔ T.A 2) ∧ Disjoint (T.A 1) (T.A 2) := by
  have h₁₂ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 1) (T.A 2)
  rw [h.disjoint₁₂.eq_bot,finrank_bot,add_zero] at h₁₂
  have h₀ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1 ⊔ T.A 2)
  rw [←sup_assoc,h.spanning,finrank_top,h₁₂] at h₀
  have hi : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact ⟨⟨disjoint_iff.mpr hi,codisjoint_iff.mpr (by rw [←sup_assoc,h.spanning])⟩,h.disjoint₁₂⟩

/-- No pair-known coefficients, hence no active pair rank, survive in any
intrinsically active residual component. -/
theorem pair_ranks_zero [FiniteDimensional K F] (T : Task K F) (h : ActiveResidual T) :
    (∀ i, T.pairKnown i = ⊥) ∧ (∀ i, T.intrinsicActivePairRank i = 0) := by
  have hp : ∀ i, T.pairKnown i = ⊥ := by
    intro i
    fin_cases i
    · change T.pairKnown (0 : Three) = ⊥
      rw [T.pairKnown_eq_pair 0 1 2 (by decide) (by decide) (by decide)]
      exact h.disjoint₁₂.eq_bot
    · change T.pairKnown (1 : Three) = ⊥
      rw [T.pairKnown_eq_pair 1 0 2 (by decide) (by decide) (by decide)]
      exact h.disjoint₀₂.eq_bot
    · change T.pairKnown (2 : Three) = ⊥
      rw [T.pairKnown_eq_pair 2 0 1 (by decide) (by decide) (by decide)]
      exact h.disjoint₀₁.eq_bot
  refine ⟨hp,?_⟩
  intro i
  change finrank K ↥(T.U i ⊓ T.pairKnown i) - finrank K T.commonKnown = 0
  rw [hp i,inf_bot_eq,finrank_bot,Nat.zero_sub]

end UploadBroadcast.ResidualComponentAdditivity


namespace UploadBroadcast.Task.PrivateTripodChart
open ResidualComponentAdditivity
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]
  {T : Task K F} (c : T.PrivateTripodChart)

/-- The source post-common, post-passive residual in this constructed chart. -/
noncomputable def componentResidual :=
  ResidualTaskAssembly.finalResidual c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

theorem componentResidual_active : ActiveResidual c.componentResidual :=
  finalResidual_active c.toTask c.sides.1 c.sides.2.1 c.sides.2.2

/-- Chart-generic form keeps coefficient instances available when applied to
an arbitrary original task's deeply nested quotient chart. -/
theorem componentResidual_decomposition [Finite K] [FiniteDimensional K F] : type_of%
    (exists_indecomposable_residual_decomposition c.componentResidual c.componentResidual_active) :=
  exists_indecomposable_residual_decomposition c.componentResidual c.componentResidual_active

/-- The same source rank identity before specializing the original-task chart. -/
theorem componentResidual_upload_formula [Finite K] [FiniteDimensional K F] :
    c.componentResidual.uploadOptimum =
      (ResidualTaskAssembly.privateDimension c.toTask : ℝ) +
        ResidualTaskAssembly.tripodDimension c.toTask c.sides.1 c.sides.2.1 c.sides.2.2 :=
  (minimum_upload _ c.componentResidual_active).trans
    (finalResidual_uploadValue c.toTask c.sides.1 c.sides.2.1 c.sides.2.2)
end UploadBroadcast.Task.PrivateTripodChart

namespace UploadBroadcast.ResidualComponentAdditivity
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The actual source residual, selected from an arbitrary original task,
satisfies all intrinsic activity conditions. -/
theorem source_residual_active (T : Task K F) : type_of%
    T.pairFreeChart.componentResidual_active :=
  T.pairFreeChart.componentResidual_active

/-- Unconditional original-task endpoint for `prop:exhaustion`: actual
indecomposable coefficient subspaces, inherited activity, component upload
formulas and operational additivity. -/
theorem source_residual_decomposition [Finite K] [FiniteDimensional K F]
    (T : Task K F) : type_of% T.pairFreeChart.componentResidual_decomposition :=
  T.pairFreeChart.componentResidual_decomposition

/-- The common value is the source's pre-common private-plus-retained-tripod
rank, using the chart constructed from the original task. -/
theorem source_residual_upload_formula [Finite K] [FiniteDimensional K F]
    (T : Task K F) : type_of% T.pairFreeChart.componentResidual_upload_formula :=
  T.pairFreeChart.componentResidual_upload_formula
end UploadBroadcast.ResidualComponentAdditivity
