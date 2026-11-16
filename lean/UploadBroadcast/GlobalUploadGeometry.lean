import UploadBroadcast.GlobalUploadConverse
import UploadBroadcast.Profile

/-! Construct the global entropy geometry from actual residual signal data
and an omniscience direct summand. No entropy inequality is assumed. -/
namespace UploadBroadcast.GlobalUploadGeometry
open GlobalUploadConverse ResidualConverse
variable {K F E T P₁ P₂ P₃ L : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup E] [Module K E]
  [AddCommGroup T] [Module K T] [AddCommGroup P₁] [Module K P₁]
  [AddCommGroup P₂] [Module K P₂] [AddCommGroup P₃] [Module K P₃]
  [AddCommGroup L] [Module K L]

structure ResidualGeometry (task : Task K F) where
  tripod : Three → Submodule K F
  common : Three → Submodule K F
  pair : ∀ i j, i ≠ j → Disjoint (task.A i) (task.A j)
  private_split : ∀ i, PrivateSplit task i (tripod i)
  tri : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → tripod k ≤ tripod i ⊔ tripod j
  common_le : ∀ i k, i ≠ k → common k ≤ task.U i
  bridge : ∀ i k, i ≠ k → tripod i ≤ task.U k ⊔ common k

def tripodSpaces (v r : T →ₗ[K] F) : Three → Submodule K F :=
  ![LinearMap.range v,LinearMap.range r,LinearMap.range (r-v)]

theorem tripod_recovery (v r : T →ₗ[K] F) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripodSpaces v r k ≤ tripodSpaces v r i ⊔ tripodSpaces v r j := by
  have h₂ : LinearMap.range (r-v) ≤ LinearMap.range v ⊔ LinearMap.range r := by
    rintro _ ⟨t,rfl⟩
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨t,rfl⟩) (Submodule.mem_sup_left ⟨t,rfl⟩)
  have h₁ : LinearMap.range r ≤ LinearMap.range v ⊔ LinearMap.range (r-v) := by
    rintro _ ⟨t,rfl⟩
    have hh := Submodule.add_mem_sup (show v t ∈ LinearMap.range v from ⟨t,rfl⟩)
      (show (r-v) t ∈ LinearMap.range (r-v) from ⟨t,rfl⟩)
    have he : v t+(r t-v t)=r t := by abel
    simpa only [LinearMap.sub_apply,he] using hh
  have h₀ : LinearMap.range v ≤ LinearMap.range r ⊔ LinearMap.range (r-v) := by
    rintro _ ⟨t,rfl⟩
    have hh := Submodule.sub_mem (LinearMap.range r ⊔ LinearMap.range (r-v))
      (Submodule.mem_sup_left (show r t ∈ LinearMap.range r from ⟨t,rfl⟩))
      (Submodule.mem_sup_right (show (r-v) t ∈ LinearMap.range (r-v) from ⟨t,rfl⟩))
    simpa only [LinearMap.sub_apply,sub_sub_cancel] using hh
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [tripodSpaces,sup_comm]

/-- The common-function subspaces and all bridges are constructed from the
active signal data; callers do not supply intersection inclusions. -/
def of_active_data (task : Task K F)
    (a : SignalBridge.Data (K := K) (F := F) (T := T) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))
    (hU : ∀ i, task.U i = ![a.U₁,a.U₂,a.U₃] i)
    (pair : ∀ i j, i ≠ j → Disjoint (task.A i) (task.A j))
    (priv : ∀ i, PrivateSplit task i (tripodSpaces a.v a.r i)) : ResidualGeometry task where
  tripod := tripodSpaces a.v a.r
  common := ![a.U₂ ⊓ a.U₃,a.U₃ ⊓ a.U₁,a.U₁ ⊓ a.U₂]
  pair := pair
  private_split := priv
  tri := tripod_recovery a.v a.r
  common_le := by
    intro i k hik
    rw [hU]
    fin_cases i <;> fin_cases k <;> simp_all
  bridge := by
    intro i k _
    have ht : tripodSpaces a.v a.r i ≤ LinearMap.range a.v ⊔ LinearMap.range a.r := by
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
      · rintro _ ⟨t,rfl⟩
        exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨t,rfl⟩) (Submodule.mem_sup_left ⟨t,rfl⟩)
    apply ht.trans
    rw [hU]
    have hh := SignalBridge.all_tripod_bridges a
    fin_cases k
    · exact hh.2.2
    · exact hh.2.1
    · exact hh.1

/-- Extend an actual residual private projection through the independent
omniscience factor. Its extra local coordinates are exactly Si+Ti. -/
def private_directSum (om : Task K E) (res : Task K F) (t : Three → Submodule K F)
    (priv : ∀ i, PrivateSplit res i (t i)) (i : Three) :
    PrivateSplit (Profile.directSum om res) i
      ((om.A i).prod ⊥ ⊔ (⊥ : Submodule K E).prod (t i)) := by
  let p := priv i
  let embed : p.P →ₗ[K] (E × F) := (LinearMap.inr K E F).comp p.P.subtype
  let proj : (E × F) →ₗ[K] p.P := p.projection.comp (LinearMap.snd K E F)
  have hrange : LinearMap.range embed = (⊥ : Submodule K E).prod p.P := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨by simp [embed],u.property⟩
    · rintro ⟨hx,hy⟩
      have hx' : x.1 = 0 := hx
      exact ⟨⟨x.2,hy⟩,by ext <;> simp [embed,hx']⟩
  apply PrivateSplit.of_raw_projection (Profile.directSum om res) i _ embed proj
  · intro u
    exact p.on_private u
  · intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    change p.projection (a.2+b.2) = 0
    have ha' : a.2 = 0 := ha.2
    rw [ha',zero_add]
    exact p.on_tripod b.2 hb.2
  · change (om.A i).prod (res.A i) = _
    rw [hrange]
    simp only [Submodule.prod_sup_prod,bot_sup_eq,sup_bot_eq]
    rw [← p.side_eq]
  · intro j hj x hx
    exact p.on_others j hj x.2 hx.2
  · apply top_unique
    rw [← p.remote_span]
    apply iSup_le
    intro j x hx
    obtain ⟨u,hu,rfl⟩ := hx
    apply (le_iSup (fun j : {j : Three // j ≠ i} => ((Profile.directSum om res).U j.val).map proj) j)
    exact ⟨(0,u),⟨(om.U j.val).zero_mem,hu⟩,rfl⟩

/-- Actual direct-sum geometry for a fully demanded omniscience component
and an active residual component. -/
def directSumGeometry (om : Task K E) (res : Task K F)
    (hom : ∀ i, om.U i = ⊤) (r : ResidualGeometry res) :
    Geometry (Profile.directSum om res) where
  O := (⊤ : Submodule K E).prod (⊥ : Submodule K F)
  S i := (om.A i).prod ⊥
  R i := (⊥ : Submodule K E).prod (res.A i)
  T i := (⊥ : Submodule K E).prod (r.tripod i)
  Θ i := (⊥ : Submodule K E).prod (r.common i)
  side_eq i := by simp [Profile.directSum]
  side_om _ := Submodule.prod_mono le_top le_rfl
  demand_om i := by
    change (⊤ : Submodule K E).prod (⊥ : Submodule K F) ≤ (om.U i).prod (res.U i)
    rw [hom]
    exact Submodule.prod_mono le_rfl bot_le
  tripod_le i := Submodule.prod_mono le_rfl (by rw [(r.private_split i).side_eq]; exact le_sup_right)
  om_disjoint := by simp [disjoint_iff]
  residual_disjoint i j hij := by
    rw [disjoint_iff]
    simp only [Submodule.prod_inf_prod,inf_idem,disjoint_iff.mp (r.pair i j hij),Submodule.prod_bot]
  private_split := private_directSum om res r.tripod r.private_split
  tripod_recovery i j k hij hik hjk := by
    simpa only [Submodule.prod_sup_prod,bot_sup_eq] using
      (Submodule.prod_mono (le_rfl : (⊥ : Submodule K E) ≤ ⊥) (r.tri i j k hij hik hjk))
  common_le i k hik := Submodule.prod_mono bot_le (r.common_le i k hik)
  common_bridge i k hik := by
    simpa only [Profile.directSum,Submodule.prod_sup_prod,sup_bot_eq] using
      (Submodule.prod_mono (bot_le : (⊥ : Submodule K E) ≤ om.U k) (r.bridge i k hik))

section Ranks
variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- The actual direct-sum geometry has the manuscript's residual Γ and
omniscience deficits, by proved submodule-product dimension identities. -/
theorem directSum_rankBound (om : Task K E) (res : Task K F)
    (hom : ∀ i, om.U i = ⊤) (r : ResidualGeometry res) :
    (directSumGeometry om res hom r).rankBound =
      (2 * (Module.finrank K ↥(res.A 0 ⊔ res.A 1 ⊔ res.A 2) : ℝ) -
        (Module.finrank K (res.A 0)+Module.finrank K (res.A 1)+Module.finrank K (res.A 2))) +
      max (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))
        (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2))))
        ((((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))+
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))+
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2)))/2) := by
  simp [Geometry.rankBound,directSumGeometry,Submodule.prod_sup_prod,Profile.finrank_submodule_prod]
  rw [Submodule.prod_sup_prod,Submodule.prod_sup_prod]
  simp [Profile.finrank_submodule_prod]

/-- Operational global upload lower bound for an actual direct sum, for
arbitrary nonlinear finite codes at every positive blocklength. -/
theorem directSum_upload_lower_bound [Finite K] {n : ℕ} {M : Three → Type*} {B : Type*}
    (om : Task K E) (res : Task K F) (hom : ∀ i, om.U i = ⊤) (r : ResidualGeometry res)
    (code : (Profile.directSum om res).FiniteCode n M B) :
    (2 * (Module.finrank K ↥(res.A 0 ⊔ res.A 1 ⊔ res.A 2) : ℝ) -
      (Module.finrank K (res.A 0)+Module.finrank K (res.A 1)+Module.finrank K (res.A 2))) +
      max (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))
        (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2))))
        ((((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))+
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))+
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2)))/2) ≤ code.toCode.uploadCost := by
  rw [← directSum_rankBound om res hom r]
  exact GlobalUploadConverse.code_upload_lower_bound (Profile.directSum om res)
    (directSumGeometry om res hom r) code
end Ranks

section Canonical
variable [FiniteDimensional K E] [FiniteDimensional K P₁] [FiniteDimensional K P₂]
  [FiniteDimensional K P₃] [FiniteDimensional K T] [Finite K]
local notation "V" => ResidualUpload.Ambient P₁ P₂ P₃ T

/-- The global minimum-upload converse formula in actual residual coordinates:
dpriv+dtri plus the omniscience maximum/half-sum deficit term. -/
theorem canonical_directSum_upload_lower_bound {n : ℕ} {M : Three → Type*} {B : Type*}
    (om : Task K E) (res : Task K V) (hom : ∀ i, om.U i = ⊤) (r : ResidualGeometry res)
    (h₀ : res.A 0 = ResidualUpload.A₁ K P₁ P₂ P₃ T)
    (h₁ : res.A 1 = ResidualUpload.A₂ K P₁ P₂ P₃ T)
    (h₂ : res.A 2 = ResidualUpload.A₃ K P₁ P₂ P₃ T)
    (code : (Profile.directSum om res).FiniteCode n M B) :
    ((Module.finrank K P₁ : ℝ)+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T) +
      max (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))
        (max ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2))))
        ((((Module.finrank K E : ℝ)-Module.finrank K (om.A 0))+
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 1))+
          ((Module.finrank K E : ℝ)-Module.finrank K (om.A 2)))/2) ≤ code.toCode.uploadCost := by
  have hb := directSum_upload_lower_bound om res hom r code
  have hg : 2*(Module.finrank K ↥(res.A 0 ⊔ res.A 1 ⊔ res.A 2):ℝ)-
      (Module.finrank K (res.A 0)+Module.finrank K (res.A 1)+Module.finrank K (res.A 2)) =
      (Module.finrank K P₁ : ℝ)+Module.finrank K P₂+Module.finrank K P₃+Module.finrank K T := by
    rw [h₀,h₁,h₂,ResidualUpload.sides_span,finrank_top]
    exact_mod_cast (ResidualUpload.gamma_rank (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := T))
  rwa [hg] at hb
end Canonical

end UploadBroadcast.GlobalUploadGeometry
