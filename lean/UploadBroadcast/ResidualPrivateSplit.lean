import UploadBroadcast.ResidualConverse
import UploadBroadcast.ResidualTaskAssembly

/-! Private-slice certificates derived from actual canonical coordinates and
full use of the private projections, including the output of privateTrim. -/
namespace UploadBroadcast.ResidualPrivateSplit
open ResidualUpload ResidualTaskAssembly ResidualConverse
variable {K P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

def embed₁ : P₁ →ₗ[K] Ambient P₁ P₂ P₃ D := side₁.comp (LinearMap.inl K P₁ D)
def embed₂ : P₂ →ₗ[K] Ambient P₁ P₂ P₃ D := side₂.comp (LinearMap.inl K P₂ D)
def embed₃ : P₃ →ₗ[K] Ambient P₁ P₂ P₃ D := side₃.comp (LinearMap.inl K P₃ D)
def tripod₁ : D →ₗ[K] Ambient P₁ P₂ P₃ D := side₁.comp (LinearMap.inr K P₁ D)
def tripod₂ : D →ₗ[K] Ambient P₁ P₂ P₃ D := side₂.comp (LinearMap.inr K P₂ D)
def tripod₃ : D →ₗ[K] Ambient P₁ P₂ P₃ D := side₃.comp (LinearMap.inr K P₃ D)

@[simp] theorem tripod₃_eq : (tripod₃ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) =
    tripod₂ - tripod₁ := by
  ext t <;> simp [tripod₁,tripod₂,tripod₃,side₁,side₂,side₃]

private theorem range_split {P T F : Type*} [AddCommGroup P] [Module K P]
    [AddCommGroup T] [Module K T] [AddCommGroup F] [Module K F]
    (f : (P × T) →ₗ[K] F) : LinearMap.range f =
      LinearMap.range (f.comp (LinearMap.inl K P T)) ⊔
      LinearMap.range (f.comp (LinearMap.inr K P T)) := by
  apply le_antisymm
  · rintro _ ⟨⟨p,t⟩,rfl⟩
    have he : f (p,0) + f (0,t) = f (p,t) := by rw [← map_add]; simp
    exact he ▸ Submodule.add_mem_sup ⟨p,rfl⟩ ⟨t,rfl⟩
  · apply sup_le
    · rintro _ ⟨p,rfl⟩; exact ⟨(p,0),rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨(0,t),rfl⟩

/-- Fully used canonical private coordinates give all three actual private
projection certificates required by the nonlinear residual converse. -/
def fully_used_splits (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₁ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₂ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₃ : task.A 2 = A₃ K P₁ P₂ P₃ D)
    (hu₁ : used₁ task = ⊤) (hu₂ : used₂ task = ⊤) (hu₃ : used₃ task = ⊤) :
    ∀ i : Three, PrivateSplit task i
      (![LinearMap.range (tripod₁ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)),LinearMap.range (tripod₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)),
        LinearMap.range ((tripod₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D))-tripod₁)] i) := by
  have c₁ : PrivateSplit task 0 (LinearMap.range (tripod₁ (K := K))) := by
    apply PrivateSplit.of_raw_projection task 0 _ embed₁ private₁
    · intro p; rfl
    · rintro _ ⟨t,rfl⟩; rfl
    · rw [h₁]
      exact range_split (side₁ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := D))
    · intro j hj a ha
      fin_cases j
      · exact (hj rfl).elim
      · change a ∈ task.A 1 at ha
        rw [h₂] at ha
        obtain ⟨⟨p,t⟩,rfl⟩ := ha
        rfl
      · change a ∈ task.A 2 at ha
        rw [h₃] at ha
        obtain ⟨⟨p,t⟩,rfl⟩ := ha
        rfl
    · apply top_unique
      rw [← hu₁]
      exact sup_le (le_iSup_of_le ⟨1,by decide⟩ le_rfl) (le_iSup_of_le ⟨2,by decide⟩ le_rfl)
  have c₂ : PrivateSplit task 1 (LinearMap.range (tripod₂ (K := K))) := by
    apply PrivateSplit.of_raw_projection task 1 _ embed₂ private₂
    · intro p; rfl
    · rintro _ ⟨t,rfl⟩; rfl
    · rw [h₂]
      exact range_split (side₂ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := D))
    · intro j hj a ha
      fin_cases j
      · change a ∈ task.A 0 at ha
        rw [h₁] at ha
        obtain ⟨⟨p,t⟩,rfl⟩ := ha
        rfl
      · exact (hj rfl).elim
      · change a ∈ task.A 2 at ha
        rw [h₃] at ha
        obtain ⟨⟨p,t⟩,rfl⟩ := ha
        rfl
    · apply top_unique
      rw [← hu₂]
      exact sup_le (le_iSup_of_le ⟨0,by decide⟩ le_rfl) (le_iSup_of_le ⟨2,by decide⟩ le_rfl)
  have c₃ : PrivateSplit task 2 (LinearMap.range (tripod₃ (K := K))) := by
    apply PrivateSplit.of_raw_projection task 2 _ embed₃ private₃
    · intro p; simp [embed₃,side₃,private₃]
    · rintro _ ⟨t,rfl⟩; rfl
    · rw [h₃]
      exact range_split (side₃ (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (T := D))
    · intro j hj a ha
      fin_cases j
      · change a ∈ task.A 0 at ha
        rw [h₁] at ha
        obtain ⟨⟨p,t⟩,rfl⟩ := ha
        rfl
      · change a ∈ task.A 1 at ha
        rw [h₂] at ha
        obtain ⟨⟨p,t⟩,rfl⟩ := ha
        rfl
      · exact (hj rfl).elim
    · apply top_unique
      rw [← hu₃]
      exact sup_le (le_iSup_of_le ⟨0,by decide⟩ le_rfl) (le_iSup_of_le ⟨1,by decide⟩ le_rfl)
  intro i
  by_cases hi : i = 0
  · subst i; exact c₁
  by_cases hj : i = 1
  · subst i; exact c₂
  have hk : i = 2 := by fin_cases i <;> simp_all
  subst i
  simpa only [tripod₃_eq] using c₃

/-- No full-use certificate is requested after the proved private deletion. -/
noncomputable def trimmed_splits (task : Task K (Ambient P₁ P₂ P₃ D))
    (h₁ : task.A 0 = A₁ K P₁ P₂ P₃ D)
    (h₂ : task.A 1 = A₂ K P₁ P₂ P₃ D)
    (h₃ : task.A 2 = A₃ K P₁ P₂ P₃ D) :
    ∀ i : Three, PrivateSplit (privateTrim task) i
      (![LinearMap.range (tripod₁ (K := K) (P₁ := used₁ task) (P₂ := used₂ task) (P₃ := used₃ task) (D := D)),LinearMap.range (tripod₂ (K := K) (P₁ := used₁ task) (P₂ := used₂ task) (P₃ := used₃ task) (D := D)),
        LinearMap.range ((tripod₂ (K := K) (P₁ := used₁ task) (P₂ := used₂ task) (P₃ := used₃ task) (D := D))-tripod₁)] i) := by
  obtain ⟨ha,hb,hc⟩ := privateTrim_sides task h₁ h₂ h₃
  obtain ⟨hu,hv,hw⟩ := privateTrim_fully_used task
  exact fully_used_splits (privateTrim task) ha hb hc hu hv hw

end UploadBroadcast.ResidualPrivateSplit
