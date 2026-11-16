import UploadBroadcast.ResidualComponentAdditivity

/-! Intrinsic residual activity and zero excess on arbitrary actual binary
coefficient factors, used after a further physical component extraction. -/
namespace UploadBroadcast.ResidualComponentAdditivity
open Module
variable {K F G : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G]
set_option maxHeartbeats 1000000

theorem ActiveResidual.directSum_left (T : Task K F) (S : Task K G)
    (h : ActiveResidual (Profile.directSum T S)) : ActiveResidual T := by
  have hbot (A : Submodule K F) (B : Submodule K G) (hh : A.prod B = ⊥) : A = ⊥ :=
    ((Submodule.prod_eq_bot_iff K F G).mp hh).1
  have htop (A : Submodule K F) (B : Submodule K G) (hh : A.prod B = ⊤) : A = ⊤ :=
    ((Submodule.prod_eq_top_iff K F G).mp hh).1
  constructor
  · rw [disjoint_iff]
    apply hbot
    simpa only [Profile.directSum,Submodule.prod_inf_prod] using h.disjoint₀₁.eq_bot
  · rw [disjoint_iff]
    apply hbot
    simpa only [Profile.directSum,Submodule.prod_inf_prod] using h.disjoint₀₂.eq_bot
  · rw [disjoint_iff]
    apply hbot
    simpa only [Profile.directSum,Submodule.prod_inf_prod] using h.disjoint₁₂.eq_bot
  · apply htop
    simpa only [Profile.directSum,Submodule.prod_sup_prod] using h.spanning
  · intro i j hij
    apply htop
    simpa only [Profile.directSum,Submodule.prod_sup_prod] using h.private_active i j hij
  · have hh := Submodule.map_mono (f := LinearMap.fst K F G) h.tripod_active
    simpa only [Profile.directSum,Submodule.prod_inf_prod,Submodule.prod_sup_prod,
      Submodule.prod_map_fst] using hh
  · apply hbot
    simpa only [commonSeed,Profile.directSum,Submodule.prod_inf_prod,Submodule.prod_sup_prod]
      using h.common_zero

theorem ActiveResidual.directSum_right (T : Task K F) (S : Task K G)
    (h : ActiveResidual (Profile.directSum T S)) : ActiveResidual S := by
  have hbot (A : Submodule K F) (B : Submodule K G) (hh : A.prod B = ⊥) : B = ⊥ :=
    ((Submodule.prod_eq_bot_iff K F G).mp hh).2
  have htop (A : Submodule K F) (B : Submodule K G) (hh : A.prod B = ⊤) : B = ⊤ :=
    ((Submodule.prod_eq_top_iff K F G).mp hh).2
  constructor
  · rw [disjoint_iff]
    apply hbot
    simpa only [Profile.directSum,Submodule.prod_inf_prod] using h.disjoint₀₁.eq_bot
  · rw [disjoint_iff]
    apply hbot
    simpa only [Profile.directSum,Submodule.prod_inf_prod] using h.disjoint₀₂.eq_bot
  · rw [disjoint_iff]
    apply hbot
    simpa only [Profile.directSum,Submodule.prod_inf_prod] using h.disjoint₁₂.eq_bot
  · apply htop
    simpa only [Profile.directSum,Submodule.prod_sup_prod] using h.spanning
  · intro i j hij
    apply htop
    simpa only [Profile.directSum,Submodule.prod_sup_prod] using h.private_active i j hij
  · have hh := Submodule.map_mono (f := LinearMap.snd K F G) h.tripod_active
    simpa only [Profile.directSum,Submodule.prod_inf_prod,Submodule.prod_sup_prod,
      Submodule.prod_map_snd] using hh
  · apply hbot
    simpa only [commonSeed,Profile.directSum,Submodule.prod_inf_prod,Submodule.prod_sup_prod]
      using h.common_zero

variable [FiniteDimensional K F] [FiniteDimensional K G]

/-- Zero total side-information excess forces zero excess in both actual
factors; nonnegativity follows from their inherited spanning geometry. -/
theorem zero_excess_directSum_factors (T : Task K F) (S : Task K G)
    (h : ActiveResidual (Profile.directSum T S))
    (hz : finrank K ((Profile.directSum T S).A 0) +
      finrank K ((Profile.directSum T S).A 1) +
      finrank K ((Profile.directSum T S).A 2) = finrank K (F × G)) :
    (finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F) ∧
    (finrank K (S.A 0)+finrank K (S.A 1)+finrank K (S.A 2) = finrank K G) := by
  have hT := h.directSum_left T S
  have hS := h.directSum_right T S
  have hdT₀ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1)
  have hdT₁ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0 ⊔ T.A 1) (T.A 2)
  rw [hT.spanning,finrank_top] at hdT₁
  have hdS₀ := Submodule.finrank_sup_add_finrank_inf_eq (S.A 0) (S.A 1)
  have hdS₁ := Submodule.finrank_sup_add_finrank_inf_eq (S.A 0 ⊔ S.A 1) (S.A 2)
  rw [hS.spanning,finrank_top] at hdS₁
  simp only [Profile.directSum,Profile.finrank_submodule_prod,Module.finrank_prod] at hz
  omega

section Products
variable {I : Type*} {V : I → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
open FiniteRelayAssembly

omit [FiniteDimensional K F] [FiniteDimensional K G] in
/-- Conversely, an actual coefficient product of active residuals is active. -/
theorem ActiveResidual.product (T : ∀ i, Task K (V i)) (h : ∀ i, ActiveResidual (T i)) :
    ActiveResidual (task T) := by
  constructor
  · rw [disjoint_iff]
    simp only [task,←space_inf]
    simp_rw [(h _).disjoint₀₁.eq_bot]
    simp [space]
  · rw [disjoint_iff]
    simp only [task,←space_inf]
    simp_rw [(h _).disjoint₀₂.eq_bot]
    simp [space]
  · rw [disjoint_iff]
    simp only [task,←space_inf]
    simp_rw [(h _).disjoint₁₂.eq_bot]
    simp [space]
  · simp only [task,←space_sup]
    simp_rw [(h _).spanning]
    simp [space]
  · intro i j hij
    simp only [task,←space_sup]
    simp_rw [(h _).private_active i j hij]
    simp [space]
  · simp only [task,←space_sup,←space_inf]
    exact Submodule.pi_mono fun i _ => (h i).tripod_active
  · rw [commonSeed_product]
    simp_rw [(h _).common_zero]
    simp [space]

variable [Fintype I] [∀ i, FiniteDimensional K (V i)]
open scoped BigOperators
omit [FiniteDimensional K F] [FiniteDimensional K G] in
/-- Zero excess is preserved by every finite actual product, including the
empty product. No activity hypothesis is needed for this rank identity. -/
theorem zero_excess_product (T : ∀ i, Task K (V i))
    (h : ∀ i, finrank K ((T i).A 0)+finrank K ((T i).A 1)+finrank K ((T i).A 2) = finrank K (V i)) :
    finrank K ((task T).A 0)+finrank K ((task T).A 1)+finrank K ((task T).A 2) =
      finrank K (∀ i, V i) := by
  simp only [task,finrank_space,Module.finrank_pi_fintype]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => h i)
end Products

section Normalized
omit [FiniteDimensional K G] in
/-- Source side-information excess is nonnegative for every normalized
feasible task; residual activity is unnecessary. -/
theorem spanning_side_dimension_le (T : Task K F) (hspan : T.Spanning) :
    finrank K F ≤ finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) := by
  have hs : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤ := by
    simpa only [Task.Spanning,Profile.three_iSup] using hspan
  have h₀ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1)
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0 ⊔ T.A 1) (T.A 2)
  rw [hs,finrank_top] at h₁
  omega

omit [FiniteDimensional K G] in
/-- Zero excess is equivalent to an actual three-way direct sum for every
normalized task. Pairwise disjointness is derived, not assumed. -/
theorem spanning_zero_excess_iff (T : Task K F) (hspan : T.Spanning) :
    (finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2) = finrank K F) ↔
      IsCompl (T.A 0) (T.A 1 ⊔ T.A 2) ∧ Disjoint (T.A 1) (T.A 2) := by
  have hs : T.A 0 ⊔ T.A 1 ⊔ T.A 2 = ⊤ := by
    simpa only [Task.Spanning,Profile.three_iSup] using hspan
  have h₁₂ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 1) (T.A 2)
  have h₀ := Submodule.finrank_sup_add_finrank_inf_eq (T.A 0) (T.A 1 ⊔ T.A 2)
  rw [←sup_assoc,hs,finrank_top] at h₀
  constructor
  · intro hz
    have hi : T.A 0 ⊓ (T.A 1 ⊔ T.A 2) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hj : T.A 1 ⊓ T.A 2 = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    exact ⟨⟨disjoint_iff.mpr hi,codisjoint_iff.mpr (by rw [←sup_assoc,hs])⟩,disjoint_iff.mpr hj⟩
  · rintro ⟨hi,hj⟩
    rw [hj.eq_bot,finrank_bot,add_zero] at h₁₂
    rw [hi.disjoint.eq_bot,finrank_bot,add_zero,h₁₂] at h₀
    omega
end Normalized
end UploadBroadcast.ResidualComponentAdditivity
