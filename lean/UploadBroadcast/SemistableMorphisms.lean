import UploadBroadcast.SemistableFiltration

/-! Kernels, saturated images, and simple morphisms of actual semistable tasks. -/
namespace UploadBroadcast.TaskDecomposition
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Rank-nullity on a designated actual subspace, retaining its ambient
intersection with the kernel. -/
theorem map_intersection_finrank [FiniteDimensional K V]
    (A : Submodule K V) (f : V →ₗ[K] W) :
    Module.finrank K (A.map f)+Module.finrank K ↥(A ⊓ LinearMap.ker f)=
      Module.finrank K A := by
  have h := (f.comp A.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.ker_comp,
    finrank_comap_subtype,inf_comm] at h
  exact h

/-- A preserving map's image in each designated space lies in the actual
intersection with its full ambient image. -/
theorem image_le_intersection (S : Task K V) (T : Task K W)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) (i : Fin 3 × Bool) :
    (S.spaces i).map f ≤ T.spaces i ⊓ LinearMap.range f := by
  rintro x ⟨a,ha,rfl⟩
  exact ⟨hf i a ha,⟨a,rfl⟩⟩

/-- Every morphism between semistable actual tasks has a zero-defect induced
kernel, a zero-defect induced image, and a saturated image at every flag vertex.
This establishes strictness directly by six rank-nullity equations. -/
theorem Task.IsSemistable.kernel_image_saturated [FiniteDimensional K V]
    [FiniteDimensional K W] {S : Task K V} {T : Task K W}
    (hS : S.IsSemistable) (hT : T.IsSemistable)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) :
    S.componentDefect (LinearMap.ker f)=0 ∧
      T.componentDefect (LinearMap.range f)=0 ∧
      ∀ i, (S.spaces i).map f=T.spaces i ⊓ LinearMap.range f := by
  have hk := hS.2 (LinearMap.ker f)
  have hr := hT.2 (LinearMap.range f)
  have hz := hS.1
  have hdim := f.finrank_range_add_finrank_ker
  have hu0 := map_intersection_finrank (S.U 0) f
  have hu1 := map_intersection_finrank (S.U 1) f
  have hu2 := map_intersection_finrank (S.U 2) f
  have ha0 := map_intersection_finrank (S.A 0) f
  have ha1 := map_intersection_finrank (S.A 1) f
  have ha2 := map_intersection_finrank (S.A 2) f
  have hle := fun i => Submodule.finrank_mono (image_le_intersection S T f hf i)
  have hU0 := hle (0,true)
  have hU1 := hle (1,true)
  have hU2 := hle (2,true)
  have hA0 := hle (0,false)
  have hA1 := hle (1,false)
  have hA2 := hle (2,false)
  change -3*(Module.finrank K V:ℤ)+Module.finrank K (S.U 0)+Module.finrank K (S.U 1)+
    Module.finrank K (S.U 2)+Module.finrank K (S.A 0)+Module.finrank K (S.A 1)+
    Module.finrank K (S.A 2)=0 at hz
  unfold Task.componentDefect Task.componentDimension ReflectionReduction.defect at hk hr ⊢
  dsimp only at hk hr
  change Module.finrank K ((S.U 0).map f) ≤ Module.finrank K ↥(T.U 0 ⊓ LinearMap.range f) at hU0
  change Module.finrank K ((S.U 1).map f) ≤ Module.finrank K ↥(T.U 1 ⊓ LinearMap.range f) at hU1
  change Module.finrank K ((S.U 2).map f) ≤ Module.finrank K ↥(T.U 2 ⊓ LinearMap.range f) at hU2
  change Module.finrank K ((S.A 0).map f) ≤ Module.finrank K ↥(T.A 0 ⊓ LinearMap.range f) at hA0
  change Module.finrank K ((S.A 1).map f) ≤ Module.finrank K ↥(T.A 1 ⊓ LinearMap.range f) at hA1
  change Module.finrank K ((S.A 2).map f) ≤ Module.finrank K ↥(T.A 2 ⊓ LinearMap.range f) at hA2
  have hker : -3*(Module.finrank K (LinearMap.ker f):ℤ)+
      Module.finrank K ↥(S.U 0 ⊓ LinearMap.ker f)+Module.finrank K ↥(S.U 1 ⊓ LinearMap.ker f)+
      Module.finrank K ↥(S.U 2 ⊓ LinearMap.ker f)+Module.finrank K ↥(S.A 0 ⊓ LinearMap.ker f)+
      Module.finrank K ↥(S.A 1 ⊓ LinearMap.ker f)+Module.finrank K ↥(S.A 2 ⊓ LinearMap.ker f)=0 := by omega
  have hran : -3*(Module.finrank K (LinearMap.range f):ℤ)+
      Module.finrank K ↥(T.U 0 ⊓ LinearMap.range f)+Module.finrank K ↥(T.U 1 ⊓ LinearMap.range f)+
      Module.finrank K ↥(T.U 2 ⊓ LinearMap.range f)+Module.finrank K ↥(T.A 0 ⊓ LinearMap.range f)+
      Module.finrank K ↥(T.A 1 ⊓ LinearMap.range f)+Module.finrank K ↥(T.A 2 ⊓ LinearMap.range f)=0 := by omega
  refine ⟨hker,hran,?_⟩
  intro i
  apply Submodule.eq_of_le_of_finrank_eq (image_le_intersection S T f hf i)
  rcases i with ⟨i,b⟩
  fin_cases i <;> cases b
  all_goals first
    | change Module.finrank K ((S.U 0).map f) = Module.finrank K ↥(T.U 0 ⊓ LinearMap.range f)
    | change Module.finrank K ((S.U 1).map f) = Module.finrank K ↥(T.U 1 ⊓ LinearMap.range f)
    | change Module.finrank K ((S.U 2).map f) = Module.finrank K ↥(T.U 2 ⊓ LinearMap.range f)
    | change Module.finrank K ((S.A 0).map f) = Module.finrank K ↥(T.A 0 ⊓ LinearMap.range f)
    | change Module.finrank K ((S.A 1).map f) = Module.finrank K ↥(T.A 1 ⊓ LinearMap.range f)
    | change Module.finrank K ((S.A 2).map f) = Module.finrank K ↥(T.A 2 ⊓ LinearMap.range f)
  all_goals omega

/-- The induced kernel of a semistable morphism is semistable. -/
theorem Task.IsSemistable.kernel [FiniteDimensional K V] [FiniteDimensional K W]
    {S : Task K V} {T : Task K W} (hS : S.IsSemistable) (hT : T.IsSemistable)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) :
    (S.onComponent (LinearMap.ker f)).IsSemistable :=
  hS.onComponent _ (hS.kernel_image_saturated hT f hf).1

/-- The induced image of a semistable morphism is semistable. -/
theorem Task.IsSemistable.image [FiniteDimensional K V] [FiniteDimensional K W]
    {S : Task K V} {T : Task K W} (hS : S.IsSemistable) (hT : T.IsSemistable)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) :
    (T.onComponent (LinearMap.range f)).IsSemistable :=
  hT.onComponent _ (hS.kernel_image_saturated hT f hf).2.1

/-- A nonzero morphism between regular-simple actual tasks is a bijection of
ambient spaces; this uses no categorical or root classification. -/
theorem Task.IsRegularSimple.bijective_of_nonzero [FiniteDimensional K V]
    [FiniteDimensional K W] {S : Task K V} {T : Task K W}
    (hS : S.IsRegularSimple) (hT : T.IsRegularSimple)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) (hne : f≠0) :
    Function.Bijective f := by
  obtain ⟨hk,hr,_⟩ := hS.1.kernel_image_saturated hT.1 f hf
  constructor
  · obtain hz | hz := hS.2.2 _ hk
    · exact LinearMap.ker_eq_bot.mp hz
    · exact False.elim (hne (LinearMap.ker_eq_top.mp hz))
  · obtain hz | hz := hT.2.2 _ hr
    · exact False.elim (hne (LinearMap.range_eq_bot.mp hz))
    · exact LinearMap.range_eq_top.mp hz

/-- The inverse of a nonzero regular-simple morphism preserves every actual
flag because its image is saturated. -/
theorem Task.IsRegularSimple.configurationIso_of_nonzero [FiniteDimensional K V]
    [FiniteDimensional K W] {S : Task K V} {T : Task K W}
    (hS : S.IsRegularSimple) (hT : T.IsRegularSimple)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) (hne : f≠0) :
    ConfigurationIso S.spaces T.spaces := by
  let e := LinearEquiv.ofBijective f (hS.bijective_of_nonzero hT f hf hne)
  refine ⟨e,hf,?_⟩
  intro i y hy
  have hs := (hS.1.kernel_image_saturated hT.1 f hf).2.2 i
  have hsur := (hS.bijective_of_nonzero hT f hf hne).2
  rw [LinearMap.range_eq_top.mpr hsur,inf_top_eq] at hs
  have him : y ∈ (S.spaces i).map f := hs.symm ▸ hy
  obtain ⟨x,hx,he⟩ := him
  have he' : e x=y := he
  change e.symm y ∈ S.spaces i
  rw [←he',e.symm_apply_apply]
  exact hx

/-- Distinct regular-simple isomorphism classes have no nonzero morphisms. -/
theorem Task.IsRegularSimple.hom_zero_of_not_iso [FiniteDimensional K V]
    [FiniteDimensional K W] {S : Task K V} {T : Task K W}
    (hS : S.IsRegularSimple) (hT : T.IsRegularSimple)
    (hni : ¬ConfigurationIso S.spaces T.spaces)
    (f : V →ₗ[K] W) (hf : Preserves S.spaces T.spaces f) : f=0 := by
  by_contra hn
  exact hni (hS.configurationIso_of_nonzero hT f hf hn)

end UploadBroadcast.TaskDecomposition
