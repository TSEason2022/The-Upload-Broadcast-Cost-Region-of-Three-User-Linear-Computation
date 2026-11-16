import UploadBroadcast.ScalarExtensionConfiguration

/-!
# Descent of actual retracts after finite scalar extension

This proves the restriction-of-scalars and Krull–Schmidt step of the
manuscript's positive-excess descent argument. The existence of an absolutely
indecomposable real-root summand descending to the ground field is not assumed
implicitly, and is not proved by this file. It requires additional
representation-theoretic results beyond numerical root classification.
-/
noncomputable section
set_option maxRecDepth 4096
open scoped TensorProduct
namespace UploadBroadcast.TaskDecomposition
variable {K L V W ι J : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- If the extension of one indecomposable finite-field configuration is an
actual retract of the extension of another, the original configurations are
isomorphic. The supplied maps preserve all designated subspaces. -/
theorem iso_of_extended_retract [Finite K] [FiniteDimensional K V]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (b : Basis J K L)
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    (hS : Indecomposable S ⊤) (hT : Indecomposable T ⊤)
    (f : (L ⊗[K] V) →ₗ[L] (L ⊗[K] W))
    (g : (L ⊗[K] W) →ₗ[L] (L ⊗[K] V))
    (hf : Preserves (extendConfiguration (L := L) S) (extendConfiguration (L := L) T) f)
    (hg : Preserves (extendConfiguration (L := L) T) (extendConfiguration (L := L) S) g)
    (hgf : ∀ x, g (f x) = x) : ConfigurationIso S T := by
  classical
  let j : J := Classical.choice inferInstance
  let eV := restrictionCoordinates (V := V) b
  let eW := restrictionCoordinates (V := W) b
  let u : V →ₗ[K] (J → V) := LinearMap.single K (fun _ : J => V) j
  let p : (J → V) →ₗ[K] V := LinearMap.proj j
  let F : V →ₗ[K] (J → W) :=
    eW.toLinearMap.comp ((f.restrictScalars K).comp (eV.symm.toLinearMap.comp u))
  let G : (J → W) →ₗ[K] V :=
    p.comp (eV.toLinearMap.comp ((g.restrictScalars K).comp eW.symm.toLinearMap))
  apply iso_of_retract_copies hS hT F G
  · intro i x hx k _
    apply (mem_baseChange_iff_coordinates b (T i) _).mp
    apply hf i
    apply (mem_baseChange_iff_coordinates b (S i) _).mpr
    intro l
    change eV (eV.symm (u x)) l ∈ S i
    rw [LinearEquiv.apply_symm_apply]
    by_cases hl : l = j
    · subst l; simpa [u] using hx
    · simp [u, LinearMap.single_apply, Pi.single_eq_of_ne hl]
  · intro i x hx
    have h : eW.symm x ∈ (T i).baseChange L := by
      apply (mem_baseChange_iff_coordinates b (T i) _).mpr
      simpa [eW] using fun k => hx k (Set.mem_univ k)
    exact (mem_baseChange_iff_coordinates b (S i) _).mp (hg i _ h) j
  · intro x
    change p (eV (g (eW.symm (eW (f (eV.symm (u x))))))) = x
    rw [LinearEquiv.symm_apply_apply, hgf, LinearEquiv.apply_symm_apply]
    simp [p, u]

/-- Basis-free finite-extension formulation of the retract descent theorem. -/
theorem iso_of_finite_extension_retract [Finite K] [FiniteDimensional K V]
    [FiniteDimensional K L]
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    (hS : Indecomposable S ⊤) (hT : Indecomposable T ⊤)
    (f : (L ⊗[K] V) →ₗ[L] (L ⊗[K] W))
    (g : (L ⊗[K] W) →ₗ[L] (L ⊗[K] V))
    (hf : Preserves (extendConfiguration (L := L) S) (extendConfiguration (L := L) T) f)
    (hg : Preserves (extendConfiguration (L := L) T) (extendConfiguration (L := L) S) g)
    (hgf : ∀ x, g (f x) = x) : ConfigurationIso S T := by
  letI : Nonempty (Fin (Module.finrank K L)) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := K) (M := L))
  exact iso_of_extended_retract (Module.finBasis K L) hS hT f g hf hg hgf

/-- An actual simultaneous summand isomorphic to the extension of `S`
descends to an isomorphism of the two ground-field indecomposables. -/
theorem iso_of_extended_summand [Finite K] [FiniteDimensional K V]
    [FiniteDimensional K L]
    {S : ι → Submodule K V} {T : ι → Submodule K W}
    (hS : Indecomposable S ⊤) (hT : Indecomposable T ⊤)
    {P Q : Submodule L (L ⊗[K] W)}
    (hsplit : Split (extendConfiguration (L := L) T) ⊤ P Q)
    (hiso : ConfigurationIso (K := L) (V := L ⊗[K] V) (W := P) (extendConfiguration (L := L) S)
      (onSubspace (K := L) (V := L ⊗[K] W) (extendConfiguration (L := L) T) P)) : ConfigurationIso S T := by
  obtain ⟨e, he, hei⟩ := hiso
  obtain ⟨p, hp, hpi⟩ := hsplit.exists_retraction
  apply iso_of_finite_extension_retract hS hT
    (P.subtype.comp e.toLinearMap) (e.symm.toLinearMap.comp p)
  · intro i x hx
    exact he i x hx
  · intro i x hx
    exact hei i (p x) (hp i x hx)
  · intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpi,
      LinearEquiv.symm_apply_apply]

end UploadBroadcast.TaskDecomposition
