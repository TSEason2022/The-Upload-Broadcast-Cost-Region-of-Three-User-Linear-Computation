import UploadBroadcast.EdgeDeficits
import UploadBroadcast.RelayCoordinateTransport

namespace UploadBroadcast.PhysicalCycleCoordinates
open Module EdgeExtraction
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Intersecting a direct edge sum with a signal keeps exactly its contained
summands. This rules out any cancellation-created extra direction. -/
theorem inf_sup_of_disjoint (A X Y : Submodule K V)
    (hX : Disjoint X A) (hY : Y ≤ A) : A ⊓ (X ⊔ Y)=Y := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu,v,hv,he⟩ := Submodule.mem_sup.mp hx.2
    have huA : u ∈ A := by
      have hh : u=x-v := by rw [← he]; abel
      rw [hh]
      exact A.sub_mem hx.1 (hY hv)
    have hz := Submodule.disjoint_def.mp hX u hu huA
    have hxv : x=v := by simpa only [hz,zero_add] using he.symm
    rwa [hxv]
  · exact le_inf hY le_sup_right

/-- Complete six-space signature on the span of a physical directed cycle
bundle. The assumptions are actual extracted EdgeBlock memberships. -/
theorem bundle_signature (T : Task K V) (W₀ W₁ W₂ : Submodule K V)
    (h₀ : EdgeBlock T 0 1 2 W₀) (h₁ : EdgeBlock T 1 2 0 W₁)
    (h₂ : EdgeBlock T 2 0 1 W₂) :
    let W := W₀ ⊔ W₁ ⊔ W₂
    T.A 0 ⊓ W=W₁ ∧ T.A 1 ⊓ W=W₂ ∧ T.A 2 ⊓ W=W₀ ∧
    T.U 0 ⊓ W=W₁ ⊔ W₂ ∧ T.U 1 ⊓ W=W₀ ⊔ W₂ ∧ T.U 2 ⊓ W=W₀ ⊔ W₁ := by
  let W := W₀ ⊔ W₁ ⊔ W₂
  have hu₀ : T.U 0 ⊓ W = W₁ ⊔ W₂ := by
    change T.U 0 ⊓ (W₀ ⊔ W₁ ⊔ W₂) = _
    rw [sup_assoc]
    exact inf_sup_of_disjoint _ _ _ h₀.third_zero
      (sup_le (h₁.source.trans (T.side_le_signal 0)) h₂.target)
  have hu₁ : T.U 1 ⊓ W = W₀ ⊔ W₂ := by
    have he : W = W₁ ⊔ (W₀ ⊔ W₂) := by dsimp [W]; ac_rfl
    rw [he]
    exact inf_sup_of_disjoint _ _ _ h₁.third_zero
      (sup_le h₀.target (h₂.source.trans (T.side_le_signal 1)))
  have hu₂ : T.U 2 ⊓ W = W₀ ⊔ W₁ := by
    have he : W = W₂ ⊔ (W₀ ⊔ W₁) := by dsimp [W]; ac_rfl
    rw [he]
    exact inf_sup_of_disjoint _ _ _ h₂.third_zero
      (sup_le (h₀.source.trans (T.side_le_signal 2)) h₁.target)
  have ha₀ : T.A 0 ⊓ W=W₁ := by
    calc
      T.A 0 ⊓ W = T.A 0 ⊓ (T.U 0 ⊓ W) := by rw [← inf_assoc,inf_eq_left.mpr (T.side_le_signal 0)]
      _ = T.A 0 ⊓ (W₂ ⊔ W₁) := by rw [hu₀,sup_comm W₁ W₂]
      _ = W₁ := inf_sup_of_disjoint _ _ _ h₂.target_side_zero h₁.source
  have ha₁ : T.A 1 ⊓ W=W₂ := by
    calc
      T.A 1 ⊓ W = T.A 1 ⊓ (T.U 1 ⊓ W) := by rw [← inf_assoc,inf_eq_left.mpr (T.side_le_signal 1)]
      _ = T.A 1 ⊓ (W₀ ⊔ W₂) := by rw [hu₁]
      _ = W₂ := inf_sup_of_disjoint _ _ _ h₀.target_side_zero h₂.source
  have ha₂ : T.A 2 ⊓ W=W₀ := by
    calc
      T.A 2 ⊓ W = T.A 2 ⊓ (T.U 2 ⊓ W) := by rw [← inf_assoc,inf_eq_left.mpr (T.side_le_signal 2)]
      _ = T.A 2 ⊓ (W₁ ⊔ W₀) := by rw [hu₂,sup_comm W₀ W₁]
      _ = W₀ := inf_sup_of_disjoint _ _ _ h₁.target_side_zero h₀.source
  exact ⟨ha₀,ha₁,ha₂,hu₀,hu₁,hu₂⟩

/-- The physically extracted cycle span is itself locally generated. -/
theorem bundle_locally_generated (T : Task K V) (W₀ W₁ W₂ : Submodule K V)
    (h₀ : EdgeBlock T 0 1 2 W₀) (h₁ : EdgeBlock T 1 2 0 W₁)
    (h₂ : EdgeBlock T 2 0 1 W₂) : T.LocallyGenerated (W₀ ⊔ W₁ ⊔ W₂) := by
  obtain ⟨ha₀,ha₁,ha₂,_,_,_⟩ := bundle_signature T W₀ W₁ W₂ h₀ h₁ h₂
  unfold Task.LocallyGenerated
  rw [Profile.three_iSup]
  rw [inf_comm _ (T.A 0),inf_comm _ (T.A 1),inf_comm _ (T.A 2),ha₀,ha₁,ha₂]
  ac_rfl

/-- The edge blocks in a directed cycle have a genuine internal direct sum. -/
theorem bundle_disjoint (T : Task K V) (W₀ W₁ W₂ : Submodule K V)
    (h₀ : EdgeBlock T 0 1 2 W₀) (h₁ : EdgeBlock T 1 2 0 W₁)
    (h₂ : EdgeBlock T 2 0 1 W₂) :
    Disjoint W₀ (W₁ ⊔ W₂) ∧ Disjoint W₁ W₂ :=
  ⟨h₀.third_zero.mono_right (sup_le (h₁.source.trans (T.side_le_signal 0)) h₂.target),
    h₁.third_zero.mono_right (h₂.source.trans (T.side_le_signal 1))⟩

/-- The opposite physical cycle has the corresponding literal six-space
signature, derived by user relabeling of actual edge flags. -/
theorem reverse_bundle_signature (T : Task K V) (W₀ W₁ W₂ : Submodule K V)
    (h₀ : EdgeBlock T 1 0 2 W₀) (h₁ : EdgeBlock T 2 1 0 W₁)
    (h₂ : EdgeBlock T 0 2 1 W₂) :
    let W := W₀ ⊔ W₁ ⊔ W₂
    T.A 0 ⊓ W=W₁ ∧ T.A 1 ⊓ W=W₂ ∧ T.A 2 ⊓ W=W₀ ∧
    T.U 0 ⊓ W=W₀ ⊔ W₁ ∧ T.U 1 ⊓ W=W₁ ⊔ W₂ ∧ T.U 2 ⊓ W=W₀ ⊔ W₂ := by
  let S := Profile.reindexTask (Equiv.swap 0 1) T
  have hh₀ : EdgeBlock S 0 1 2 W₀ := ⟨h₀.source,h₀.target,h₀.third_zero,h₀.target_side_zero⟩
  have hh₁ : EdgeBlock S 1 2 0 W₂ := ⟨h₂.source,h₂.target,h₂.third_zero,h₂.target_side_zero⟩
  have hh₂ : EdgeBlock S 2 0 1 W₁ := ⟨h₁.source,h₁.target,h₁.third_zero,h₁.target_side_zero⟩
  obtain ⟨ha₁,ha₀,ha₂,hu₁,hu₀,hu₂⟩ := bundle_signature S W₀ W₂ W₁ hh₀ hh₁ hh₂
  have he : W₀ ⊔ W₂ ⊔ W₁ = W₀ ⊔ W₁ ⊔ W₂ := by ac_rfl
  rw [he] at ha₁ ha₀ ha₂ hu₁ hu₀ hu₂
  refine ⟨ha₀,ha₁,ha₂,hu₀,?_,hu₂⟩
  exact hu₁.trans (sup_comm _ _)

theorem reverse_bundle_locally_generated (T : Task K V) (W₀ W₁ W₂ : Submodule K V)
    (h₀ : EdgeBlock T 1 0 2 W₀) (h₁ : EdgeBlock T 2 1 0 W₁)
    (h₂ : EdgeBlock T 0 2 1 W₂) : T.LocallyGenerated (W₀ ⊔ W₁ ⊔ W₂) := by
  obtain ⟨ha₀,ha₁,ha₂,_,_,_⟩ := reverse_bundle_signature T W₀ W₁ W₂ h₀ h₁ h₂
  unfold Task.LocallyGenerated
  rw [Profile.three_iSup]
  rw [inf_comm _ (T.A 0),inf_comm _ (T.A 1),inf_comm _ (T.A 2),ha₀,ha₁,ha₂]
  ac_rfl

end UploadBroadcast.PhysicalCycleCoordinates
