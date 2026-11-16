import UploadBroadcast.EdgeExtraction
import UploadBroadcast.ProfileTransport

/-! User relabeling preserves the actual simultaneous-subspace indecomposable
predicate. No classification uniqueness theorem is needed for this transport. -/
namespace UploadBroadcast.TaskUserPermutation
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

theorem reindex_indecomposable (T : Task K F) (p : Equiv.Perm Three)
    (hT : TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces ⊤) :
    TaskDecomposition.Indecomposable (EdgeExtraction.configuration (Profile.reindexTask p T)).spaces ⊤ := by
  refine ⟨hT.1,fun P Q h => hT.2 P Q ⟨h.disjoint,h.sup_eq,?_⟩⟩
  rintro ⟨i,b⟩
  have hh := h.compatible (p.symm i,b)
  simpa only [TaskDecomposition.Task.spaces,EdgeExtraction.configuration,
    Profile.reindexTask,p.apply_symm_apply] using hh

end UploadBroadcast.TaskUserPermutation
