import UploadBroadcast.Profile

/-! Exact profile invariance under ambient linear equivalences and user
permutations. These are rank identities, not an operational capacity theorem. -/
namespace UploadBroadcast.Profile
open Module
variable {K F G : Type*} [Field K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup G] [Module K G] [FiniteDimensional K G]

def mapTask (e : F ≃ₗ[K] G) (T : Task K F) : Task K G where
  A i := (T.A i).map e.toLinearMap
  U i := (T.U i).map e.toLinearMap
  side_le_signal i := Submodule.map_mono (T.side_le_signal i)
  feasible i := by
    rw [← Submodule.map_iSup]
    exact Submodule.map_mono (T.feasible i)

theorem condRank_map (e : F ≃ₗ[K] G) (C A : Submodule K F) :
    condRank (C.map e.toLinearMap) (A.map e.toLinearMap) = condRank C A := by
  unfold condRank
  rw [← Submodule.map_sup, e.finrank_map_eq, e.finrank_map_eq]

omit [FiniteDimensional K F] [FiniteDimensional K G] in
theorem totalDemand_mapTask (e : F ≃ₗ[K] G) (T : Task K F) :
    totalDemand (mapTask e T) = totalDemand T := by
  simp [totalDemand, mapTask, e.finrank_map_eq]

theorem firstEntry_mapTask (e : F ≃ₗ[K] G) (T : Task K F) (i j k : Three) :
    firstEntry (mapTask e T) i j k = firstEntry T i j k := by
  unfold firstEntry
  rw [totalDemand_mapTask]
  simp only [mapTask, ← Submodule.map_inf e.toLinearMap e.injective,
    ← Submodule.map_sup, condRank_map]

theorem secondEntry_mapTask (e : F ≃ₗ[K] G) (T : Task K F) (i j k ell : Three) :
    secondEntry (mapTask e T) i j k ell = secondEntry T i j k ell := by
  unfold secondEntry
  rw [totalDemand_mapTask]
  simp only [mapTask, ← Submodule.map_inf e.toLinearMap e.injective,
    ← Submodule.map_sup, condRank_map]

theorem entry_mapTask (e : F ≃ₗ[K] G) (T : Task K F) (r : Index) :
    entry (mapTask e T) r = entry T r := by
  cases r with
  | inl r => exact firstEntry_mapTask e T _ _ _
  | inr r => exact secondEntry_mapTask e T _ _ _ _

def reindexTask (p : Equiv.Perm Three) (T : Task K F) : Task K F where
  A i := T.A (p i)
  U i := T.U (p i)
  side_le_signal i := T.side_le_signal (p i)
  feasible i := by
    rw [Equiv.iSup_comp p]
    exact T.feasible (p i)

omit [FiniteDimensional K F] in
theorem totalDemand_reindexTask (p : Equiv.Perm Three) (T : Task K F) :
    totalDemand (reindexTask p T) = totalDemand T := by
  exact Equiv.sum_comp p (fun i => finrank K (T.U i) - finrank K (T.A i))

theorem three_iInf {α : Type*} [CompleteLattice α] (a : Three → α) :
    (⨅ i, a i) = (a 0 ⊓ a 1) ⊓ a 2 :=
  three_iSup (α := OrderDual α) a

theorem firstEntry_reindexTask (p : Equiv.Perm Three) (T : Task K F) (i j k : Three) :
    firstEntry (reindexTask p T) i j k = firstEntry T (p i) (p j) (p k) := by
  unfold firstEntry
  rw [totalDemand_reindexTask]
  rfl

theorem secondEntry_reindexTask (p : Equiv.Perm Three) (T : Task K F) (i j k ell : Three) :
    secondEntry (reindexTask p T) i j k ell = secondEntry T (p i) (p j) (p k) (p ell) := by
  have ht : T.U (p 0) ⊓ T.U (p 1) ⊓ T.U (p 2) = T.U 0 ⊓ T.U 1 ⊓ T.U 2 := by
    rw [← three_iInf (fun i => T.U (p i)), Equiv.iInf_comp, three_iInf]
  unfold secondEntry
  rw [totalDemand_reindexTask]
  simp only [reindexTask, ht]

end UploadBroadcast.Profile
