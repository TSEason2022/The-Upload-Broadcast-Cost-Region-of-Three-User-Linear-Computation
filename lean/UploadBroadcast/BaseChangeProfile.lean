import UploadBroadcast.ScalarExtensionConfiguration
import UploadBroadcast.AllocationProfile
import Mathlib.FieldTheory.Finite.GaloisField

/-! Exact invariance of the fifteen numerical profile entries under finite
field extension, plus a concrete quadratic extension of the binary field. -/
namespace UploadBroadcast
open scoped TensorProduct
variable {K E F J : Type*} [Field K] [Field E] [Algebra K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [Fintype J] [DecidableEq J]

 theorem condRank_baseChange (b : Basis J K E) (C A : Submodule K F) :
    condRank (C.baseChange E) (A.baseChange E) = condRank C A := by
  unfold condRank
  rw [← TaskDecomposition.baseChange_sup,
    TaskDecomposition.finrank_baseChange b, TaskDecomposition.finrank_baseChange b]

theorem rawEntry_baseChange (b : Basis J K E) (A U : Fin 3 → Submodule K F)
    (r : Profile.Index) :
    Allocation.rawEntry (fun i => (A i).baseChange E) (fun i => (U i).baseChange E) r =
      Allocation.rawEntry A U r := by
  cases r with
  | inl r =>
    simp only [Allocation.rawEntry, Allocation.rawFirstEntry, Allocation.demandRank,
      ← TaskDecomposition.baseChange_inf b, ← TaskDecomposition.baseChange_sup,
      condRank_baseChange b]
  | inr r =>
    simp only [Allocation.rawEntry, Allocation.rawSecondEntry, Allocation.demandRank,
      ← TaskDecomposition.baseChange_inf b, ← TaskDecomposition.baseChange_sup,
      condRank_baseChange b]

theorem rawRankBound_baseChange (b : Basis J K E) (A U : Fin 3 → Submodule K F) :
    Allocation.rawRankBound (fun i => (A i).baseChange E) (fun i => (U i).baseChange E) =
      Allocation.rawRankBound A U := by
  unfold Allocation.rawRankBound
  congr 1
  funext r
  exact rawEntry_baseChange b A U r

namespace BinaryExtension
abbrev F4 := GaloisField 2 2

theorem degree : Module.finrank (ZMod 2) F4 = 2 := GaloisField.finrank 2 (by decide)
theorem card : Nat.card F4 = 4 := by
  simpa using GaloisField.card 2 2 (by decide : (2:ℕ) ≠ 0)

noncomputable def basis : Basis (Fin 2) (ZMod 2) F4 :=
  (Module.finBasis (ZMod 2) F4).reindex (finCongr degree)

end BinaryExtension
end UploadBroadcast
