import UploadBroadcast.OriginalUploadChart
import UploadBroadcast.PairReductionRanks

namespace UploadBroadcast.Task
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
variable {K F : Type*} [Field K] [Finite K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Original-task Ω value using the intrinsic active-pair intersection ranks. -/
noncomputable def uploadOmniscienceValue (T : Task K F) : ℝ :=
  T.pairFreeChart.omegaValue (T.intrinsicActivePairRank 0)
    (T.intrinsicActivePairRank 1) (T.intrinsicActivePairRank 2)

/-- Source minimum-upload expression for an arbitrary original task. -/
noncomputable def minimumUploadFormula (T : Task K F) : ℝ :=
  T.pairFreeChart.uploadFormula (T.intrinsicActivePairRank 0)
    (T.intrinsicActivePairRank 1) (T.intrinsicActivePairRank 2)

end UploadBroadcast.Task
