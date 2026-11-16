import UploadBroadcast.NonzeroRelationRestrictions

/-! Checked integer increments for the seven hyperplane families. -/
namespace UploadBroadcast.NonzeroHyperplaneProfiles
open Profile NonzeroDefectProfile NonzeroRelationRestrictions
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-- The arithmetic difference in the two remote first entries. -/
def incrementFormula (g : Family) (n : ℕ) (r : Fin 6) : ℕ :=
  let i := (firstOrder r).1
  let j := (firstOrder r).2.1
  if i = hyperplaneArm g ∨ j = hyperplaneArm g then 0 else
    min (fullSignal g n j-fullSide g n j)
      (fullSignal g n i+fullSignal g n j-fullAmbient g n) -
    min (fullSignal g n j-fullSide g n j)
      (fullSignal g n i+fullSignal g n j-fullAmbient g n-1)

lemma incrementFormula_eq (g : Family) (hg : g ≠ .R2) (n : ℕ) (hn : 1 ≤ n) (r : Fin 6) :
    incrementFormula g n r = firstIncrement g r := by
  cases g <;> fin_cases r <;>
    simp_all [incrementFormula,firstOrder,hyperplaneArm,fullSignal,fullSide,
      fullAmbient,firstIncrement] <;> omega

end UploadBroadcast.NonzeroHyperplaneProfiles
