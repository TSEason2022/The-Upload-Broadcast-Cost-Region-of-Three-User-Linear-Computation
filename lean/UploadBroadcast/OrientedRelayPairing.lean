import UploadBroadcast.RelayCyclePairing

namespace UploadBroadcast.OrientedRelayPairing
open Module Profile RelayCyclePairing GlobalMenuAssembly
attribute [local instance] Classical.propDecidable
variable {K R V W : Type*} [Field K] [Fintype R]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def userOrder (b : Bool) : Equiv.Perm Three := if b then Equiv.swap 0 1 else Equiv.refl _
def cycleTask (K : Type*) [Field K] (b : Bool) : Task K (Three → K) :=
  if b then CycleDirectSumCoordinates.reverseCycleTask K else CycleDirectSumCoordinates.cycleTask K

def delta (b : Bool) (r : ℕ) : Profile.Index → ℝ :=
  if b then negativeDelta r else positiveDelta r

omit [FiniteDimensional K W] in
/-- Uniform typed coordinate endpoint for both physical orientations. -/
theorem exists_coordinates (b : Bool) (n : R → ℕ) (M : Task K W) (Z : Task K V)
    (r : ℕ) (hr : r ≤ Fintype.card R) (hc : r ≤ EdgeDeficits.cycleMultiplicity Z (userOrder b)) :
    ∃ (s : Fin r ↪ R) (v : Three → Fin r → V) (Q : Submodule K V)
      (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
      (hQ : TaskDecomposition.Split (EdgeExtraction.configuration Z).spaces ⊤ Q (bundleSpan v)),
      mapTask (repairCoordinates n s (bundleSplitCoordinates Z v hv Q hQ))
        (directSum (ResonantFiniteAssembly.task n) (directSum M Z)) =
        directSum (directSum (ResonantFiniteAssembly.task (fun i : Remaining s => n i.val)) M)
          (directSum (FiniteRelayAssembly.task (fun t : Fin r =>
            directSum (ResonantRelay.jordanTask K (n (s t))) (cycleTask K b)))
            (SplitTaskCoordinates.leftTask Z Q (bundleSpan v) hQ)) ∧
      Fintype.card (Remaining s)=Fintype.card R-r := by
  cases b with
  | false =>
    obtain ⟨s,v,Q,hv,hQ,he,_,hcard⟩ := exists_positive_repair_coordinates n M Z r hr hc
    exact ⟨s,v,Q,hv,hQ,he,hcard⟩
  | true =>
    obtain ⟨s,v,Q,hv,hQ,he,_,hcard⟩ := exists_negative_repair_coordinates n M Z r hr hc
    exact ⟨s,v,Q,hv,hQ,he,hcard⟩

omit [Fintype R] in
/-- Every fixed block in the repaired coordinate chart has an actual menu
and an exact total rank, including the untouched physical complement. -/
theorem fixed_realizes (b : Bool) (n : R → ℕ) {r : ℕ} (s : Fin r ↪ R) (Z : Task K V)
    (ha : ResidualComponentAdditivity.ActiveResidual Z)
    (hz : finrank K (Z.A 0)+finrank K (Z.A 1)+finrank K (Z.A 2)=finrank K V)
    (Q B : Submodule K V) (hs : TaskDecomposition.Split (EdgeExtraction.configuration Z).spaces ⊤ Q B) :
    RealizesMenu (directSum (FiniteRelayAssembly.task (fun t : Fin r =>
      directSum (ResonantRelay.jordanTask K (n (s t))) (cycleTask K b)))
      (SplitTaskCoordinates.leftTask Z Q B hs))
      ((∑ t, (3*(n (s t)+1)+4))+finrank K Q) (fun (_ : Unit) => delta b r) := by
  cases b
  · exact positive_fixed_block_realizes n s Z ha hz Q B hs
  · exact negative_fixed_block_realizes n s Z ha hz Q B hs

end UploadBroadcast.OrientedRelayPairing
