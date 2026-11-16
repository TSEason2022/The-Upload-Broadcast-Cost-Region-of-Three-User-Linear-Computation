import UploadBroadcast.LinearAlgebra
import UploadBroadcast.ProfileTransport

namespace UploadBroadcast.Task
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

theorem induced_sides_span (T : Task K F) (P : Submodule K F) (hP : T.LocallyGenerated P) :
    (⨆ i, (T.A i).comap P.subtype) = ⊤ := by
  let S : Submodule K P := ⨆ i, (T.A i).comap P.subtype
  have hm : S.map P.subtype = P := by
    dsimp [S]
    rw [Submodule.map_iSup]
    simp only [Submodule.map_comap_eq,Submodule.range_subtype]
    simpa only [inf_comm] using hP.symm
  apply top_unique
  intro p _
  have hp : (p : F) ∈ S.map P.subtype := hm.symm ▸ p.property
  obtain ⟨a,ha,he⟩ := hp
  have he' : a = p := Subtype.ext he
  exact he' ▸ ha

/-- Actual induced computation task on a locally generated relay subspace. -/
def inducedRelay (T : Task K F) (P : Submodule K F) (hP : T.LocallyGenerated P) : Task K P where
  A i := (T.A i).comap P.subtype
  U i := (T.U i).comap P.subtype
  side_le_signal i := Submodule.comap_mono (T.side_le_signal i)
  feasible i := by rw [T.induced_sides_span P hP]; exact le_top

theorem inducedRelay_spanning (T : Task K F) (P : Submodule K F) (hP : T.LocallyGenerated P) :
    (T.inducedRelay P hP).Spanning := T.induced_sides_span P hP

end UploadBroadcast.Task
