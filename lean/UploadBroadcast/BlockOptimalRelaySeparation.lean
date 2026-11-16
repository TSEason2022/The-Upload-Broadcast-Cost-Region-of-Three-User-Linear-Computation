import UploadBroadcast.OptimalRelaySeparation
import UploadBroadcast.BlockFlatten

/-! Minimum residual relay independence at every positive blocklength. -/
namespace UploadBroadcast.OptimalRelaySeparation
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Pairwise disjointness of residual sides survives arbitrary blocking. -/
theorem block_disjoint (A B : Submodule K F) (hAB : Disjoint A B) (L : ℕ) :
    Disjoint (blockSubmodule L A) (blockSubmodule L B) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  funext j
  exact Submodule.disjoint_def.mp hAB (x j) (hx j trivial) (hy j trivial)

/-- Source lemma `optimal-residual-sides` at its full blocklength generality.
The minimum is the operational optimum of the original task. An alleged
nonzero tripod constructs a two-instance code on the blocked task, which
flattens to an actual 2L-instance original-field code and contradicts that
operational infimum. -/
theorem optimal_block_residual_sides [Finite K] [FiniteDimensional K F]
    (T : Task K F) (L : ℕ) (hL : 0 < L)
    (P : Submodule K (Fin L → F))
    (hlocal : (T.blockPower L).LocallyGenerated P)
    (hfeas : (T.blockPower L).RelayFeasible P)
    (hAB : Disjoint (T.A 0) (T.A 1)) (hAC : Disjoint (T.A 0) (T.A 2))
    (hBC : Disjoint (T.A 1) (T.A 2))
    (hmin : (finrank K P : ℝ) = L * T.uploadOptimum) :
    iSupIndep (fun i => ((T.blockPower L).A i).comap P.subtype) ∧
      (⨆ i, ((T.blockPower L).A i).comap P.subtype) = ⊤ := by
  have hAB' := induced_disjoint _ _ P (block_disjoint _ _ hAB L)
  have hAC' := induced_disjoint _ _ P (block_disjoint _ _ hAC L)
  have hBC' := induced_disjoint _ _ P (block_disjoint _ _ hBC L)
  have hc := induced_separation_of_two_code_lower (T.blockPower L) P hlocal hfeas
    hAB' hAC' hBC' (by
      intro m s c
      have h := c.flatten.uploadOptimum_le (Nat.mul_pos hL (by decide))
      rw [c.flatten_costs.1] at h
      have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have hh := (le_div_iff₀ hL').mp h
      rw [hmin]
      simpa only [mul_comm] using hh)
  exact ⟨independent_of_separation _ hAB' (disjoint_iff.mpr hc),
    (T.blockPower L).induced_sides_span P hlocal⟩

/-- Full arbitrary-block direct-sum conclusion in the original blocked
ambient, matching P = direct-sum_i (P ∩ A_i^{⊕L}). -/
theorem optimal_block_residual_sides_ambient [Finite K] [FiniteDimensional K F]
    (T : Task K F) (L : ℕ) (hL : 0 < L)
    (P : Submodule K (Fin L → F))
    (hlocal : (T.blockPower L).LocallyGenerated P)
    (hfeas : (T.blockPower L).RelayFeasible P)
    (hAB : Disjoint (T.A 0) (T.A 1)) (hAC : Disjoint (T.A 0) (T.A 2))
    (hBC : Disjoint (T.A 1) (T.A 2))
    (hmin : (finrank K P : ℝ) = L * T.uploadOptimum) :
    iSupIndep (fun i => P ⊓ blockSubmodule L (T.A i)) ∧
      P = ⨆ i, P ⊓ blockSubmodule L (T.A i) := by
  obtain ⟨hi,_⟩ := optimal_block_residual_sides T L hL P hlocal hfeas hAB hAC hBC hmin
  have hc : ((T.blockPower L).A 2).comap P.subtype ⊓
      (((T.blockPower L).A 0).comap P.subtype ⊔ ((T.blockPower L).A 1).comap P.subtype) = ⊥ := by
    have h := hi 2
    have hd : Disjoint (((T.blockPower L).A 2).comap P.subtype)
        (((T.blockPower L).A 0).comap P.subtype ⊔ ((T.blockPower L).A 1).comap P.subtype) := by
      simpa [Profile.three_iSup] using h
    exact hd.eq_bot
  have hm := congrArg (Submodule.map P.subtype) hc
  rw [Submodule.map_inf _ P.subtype_injective,Submodule.map_sup,
    Submodule.map_bot] at hm
  simp only [Submodule.map_comap_subtype] at hm
  exact ⟨independent_of_separation _
    ((block_disjoint _ _ hAB L).mono inf_le_right inf_le_right) (disjoint_iff.mpr hm),hlocal⟩

end UploadBroadcast.OptimalRelaySeparation
