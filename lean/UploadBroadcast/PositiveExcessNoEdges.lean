import UploadBroadcast.EdgeExtraction
import UploadBroadcast.NonzeroDefectProfile
import UploadBroadcast.FiniteRelayAssembly

namespace UploadBroadcast.PositiveExcessNoEdges
open Module EdgeExtraction
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- No positive-excess indecomposable can contain a nonzero extractable
physical edge. This avoids assuming Krull–Schmidt uniqueness to protect menu
components when the zero-excess edge factors are extracted. -/
theorem multiplicity_eq_zero (T : Task K V)
    (hT : TaskDecomposition.Indecomposable (configuration T).spaces ⊤)
    (hpos : finrank K V < finrank K (T.A 0)+finrank K (T.A 1)+finrank K (T.A 2))
    (i j k : Three) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    multiplicity T i j k=0 := by
  obtain ⟨e⟩ := exists_extraction T i j k hij hik hjk
  have hs := TaskDecomposition.stable_projection_split (configuration T).spaces e.projection e.stable e.idempotent
  rw [e.ker_eq,e.range_eq] at hs
  have hW : e.W=⊥ := by
    rcases hT.2 e.Q e.W hs with hQ | hW
    · have htop : e.W=⊤ := by simpa only [hQ,bot_sup_eq] using hs.sup_eq
      obtain ⟨hak,_,_,hai,_,haj⟩ := e.block.signature
      rw [htop,inf_top_eq] at hak hai haj
      have he := NonzeroDefectProfile.sum_three_perm (fun a => finrank K (T.A a)) i j k hij hik hjk
      dsimp only at he
      rw [hai,haj,hak,finrank_bot,finrank_top,zero_add,zero_add] at he
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at he
      change finrank K (T.A 0)+(finrank K (T.A 1)+finrank K (T.A 2))=finrank K V at he
      omega
    · exact hW
  rw [← e.dimension,hW,finrank_bot]

variable {I : Type*} [Fintype I] {F : I → Type*}
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]

/-- Edge multiplicities add on actual finite product tasks. -/
theorem multiplicity_finite_task (T : (t : I) → Task K (F t)) (i j k : Three) :
    multiplicity (FiniteRelayAssembly.task T) i j k=∑ t, multiplicity (T t) i j k := by
  have hN : (FiniteRelayAssembly.task T).A k ⊓ (FiniteRelayAssembly.task T).U j =
      FiniteRelayAssembly.space (fun t => (T t).A k ⊓ (T t).U j) :=
    (FiniteRelayAssembly.space_inf _ _).symm
  have hB : blocked (FiniteRelayAssembly.task T) i j =
      FiniteRelayAssembly.space (fun t => blocked (T t) i j) := by
    change FiniteRelayAssembly.space (fun t => (T t).A j) ⊔
      (FiniteRelayAssembly.space (fun t => (T t).U i) ⊓ FiniteRelayAssembly.space (fun t => (T t).U j)) = _
    rw [← FiniteRelayAssembly.space_inf]
    exact (FiniteRelayAssembly.space_sup _ _).symm
  have hD : ((FiniteRelayAssembly.task T).A k ⊓ (FiniteRelayAssembly.task T).U j) ⊓
      blocked (FiniteRelayAssembly.task T) i j = FiniteRelayAssembly.space
      (fun t => ((T t).A k ⊓ (T t).U j) ⊓ blocked (T t) i j) := by
    rw [hN,hB]
    exact (FiniteRelayAssembly.space_inf _ _).symm
  unfold EdgeExtraction.multiplicity
  rw [hD,hN,FiniteRelayAssembly.finrank_space,FiniteRelayAssembly.finrank_space]
  exact (Finset.sum_tsub_distrib Finset.univ (fun t _ => Submodule.finrank_mono
    (show ((T t).A k ⊓ (T t).U j) ⊓ blocked (T t) i j ≤
      (T t).A k ⊓ (T t).U j from inf_le_left))).symm

theorem positive_finite_task_has_no_edges (T : (t : I) → Task K (F t))
    (hT : ∀ t, TaskDecomposition.Indecomposable (configuration (T t)).spaces ⊤)
    (hpos : ∀ t, finrank K (F t) < finrank K ((T t).A 0)+finrank K ((T t).A 1)+finrank K ((T t).A 2))
    (i j k : Three) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    multiplicity (FiniteRelayAssembly.task T) i j k=0 := by
  rw [multiplicity_finite_task]
  simp only [multiplicity_eq_zero _ (hT _) (hpos _) i j k hij hik hjk,Finset.sum_const_zero]

end UploadBroadcast.PositiveExcessNoEdges
