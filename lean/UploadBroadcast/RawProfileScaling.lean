import UploadBroadcast.AllocationProfile

namespace UploadBroadcast.Allocation
variable {K F G : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- First-order raw profile entries are integral. -/
theorem rawFirstEntry_integral (A U : Fin 3 → Submodule K F) (i j k : Three) :
    ∃ z : ℤ, rawFirstEntry A U i j k = z := by
  refine ⟨(demandRank A U 0 : ℤ)+demandRank A U 1+demandRank A U 2-
    condRank (U i ⊓ U j) (A j)-condRank (U k ⊓ (U i ⊔ U j)) (A k), ?_⟩
  simp [rawFirstEntry]

theorem rawSecondEntry_halfInteger (A U : Fin 3 → Submodule K F) (i j k ell : Three) :
    Profile.HalfInteger (rawSecondEntry A U i j k ell) := by
  refine ⟨2*((demandRank A U 0 : ℤ)+demandRank A U 1+demandRank A U 2)-
    ((condRank (U 0 ⊓ U 1 ⊓ U 2) (A ell) : ℤ)+
      condRank ((U i ⊓ U j) ⊔ (U i ⊓ U k)) (A i)+
      condRank (U j ⊓ (U i ⊔ U k)) (A j)+
      condRank (U k ⊓ (U i ⊔ U j)) (A k)), ?_⟩
  simp only [rawSecondEntry, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Int.cast_add, Int.cast_natCast]
  ring

theorem rawEntry_halfInteger (A U : Fin 3 → Submodule K F) (r : Profile.Index) :
    Profile.HalfInteger (rawEntry A U r) := by
  cases r with
  | inl r =>
    obtain ⟨z,hz⟩ := rawFirstEntry_integral A U (Profile.firstOrder r).1
      (Profile.firstOrder r).2.1 (Profile.firstOrder r).2.2
    refine ⟨2*z, ?_⟩
    change rawFirstEntry A U _ _ _ = _
    rw [hz]
    push_cast
    ring
  | inr r => exact rawSecondEntry_halfInteger A U _ _ _ _

/-- Half-integrality of the exact raw-subspace LP/profile value. -/
theorem rawRankBound_halfInteger (A U : Fin 3 → Submodule K F) :
    Profile.HalfInteger (rawRankBound A U) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    (by simp : (Finset.univ : Finset Profile.Index).Nonempty) (rawEntry A U)
  change Profile.HalfInteger (Finset.univ.sup' _ (rawEntry A U))
  rw [hi]
  exact rawEntry_halfInteger A U i

theorem rawFirstEntry_prod (A U : Fin 3 → Submodule K F)
    (B V : Fin 3 → Submodule K G) (i j k : Three) :
    rawFirstEntry (fun i => (A i).prod (B i)) (fun i => (U i).prod (V i)) i j k =
      rawFirstEntry A U i j k + rawFirstEntry B V i j k := by
  simp only [rawFirstEntry, demandRank, Submodule.prod_inf_prod,
    Submodule.prod_sup_prod, Profile.condRank_prod, Nat.cast_add]
  ring

theorem rawSecondEntry_prod (A U : Fin 3 → Submodule K F)
    (B V : Fin 3 → Submodule K G) (i j k ell : Three) :
    rawSecondEntry (fun i => (A i).prod (B i)) (fun i => (U i).prod (V i)) i j k ell =
      rawSecondEntry A U i j k ell + rawSecondEntry B V i j k ell := by
  simp only [rawSecondEntry, demandRank, Submodule.prod_inf_prod,
    Submodule.prod_sup_prod, Profile.condRank_prod, Nat.cast_add]
  ring

theorem rawEntry_prod (A U : Fin 3 → Submodule K F)
    (B V : Fin 3 → Submodule K G) (r : Profile.Index) :
    rawEntry (fun i => (A i).prod (B i)) (fun i => (U i).prod (V i)) r =
      rawEntry A U r + rawEntry B V r := by
  cases r with
  | inl r => exact rawFirstEntry_prod A U B V _ _ _
  | inr r => exact rawSecondEntry_prod A U B V _ _ _ _

theorem rawEntry_le_rankBound (A U : Fin 3 → Submodule K F) (r : Profile.Index) :
    rawEntry A U r ≤ rawRankBound A U :=
  Finset.le_sup' (rawEntry A U) (Finset.mem_univ r)

/-- Two identical raw instances scale the rank maximum exactly, with no
upload-feasibility assumption. This is a rank statement, not code transport. -/
theorem rawRankBound_double (A U : Fin 3 → Submodule K F) :
    rawRankBound (fun i => (A i).prod (A i)) (fun i => (U i).prod (U i)) =
      2 * rawRankBound A U := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro r _
    rw [rawEntry_prod]
    have h := rawEntry_le_rankBound A U r
    linarith
  · obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      (by simp : (Finset.univ : Finset Profile.Index).Nonempty) (rawEntry A U)
    have h := rawEntry_le_rankBound (fun i => (A i).prod (A i))
      (fun i => (U i).prod (U i)) r
    rw [rawEntry_prod] at h
    change rawRankBound A U = rawEntry A U r at hr
    rw [hr]
    linarith

end UploadBroadcast.Allocation
