import UploadBroadcast.ClassifiedComponentMenus
import UploadBroadcast.ResidualComponentAdditivity

namespace UploadBroadcast.ClassifiedComponentRanks
open Module Profile ResidualComponentAdditivity ClassifiedComponentMenus NonzeroDefectProfile
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem uploadValue_reindex (T : Task K V) (p : Equiv.Perm Three) :
    uploadValue (reindexTask p T)=uploadValue T := by
  have hs := Equiv.sum_comp p (fun i => (finrank K (T.A i) : ℝ))
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  change (finrank K (T.A (p 0)) : ℝ)+(finrank K (T.A (p 1))+finrank K (T.A (p 2)))=
    (finrank K (T.A 0) : ℝ)+(finrank K (T.A 1)+finrank K (T.A 2)) at hs
  unfold uploadValue
  change 2*(finrank K V : ℝ)-((finrank K (T.A (p 0)) : ℝ)+finrank K (T.A (p 1))+finrank K (T.A (p 2))) = _
  linarith only [hs]

theorem canonical_uploadValue (T : Task K V) (g : Family) (n : ℕ)
    (hn : Legal g n) (h : NonzeroFamilyRanks.Dimensions T g n) :
    uploadValue T=(relayRank g n : ℝ) := by
  have hc : 2*fullAmbient g n = fullSide g n 0+fullSide g n 1+fullSide g n 2+relayRank g n := by
    cases g <;> simp [Legal,fullAmbient,fullSide,relayRank,codimension] at hn ⊢ <;> omega
  have hr : 2*(fullAmbient g n : ℝ) = (fullSide g n 0 : ℝ)+fullSide g n 1+fullSide g n 2+relayRank g n := by
    exact_mod_cast hc
  unfold uploadValue
  rw [h.ambient,h.side 0,h.side 1,h.side 2]
  linarith only [hr]

theorem permuted_uploadValue (T : Task K V) (g : Family) (n : ℕ) (p : Fin 6)
    (hn : Legal g n)
    (h : NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm p) T) g n) :
    uploadValue T=(relayRank g n : ℝ) := by
  have hh := canonical_uploadValue (reindexTask (R2PermutedMenus.pathPerm p) T) g n hn h
  rw [uploadValue_reindex] at hh
  exact hh

variable {I : Type} [Fintype I] {F : I → Type}
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)] [∀ t, FiniteDimensional K (F t)]

theorem finite_product_uploadValue (T : (t : I) → Task K (F t))
    (g : I → Family) (n : I → ℕ) (p : I → Fin 6) (hn : ∀ t, Legal (g t) (n t))
    (h : ∀ t, NonzeroFamilyRanks.Dimensions (reindexTask (R2PermutedMenus.pathPerm (p t)) (T t)) (g t) (n t)) :
    uploadValue (FiniteRelayAssembly.task T)=((∑ t, relayRank (g t) (n t) : ℕ) : ℝ) := by
  rw [uploadValue_product,Nat.cast_sum]
  exact Finset.sum_congr rfl (fun t _ => permuted_uploadValue (T t) (g t) (n t) (p t) (hn t) (h t))

end UploadBroadcast.ClassifiedComponentRanks
