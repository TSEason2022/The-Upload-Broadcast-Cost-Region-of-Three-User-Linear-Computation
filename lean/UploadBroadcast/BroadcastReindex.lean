import UploadBroadcast.ScalarPaperEndpoints

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

def ScalarBroadcastCode.reindex {A U : Three → Submodule K F} {n : ℕ}
    (c : ScalarBroadcastCode A U n) (p : Equiv.Perm Three) :
    ScalarBroadcastCode (A ∘ p) (U ∘ p) n where
  encode := c.encode
  decode i := c.decode (p i)
  zero_error x i := c.zero_error x (p i)

def BlockBroadcastCode.reindex {A U : Three → Submodule K F} {L : ℕ} {S : Type*}
    (c : BlockBroadcastCode A U L S) (p : Equiv.Perm Three) :
    BlockBroadcastCode (A ∘ p) (U ∘ p) L S where
  encode := c.encode
  decode i := c.decode (p i)
  zero_error x i := c.zero_error x (p i)

theorem broadcastCosts_reindex_subset (A U : Three → Submodule K F) (p : Equiv.Perm Three) :
    broadcastCosts A U ⊆ broadcastCosts (A ∘ p) (U ∘ p) := by
  rintro r ⟨L,n,c,hL,hc⟩
  exact ⟨L,n,c.reindex p,hL,hc⟩

theorem broadcastCosts_reindex (A U : Three → Submodule K F) (p : Equiv.Perm Three) :
    broadcastCosts (A ∘ p) (U ∘ p) = broadcastCosts A U := by
  apply Set.Subset.antisymm
  · have h := broadcastCosts_reindex_subset (A ∘ p) (U ∘ p) p.symm
    have hA : (A ∘ p) ∘ p.symm = A := by funext i; exact congrArg A (p.apply_symm_apply i)
    have hU : (U ∘ p) ∘ p.symm = U := by funext i; exact congrArg U (p.apply_symm_apply i)
    rw [hA,hU] at h
    exact h
  · exact broadcastCosts_reindex_subset A U p

theorem broadcastOptimum_reindex (A U : Three → Submodule K F) (p : Equiv.Perm Three) :
    broadcastOptimum (A ∘ p) (U ∘ p) = broadcastOptimum A U := by
  unfold broadcastOptimum
  rw [broadcastCosts_reindex]

/-- Binary scalar endpoint with the manuscript's arbitrary user permutation. -/
theorem binary_at_operational_ceiling_permuted [Fintype K] [FiniteDimensional K F]
    (hK : Fintype.card K = 2) (A U : Three → Submodule K F)
    (hAU : ∀ i, A i ≤ U i) (hspan : (⨆ i, A i) = ⊤)
    (p : Equiv.Perm Three) (hsep : A (p 0) ⊓ (A (p 1) ⊔ A (p 2)) = ⊥) :
    ∃ (n : ℕ) (c : ScalarBroadcastCode A U n),
      (n : ℤ) = ⌈broadcastOptimum A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) = (n : ℝ) := by
  have hs : (⨆ i, (A ∘ p) i) = ⊤ := by
    change (⨆ i, A (p i)) = ⊤
    rw [Equiv.iSup_comp, hspan]
  obtain ⟨n,c,hn,hc⟩ := binary_at_operational_ceiling hK (A ∘ p) (U ∘ p)
    (fun i => hAU (p i)) hs hsep
  rw [broadcastOptimum_reindex] at hn
  have hA : (A ∘ p) ∘ p.symm = A := by funext i; exact congrArg A (p.apply_symm_apply i)
  have hU : (U ∘ p) ∘ p.symm = U := by funext i; exact congrArg U (p.apply_symm_apply i)
  have h : ∃ (n : ℕ) (d : ScalarBroadcastCode ((A ∘ p) ∘ p.symm)
      ((U ∘ p) ∘ p.symm) n), (n : ℤ) = ⌈broadcastOptimum A U⌉ ∧
      Real.logb (Nat.card K) (Nat.card (Set.range d.encode)) = (n : ℝ) :=
    ⟨n,c.reindex p.symm,hn,hc⟩
  rw [hA,hU] at h
  exact h

end UploadBroadcast
