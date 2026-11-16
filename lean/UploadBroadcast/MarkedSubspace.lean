import UploadBroadcast.MarkedNilpotent

namespace UploadBroadcast.MarkedSubspace
open UploadBroadcast.MarkedNilpotent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma exists_functional (D : Submodule K V) (b : V) (hb : b ≠ 0) :
    ∃ φ : V →ₗ[K] K, φ b = 1 ∧ (b ∈ D ∨ ∀ x ∈ D, φ x = 0) := by
  classical
  by_cases h : b ∈ D
  · obtain ⟨φ,hφ,_⟩ := Submodule.exists_dual_map_eq_bot_of_nmem
      (p := (⊥ : Submodule K V)) (by simpa using hb) inferInstance
    refine ⟨(φ b)⁻¹ • φ,?_,Or.inl h⟩
    simp [LinearMap.smul_apply,smul_eq_mul,hφ]
  · obtain ⟨φ,hφ,hD⟩ := Submodule.exists_dual_map_eq_bot_of_nmem h inferInstance
    refine ⟨(φ b)⁻¹ • φ,?_,Or.inr ?_⟩
    · simp [LinearMap.smul_apply,smul_eq_mul,hφ]
    · intro x hx
      have hz : φ x ∈ D.map φ := ⟨x,hx,rfl⟩
      have he : φ x = 0 := by simpa [hD] using hz
      simp [LinearMap.smul_apply,he]

lemma pow_preserves (P : Module.End K V) (D : Submodule K V)
    (h : ∀ x ∈ D, P x ∈ D) (r : ℕ) {x : V} (hx : x ∈ D) : (P^r) x ∈ D := by
  induction r with
  | zero => exact hx
  | succ r ih => rw [pow_succ',Module.End.mul_apply]; exact h _ ih

/-- Marked indecomposability forces the entire nonzero marked kernel subspace
to be a single line, and the ambient nilpotent operator to be one chain. -/
theorem single_chain_and_marked_kernel [Finite K] [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) (D : Submodule K V)
    (hD : D ≠ ⊥) (hDN : D ≤ LinearMap.ker N)
    (hind : ∀ P : Module.End K V, Commute P N → (∀ x ∈ D, P x ∈ D) →
      (∀ x, P (P x) = P x) → P = 0 ∨ P = 1) :
    (∃ (n : ℕ) (v : V), N^(n+1) = 0 ∧ (N^n) v ≠ 0 ∧
      Submodule.span K (Set.range (fun i : Fin (n+1) => (N^i.val) v)) = ⊤) ∧
    LinearMap.ker N = D ∧ Module.finrank K D = 1 := by
  classical
  obtain ⟨l,hlD,hl⟩ : ∃ l : V, l ∈ D ∧ l ≠ 0 := by
    by_contra h
    push_neg at h
    apply hD
    apply le_antisymm _ bot_le
    intro x hx
    exact h x hx
  letI : Finite V := Module.finite_of_finite K
  letI : Finite (Module.End K V) := Finite.of_injective
    (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨n,v,hn,hv⟩ := exists_maximal_chain N hN l hl
  obtain ⟨φ,hφ,hmark⟩ := exists_functional D ((N^n) v) hv
  let P := chainMap N n v φ
  have hNb : N ((N^n) v) = 0 := by rw [← Module.End.mul_apply,← pow_succ',hn]; rfl
  have hPb : P ((N^n) v) = (N^n) v := by
    rw [chainMap_on_kernel N n v φ hNb,hφ,one_smul]
  have hpowb (r : ℕ) : (P^r) ((N^n) v) = (N^n) v := by
    induction r with
    | zero => rfl
    | succ r ih => rw [pow_succ',Module.End.mul_apply,ih,hPb]
  have hPD : ∀ x ∈ D, P x ∈ D := by
    intro x hx
    rw [chainMap_on_kernel N n v φ (hDN hx)]
    rcases hmark with hb | hz
    · exact D.smul_mem _ hb
    · rw [hz x hx,zero_smul]; exact D.zero_mem
  obtain ⟨r,hr,hid⟩ := FiniteMonoidPower.exists_pos_pow_add_eq P
  have hid' : ∀ x, (P^r) ((P^r) x) = (P^r) x := by
    intro x
    simpa only [pow_add,Module.End.mul_apply] using congrArg (fun f : Module.End K V => f x) hid
  have hpow : P^r = 1 := by
    obtain hz | ho := hind (P^r) ((chainMap_commutes N n v φ hn).pow_left r)
      (fun x hx => pow_preserves P D hPD r hx) hid'
    · have hh := hpowb r
      rw [hz] at hh
      exact False.elim (hv hh.symm)
    · exact ho
  have hbD : (N^n) v ∈ D := by
    rcases hmark with hb | hz
    · exact hb
    · have hzero : P l = 0 := by rw [chainMap_on_kernel N n v φ (hDN hlD),hz l hlD,zero_smul]
      have hzero' := pow_apply_eq_zero_of_apply_eq_zero P hzero hr
      rw [hpow] at hzero'
      exact False.elim (hl hzero')
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hker : LinearMap.ker N = Submodule.span K {(N^n) v} := by
    apply le_antisymm
    · intro x hx
      have hPx : P x ∈ Submodule.span K {(N^n) v} := by
        rw [chainMap_on_kernel N n v φ hx]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have he : (P^s) (P x) = x := by
        simpa only [pow_succ,Module.End.mul_apply,Module.End.one_apply] using
          congrArg (fun f : Module.End K V => f x) hpow
      rw [← he]
      apply pow_mem_line P ((N^n) v) _ s hPx
      rw [hPb]
      exact Submodule.mem_span_singleton_self _
    · exact Submodule.span_le.mpr (by simpa [LinearMap.mem_ker] using hNb)
  have hkerD : LinearMap.ker N = D := by
    apply le_antisymm _ hDN
    rw [hker]
    exact Submodule.span_le.mpr (by simpa using hbD)
  refine ⟨⟨n,v,hn,hv,eq_top_iff.mpr ?_⟩,hkerD,?_⟩
  · intro x _
    have he : P ((P^s) x) = x := by
      simpa only [pow_succ',Module.End.mul_apply,Module.End.one_apply] using
        congrArg (fun f : Module.End K V => f x) hpow
    rw [← he]
    exact chainMap_mem_span N n v φ _
  · rw [← hkerD,hker]
    exact finrank_span_singleton hv

end UploadBroadcast.MarkedSubspace
