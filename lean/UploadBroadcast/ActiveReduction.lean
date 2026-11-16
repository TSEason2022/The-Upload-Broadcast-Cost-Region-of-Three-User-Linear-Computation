import UploadBroadcast.LinearAlgebra
import UploadBroadcast.PassiveCode

/-!
# Concrete active-reduction operations
The algebraic coordinate operations in Appendix A are proved here over an
arbitrary field. This file does not postulate a three-subspace normal form.
-/
namespace UploadBroadcast
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The coordinate map `I-N` with inverse `I+N`, when `N²=0`. -/
def squareZeroShear (N : F →ₗ[K] F) (hN : N.comp N = 0) : F ≃ₗ[K] F where
  toLinearMap := LinearMap.id - N
  invFun x := x + N x
  left_inv x := by
    have hz : N (N x) = 0 := LinearMap.congr_fun hN x
    change (x - N x) + N (x - N x) = x
    simp only [map_sub, hz]
    abel
  right_inv x := by
    have hz : N (N x) = 0 := LinearMap.congr_fun hN x
    change (x + N x) - N (x + N x) = x
    simp only [map_add, hz]
    abel

@[simp] theorem squareZeroShear_apply (N : F →ₗ[K] F) (hN : N.comp N = 0) (x : F) :
    squareZeroShear N hN x = x - N x := rfl

/-- Every side subspace stable under N is preserved exactly, not merely
mapped into itself, by the shear. -/
theorem squareZeroShear_preserves (N : F →ₗ[K] F) (hN : N.comp N = 0)
    (A : Submodule K F) (hA : ∀ x ∈ A, N x ∈ A) :
    A.map (squareZeroShear N hN).toLinearMap = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact A.sub_mem hy (hA y hy)
  · intro hx
    refine ⟨x + N x, A.add_mem hx (hA x hx), ?_⟩
    exact (squareZeroShear N hN).apply_symm_apply x

/-- The pair-block corrections annihilate one another, so they can be
performed simultaneously in all three users' quotient coordinates. -/
theorem sum_square_zero {ι : Type*} [Fintype ι]
    (N : ι → F →ₗ[K] F) (hN : ∀ i j, (N i).comp (N j) = 0) :
    (∑ i, N i).comp (∑ i, N i) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  have hz : ∀ i j, N i (N j x) = 0 := fun i j => LinearMap.congr_fun (hN i j) x
  simp [hz]

/-- Side-information preservation of the simultaneous active-pair shear. -/
theorem simultaneous_shear_preserves {ι : Type*} [Fintype ι]
    (N : ι → F →ₗ[K] F) (hN : ∀ i j, (N i).comp (N j) = 0)
    (A : Submodule K F) (hA : ∀ i x, x ∈ A → N i x ∈ A) :
    A.map (squareZeroShear (∑ i, N i) (sum_square_zero N hN)).toLinearMap = A := by
  apply squareZeroShear_preserves
  intro x hx
  simp only [LinearMap.sum_apply]
  exact A.sum_mem fun i _ => hA i x hx

/-- The actual cancellation on a graph: a retained vector plus its passive
correction is sent back to the retained vector. -/
theorem shear_cancels_graph (N : F →ₗ[K] F) (hN : N.comp N = 0) (x : F) :
    squareZeroShear N hN (x + N x) = x := by
  have hz : N (N x) = 0 := LinearMap.congr_fun hN x
  simp [hz]

/-- Projecting onto any passive complement annihilating the intrinsic
obstruction gives an actual canceling map on private coordinates. This is
the factorization step of `lem:active-empty-row`. -/
theorem cancel_passive_projection {Z : Type*} [AddCommGroup Z] [Module K Z]
    (B : F →ₗ[K] V) (G : F →ₗ[K] W) (π : W →ₗ[K] Z)
    (hπ : ∀ x ∈ LinearMap.ker B, π (G x) = 0) :
    ∃ h : V →ₗ[K] Z, π.comp G + h.comp B = 0 := by
  have hk : LinearMap.ker B ≤ LinearMap.ker (π.comp G) := by
    intro x hx
    exact hπ x hx
  obtain ⟨h, hh⟩ := factors_through_of_ker_le B (π.comp G) hk
  refine ⟨-h, ?_⟩
  rw [LinearMap.neg_comp, hh]
  exact add_neg_cancel _

/-- The passive projection is genuinely eliminated when it is idempotent,
as are projections onto a chosen complement. -/
theorem cancel_idempotent_projection
    (B : F →ₗ[K] V) (G : F →ₗ[K] W) (P : W →ₗ[K] W)
    (hPP : P.comp P = P)
    (hP : ∀ x ∈ LinearMap.ker B, P (G x) = 0) :
    ∃ h : V →ₗ[K] W, ∀ x, G x + h (B x) ∈ LinearMap.ker P := by
  obtain ⟨h, hh⟩ := factors_through_of_ker_le B (P.comp G) (by
    intro x hx
    exact hP x hx)
  refine ⟨-P.comp h, ?_⟩
  intro x
  change P (G x + -(P (h (B x)))) = 0
  rw [map_add, map_neg]
  have he := LinearMap.congr_fun hh x
  have hp := LinearMap.congr_fun hPP (h (B x))
  change h (B x) = P (G x) at he
  change P (P (h (B x))) = P (h (B x)) at hp
  rw [hp, he]
  have hp' := LinearMap.congr_fun hPP (G x)
  change P (P (G x)) = P (G x) at hp'
  rw [hp', add_neg_cancel]

/-- The graph splitting used for each active pair. `A` is the intersection
with the pair block; `Q` is the projected demand, not its intersection
with the tripod space. A complement P gives a passive-valued correction. -/
theorem active_pair_graph (D : Submodule K (F × V))
    (A P : Submodule K F)
    (hA : A = D.comap (LinearMap.inl K F V)) (hAP : IsCompl P A) :
    ∃ ψ : V →ₗ[K] F, LinearMap.range ψ ≤ P ∧
      ∀ k v, (k, v) ∈ D ↔
        k - ψ v ∈ A ∧ v ∈ D.map (LinearMap.snd K F V) := by
  let π := P.linearProjOfIsCompl A hAP
  let B := (LinearMap.snd K F V).comp D.subtype
  let G := π.comp ((LinearMap.fst K F V).comp D.subtype)
  have hk : LinearMap.ker B ≤ LinearMap.ker G := by
    intro w hw
    have hw0 : (w : F × V).2 = 0 := hw
    have ha : (w : F × V).1 ∈ A := by
      rw [hA]
      change ((w : F × V).1, 0) ∈ D
      simpa only [← hw0] using w.property
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hAP).mpr ha
  obtain ⟨h, hh⟩ := factors_through_of_ker_le B G hk
  let ψ := P.subtype.comp h
  have hforward : ∀ k v, (k, v) ∈ D → k - ψ v ∈ A := by
    intro k v hkv
    have he := LinearMap.congr_fun hh ⟨(k, v), hkv⟩
    change h v = π k at he
    apply (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hAP).mp
    change π (k - (h v : F)) = 0
    rw [map_sub, Submodule.linearProjOfIsCompl_apply_left, he, sub_self]
  refine ⟨ψ, ?_, ?_⟩
  · rintro x ⟨v, rfl⟩
    exact (h v).property
  · intro k v
    constructor
    · intro hkv
      exact ⟨hforward k v hkv, ⟨(k, v), hkv, rfl⟩⟩
    · rintro ⟨hk, w, hw, hwv⟩
      change w.2 = v at hwv
      have hw' : (w.1, v) ∈ D := by simpa only [← hwv] using hw
      have hka : k - w.1 ∈ A := by
        have ha := A.sub_mem hk (hforward w.1 v hw')
        convert ha using 1; abel
      have hd : (k - w.1, 0) ∈ D := by
        rw [hA] at hka
        exact hka
      have hs := D.add_mem hd hw'
      convert hs using 1; simp

/-- Explicit quotient-coordinate shear for the active-pair graph. -/
def pairShear (ψ : V →ₗ[K] F) : (F × V) ≃ₗ[K] (F × V) where
  toFun z := (z.1 - ψ z.2, z.2)
  invFun z := (z.1 + ψ z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by
    apply Prod.ext
    · change (x.1 + y.1) - ψ (x.2 + y.2) = (x.1 - ψ x.2) + (y.1 - ψ y.2)
      rw [map_add]
      abel
    · rfl
  map_smul' c x := by ext <;> simp [smul_sub]

/-- Active-pair graph separation as an equality of actual transformed
subspaces. This is the quotient-space algebra of `prop:active-pair`. -/
theorem active_pair_separation (D : Submodule K (F × V))
    (A P : Submodule K F)
    (hA : A = D.comap (LinearMap.inl K F V)) (hAP : IsCompl P A) :
    ∃ ψ : V →ₗ[K] F, LinearMap.range ψ ≤ P ∧
      D.map (pairShear ψ).toLinearMap = A.prod (D.map (LinearMap.snd K F V)) := by
  obtain ⟨ψ, hψ, hmem⟩ := active_pair_graph D A P hA hAP
  refine ⟨ψ, hψ, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hmem w.1 w.2).mp hw
  · intro hz
    refine ⟨(z.1 + ψ z.2, z.2), ?_, ?_⟩
    · apply (hmem _ _).mpr
      simpa using hz
    · ext <;> simp [pairShear]

/-- Pairwise corrections have square-zero mixed products whenever their
ranges lie in blocks annihilated by every correction. -/
theorem corrections_annihilate {ι : Type*} (N : ι → F →ₗ[K] F)
    (P : ι → Submodule K F) (hr : ∀ i, LinearMap.range (N i) ≤ P i)
    (hz : ∀ i j x, x ∈ P j → N i x = 0) :
    ∀ i j, (N i).comp (N j) = 0 := by
  intro i j
  ext x
  exact hz i j (N j x) (hr j ⟨x, rfl⟩)

/-- Any linear change preserving the two axis sides and the r-v side has
one common row-coordinate map on both tripod copies. This proves the
rigidity assertion used in coordinate-parameter invariance. -/
theorem tripod_coordinate_rigidity (f : (F × F) →ₗ[K] (V × V))
    (hv : ∀ x, (f (x, 0)).2 = 0)
    (hr : ∀ x, (f (0, x)).1 = 0)
    (hd : ∀ x, (f (-x, x)).1 + (f (-x, x)).2 = 0) :
    ∃ h : F →ₗ[K] V, ∀ v r, f (v, r) = (h v, h r) := by
  let a := (LinearMap.fst K V V).comp (f.comp (LinearMap.inl K F F))
  let b := (LinearMap.snd K V V).comp (f.comp (LinearMap.inr K F F))
  have hab : ∀ x, a x = b x := by
    intro x
    have hm := hd x
    have he : f (-x, x) = -(f (x, 0)) + f (0, x) := by
      rw [← map_neg, ← map_add]
      congr 1; simp
    rw [he] at hm
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hv, hr,
      neg_zero, zero_add, add_zero] at hm
    change -(a x) + b x = 0 at hm
    exact neg_add_eq_zero.mp hm
  refine ⟨a, ?_⟩
  intro v r
  have he : f (v, r) = f (v, 0) + f (0, r) := by
    rw [← map_add]
    congr 1; simp
  rw [he]
  apply Prod.ext
  · change (f (v, 0)).1 + (f (0, r)).1 = a v
    simp only [hr, add_zero]
    rfl
  · change (f (v, 0)).2 + (f (0, r)).2 = a r
    simp only [hv, zero_add]
    exact (hab r).symm

/-- Graph-data map `phi_i`: the pure-demand space is the INTERSECTION
with the tripod summand (represented by comap along inr), not the
projection of the demand space. The induced value modulo that space is
independent of the chosen tripod component. -/
theorem graph_data_map (Q : Submodule K (F × V)) :
    ∃ φ : F →ₗ[K] (V ⧸ Q.comap (LinearMap.inr K F V)),
      ∀ p t, (p, t) ∈ Q → φ p =
        (Q.comap (LinearMap.inr K F V)).mkQ t := by
  let D := Q.comap (LinearMap.inr K F V)
  let B := (LinearMap.fst K F V).comp Q.subtype
  let G := D.mkQ.comp ((LinearMap.snd K F V).comp Q.subtype)
  have hk : LinearMap.ker B ≤ LinearMap.ker G := by
    intro z hz
    have hp : (z : F × V).1 = 0 := hz
    change D.mkQ (z : F × V).2 = 0
    apply (Submodule.Quotient.mk_eq_zero D).mpr
    change (0, (z : F × V).2) ∈ Q
    simpa only [← hp] using z.property
  obtain ⟨φ, hφ⟩ := factors_through_of_ker_le B G hk
  refine ⟨φ, ?_⟩
  intro p t hpt
  exact LinearMap.congr_fun hφ ⟨(p, t), hpt⟩

/-- The obstruction map itself, not just its rank, is unchanged by every
private-lift gauge correction. -/
theorem obstruction_gauge_eq (B : F →ₗ[K] V) (G : F →ₗ[K] W)
    (h : V →ₗ[K] W) :
    (G + h.comp B).comp (LinearMap.ker B).subtype =
      G.comp (LinearMap.ker B).subtype := by
  ext x
  exact gauge_invariance B G h x x.property

theorem mixed_rank_gauge_invariant (B : F →ₗ[K] V) (G : F →ₗ[K] W)
    (h : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range
      ((G + h.comp B).comp (LinearMap.ker B).subtype)) =
    Module.finrank K (LinearMap.range (G.comp (LinearMap.ker B).subtype)) := by
  rw [obstruction_gauge_eq]

/-- Common row-basis changes preserve the common pure-demand dimension. -/
theorem common_rank_basis_invariant (e : F ≃ₗ[K] V)
    (D₁ D₂ D₃ : Submodule K F) :
    Module.finrank K ↥(D₁.map e.toLinearMap ⊓ D₂.map e.toLinearMap ⊓ D₃.map e.toLinearMap) =
      Module.finrank K ↥(D₁ ⊓ D₂ ⊓ D₃) := by
  rw [← Submodule.map_inf e.toLinearMap e.injective, ← Submodule.map_inf e.toLinearMap e.injective]
  exact e.finrank_map_eq _

/-- The signs in B follow from quotient bases r,v,v for the three
tripod sides v,r,r-v. Contributions from private lift changes sum to hB. -/
theorem private_gauge_signs {P₁ P₂ P₃ : Type*}
    [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
    [AddCommGroup P₃] [Module K P₃]
    (h₁ : P₁ →ₗ[K] W) (h₂ : P₂ →ₗ[K] W) (h₃ : P₃ →ₗ[K] W)
    (p₂₁ p₃₁ : P₁) (p₁₂ p₃₂ : P₂) (p₁₃ p₂₃ : P₃) :
    (h₂ p₁₂ + h₃ p₁₃) + (h₁ p₂₁ - h₃ p₂₃) +
      (h₁ p₃₁ + h₂ p₃₂) =
    h₁ (p₂₁ + p₃₁) + h₂ (p₁₂ + p₃₂) + h₃ (p₁₃ - p₂₃) := by
  simp only [map_add, map_sub]
  abel

end UploadBroadcast
