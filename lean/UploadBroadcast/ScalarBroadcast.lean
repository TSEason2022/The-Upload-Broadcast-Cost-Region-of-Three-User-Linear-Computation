import UploadBroadcast.LinearAlgebra
import UploadBroadcast.ObservationRank
import UploadBroadcast.LinearCosts
import UploadBroadcast.Coordination

/-! Operational scalar broadcast constructors for arbitrary side and signal
subspaces. No upload-feasibility assumption is imposed. -/
namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Evaluate the source against a finite list of broadcast coefficients. -/
def coefficientBroadcast {n : ℕ} (v : Fin n → F) :
    (F →ₗ[K] K) →ₗ[K] (Fin n → K) where
  toFun x j := x (v j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual linear scalar encoder and decoders, over the original field. -/
structure ScalarBroadcastCode (A U : Fin 3 → Submodule K F) (n : ℕ) where
  encode : (F →ₗ[K] K) →ₗ[K] (Fin n → K)
  decode : ∀ i, ((Fin n → K) × (A i →ₗ[K] K)) →ₗ[K] (U i →ₗ[K] K)
  zero_error : ∀ x i, decode i (encode x, dualObserve (A i) x) = dualObserve (U i) x

/-- A spanning coefficient list supplies linear decoders, not merely fiber
conditions or a postulated code. -/
theorem scalarBroadcastCode_of_span {n : ℕ} (A U : Fin 3 → Submodule K F)
    (v : Fin n → F)
    (hspan : ∀ i, U i ≤ A i ⊔ Submodule.span K (Set.range v)) :
    Nonempty (ScalarBroadcastCode A U n) := by
  have hk (i : Fin 3) :
      LinearMap.ker ((coefficientBroadcast v).prod (dualObserve (A i))) ≤
        LinearMap.ker (dualObserve (U i)) := by
    intro x hx
    have he : coefficientBroadcast v x = 0 ∧ dualObserve (A i) x = 0 := by
      change (coefficientBroadcast v x, dualObserve (A i) x) = (0,0) at hx
      exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    have hv : Submodule.span K (Set.range v) ≤ LinearMap.ker x := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact congrFun he.1 j
    apply LinearMap.mem_ker.mpr
    ext u
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (hspan i u.property)
    have ha0 := LinearMap.congr_fun he.2 ⟨a,ha⟩
    have hb0 := hv hb
    change x (u:F) = 0
    rw [← hab, map_add]
    exact (congrArg₂ (· + ·) ha0 hb0).trans (zero_add 0)
  choose d hd using fun i => factors_through_of_ker_le
    ((coefficientBroadcast v).prod (dualObserve (A i))) (dualObserve (U i)) (hk i)
  exact ⟨⟨coefficientBroadcast v, d, fun x i => LinearMap.congr_fun (hd i) x⟩⟩

/-- Exact attained-alphabet cost and its nominal scalar-length upper bound. -/
theorem scalarBroadcastCode_cost_le [Finite K] [FiniteDimensional K F]
    {A U : Fin 3 → Submodule K F} {n : ℕ} (c : ScalarBroadcastCode A U n) :
    Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) ≤ n := by
  rw [linear_alphabet_log]
  exact_mod_cast (LinearMap.range c.encode).finrank_le.trans_eq (by simp)

/-- The complete aligned relation space. -/
def alignedRelation (U₀ U₁ U₂ : Submodule K F) : Submodule K (F × F × F) where
  carrier := {h | h.1 ∈ U₀ ∧ h.2.1 ∈ U₁ ∧ h.2.2 ∈ U₂ ∧ h.1 + h.2.1 = h.2.2}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha₀,ha₁,ha₂,ha⟩ ⟨hb₀,hb₁,hb₂,hb⟩
    exact ⟨U₀.add_mem ha₀ hb₀, U₁.add_mem ha₁ hb₁, U₂.add_mem ha₂ hb₂, by
      change (a.1+b.1)+(a.2.1+b.2.1)=a.2.2+b.2.2
      rw [← ha, ← hb]; abel⟩
  smul_mem' := by
    rintro c a ⟨ha₀,ha₁,ha₂,ha⟩
    exact ⟨U₀.smul_mem c ha₀, U₁.smul_mem c ha₁, U₂.smul_mem c ha₂,
      by change c • a.1 + c • a.2.1 = c • a.2.2; rw [← smul_add, ha]⟩

/-- Each enlarged first-user coefficient lifts to a full aligned relation. -/
theorem alignedRelation_lift_first (U₀ U₁ U₂ : Submodule K F) (x : F)
    (hx : x ∈ U₀ ⊓ (U₁ ⊔ U₂)) :
    ∃ h : alignedRelation U₀ U₁ U₂, (h:F × F × F).1 = x := by
  obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp hx.2
  exact ⟨⟨(x,-b,c),hx.1,U₁.neg_mem hb,hc,by change x + -b = c; rw [← hbc]; abel⟩,rfl⟩

/-- Each enlarged second-user coefficient lifts to a full aligned relation. -/
theorem alignedRelation_lift_second (U₀ U₁ U₂ : Submodule K F) (x : F)
    (hx : x ∈ U₁ ⊓ (U₀ ⊔ U₂)) :
    ∃ h : alignedRelation U₀ U₁ U₂, (h:F × F × F).2.1 = x := by
  obtain ⟨a,ha,c,hc,hac⟩ := Submodule.mem_sup.mp hx.2
  exact ⟨⟨(-a,x,c),U₀.neg_mem ha,hx.1,hc,by change -a + x = c; rw [← hac]; abel⟩,rfl⟩

/-- Each enlarged third-user coefficient lifts to a full aligned relation. -/
theorem alignedRelation_lift_third (U₀ U₁ U₂ : Submodule K F) (x : F)
    (hx : x ∈ U₂ ⊓ (U₀ ⊔ U₁)) :
    ∃ h : alignedRelation U₀ U₁ U₂, (h:F × F × F).2.2 = x := by
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx.2
  exact ⟨⟨(a,b,x),ha,hb,hx.1,hab⟩,rfl⟩

/-- Broadcast a basis of a feasible coefficient subspace. The constructor
has exactly its dimension many scalar message coordinates. -/
theorem scalarBroadcastCode_of_subspace [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (S : Submodule K F)
    (hspan : ∀ i, U i ≤ A i ⊔ S) :
    Nonempty (ScalarBroadcastCode A U (Module.finrank K S)) := by
  let b := Module.finBasis K S
  have hb : Submodule.span K (Set.range (fun j => (b j : F))) = S := by
    have he := congrArg (Submodule.map S.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at he
    rw [← Set.range_comp] at he
    exact he
  apply scalarBroadcastCode_of_span A U (fun j => (b j : F))
  simpa only [hb] using hspan

/-- A coordinate projection that reads a specified independent family as
standard basis vectors. Its extension outside their span is immaterial. -/
theorem independent_coordinate_projection {J : Type*} [Fintype J] [DecidableEq J]
    (v : J → F) (hv : LinearIndependent K v) :
    ∃ p : F →ₗ[K] (J → K), ∀ j k, p (v j) k = if j = k then 1 else 0 := by
  obtain ⟨p,hp⟩ := (Basis.span hv).equivFun.toLinearMap.exists_extend
  refine ⟨p,fun j k => ?_⟩
  have he := congrFun (LinearMap.congr_fun hp ((Basis.span hv) j)) k
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, Basis.span_apply,
    LinearEquiv.coe_coe, Basis.equivFun_self] using he

/-- Coordinate-free homogeneous-column reconciliation for independent
families. Separate witnesses need not be bases of the ambient space. -/
theorem homogeneous_independent_coordination
    {G I : Type*} [DecidableEq G] [Fintype G] [Fintype I] [Fintype K]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (N : I → Type*) [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (w : (i : I) → ((g : G) → V g) → N i → F)
    (hcol : ∀ i g a,
      (∀ x, w i (Function.update a g x) = w i a) ∨
      (∃ (j : N i) (l : V g →ₗ[K] F),
        ∀ x, w i (Function.update a g x) = Function.update (w i a) j (l x)))
    (hw : ∀ i, ∃ a, LinearIndependent K (w i a))
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ a, ∀ i, LinearIndependent K (w i a) := by
  classical
  choose a ha using hw
  choose p hp using fun i => independent_coordinate_projection (w i (a i)) (ha i)
  let C : (i : I) → ((g : G) → V g) → Matrix (N i) (N i) K :=
    fun i x r c => p i (w i x c) r
  have hC : HomogeneousColumnGroups V N C := by
    intro i g x
    rcases hcol i g x with hc | ⟨j,l,hl⟩
    · exact Or.inl (fun y => by simp only [C,hc y])
    · refine Or.inr ⟨j,(p i).comp l,fun y => ?_⟩
      ext r c
      dsimp [C]
      rw [hl y]
      by_cases hc : c = j
      · subst c; simp [Matrix.updateCol]
      · simp [Function.update_of_ne hc, Matrix.updateCol, hc]
  have hwC : ∀ i, ∃ x, (C i x).det ≠ 0 := by
    intro i
    refine ⟨a i,?_⟩
    have he : C i (a i) = 1 := by
      ext r c
      simp only [C,hp,Matrix.one_apply]
      split_ifs <;> simp_all
    rw [he,Matrix.det_one]
    exact one_ne_zero
  obtain ⟨x,hx⟩ := homogeneous_column_coordination V N C hC hwC hcount
  refine ⟨x,fun i => ?_⟩
  apply LinearIndependent.of_comp (p i)
  exact Matrix.linearIndependent_cols_of_det_ne_zero (hx i)

end UploadBroadcast
