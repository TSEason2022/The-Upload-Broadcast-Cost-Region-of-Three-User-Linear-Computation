import UploadBroadcast.ScalarBroadcast
import UploadBroadcast.AllocationNat

/-! Change of coefficient field by a genuine field isomorphism, including
operational encoders and decoders. -/
namespace UploadBroadcast.SemilinearTransport
attribute [local instance] RingHomInvPair.of_ringEquiv
variable {K L F G : Type*} [Field K] [Field L]
  [AddCommGroup F] [Module K F] [AddCommGroup G] [Module L G]
variable (σ : K ≃+* L)
local instance : RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
local instance : RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.symm _ _

/-- Transport a linear map by semilinear equivalences on domain and codomain. -/
def conjugate {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module L Y]
    (e : F ≃ₛₗ[σ.toRingHom] G) (f : X ≃ₛₗ[σ.toRingHom] Y)
    (a : F →ₗ[K] X) : G →ₗ[L] Y where
  toFun x := f (a (e.symm x))
  map_add' x y := by simp
  map_smul' c x := by simp [LinearEquiv.map_smulₛₗ]

/-- The dual changes by applying the field isomorphism to each evaluation. -/
def dual (e : F ≃ₛₗ[σ.toRingHom] G) :
    (F →ₗ[K] K) ≃ₛₗ[σ.toRingHom] (G →ₗ[L] L) where
  toFun a := {
    toFun := fun x => σ (a (e.symm x))
    map_add' := by intros; simp
    map_smul' := by intros; simp [LinearEquiv.map_smulₛₗ] }
  invFun b := {
    toFun := fun x => σ.symm (b (e x))
    map_add' := by intros; simp
    map_smul' := by intros; simp [LinearEquiv.map_smulₛₗ] }
  left_inv a := by ext x; simp
  right_inv b := by ext x; simp
  map_add' a b := by ext x; simp
  map_smul' c a := by ext x; simp

def coordinates (n : ℕ) : (Fin n → K) ≃ₛₗ[σ.toRingHom] (Fin n → L) where
  toFun a i := σ (a i)
  invFun b i := σ.symm (b i)
  left_inv a := by ext i; simp
  right_inv b := by ext i; simp
  map_add' a b := by ext i; simp
  map_smul' c a := by ext i; simp

def prod {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module L Y]
    (e : F ≃ₛₗ[σ.toRingHom] G) (f : X ≃ₛₗ[σ.toRingHom] Y) :
    (F × X) ≃ₛₗ[σ.toRingHom] (G × Y) where
  toFun p := (e p.1, f p.2)
  invFun p := (e.symm p.1, f.symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp
  map_smul' c p := by simp [LinearEquiv.map_smulₛₗ]

@[simp] theorem dual_apply (e : F ≃ₛₗ[σ.toRingHom] G) (a : F →ₗ[K] K) (x : G) :
    dual σ e a x = σ (a (e.symm x)) := rfl
@[simp] theorem dual_symm_apply (e : F ≃ₛₗ[σ.toRingHom] G) (a : G →ₗ[L] L) (x : F) :
    (dual σ e).symm a x = σ.symm (a (e x)) := rfl
@[simp] theorem coordinates_symm_apply (n : ℕ) (a : Fin n → L) (i : Fin n) :
    (coordinates σ n).symm a i = σ.symm (a i) := rfl
@[simp] theorem prod_symm_apply {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module L Y]
    (e : F ≃ₛₗ[σ.toRingHom] G) (f : X ≃ₛₗ[σ.toRingHom] Y) (p : G × Y) :
    (prod σ e f).symm p = (e.symm p.1, f.symm p.2) := rfl

/-- Field transport preserves genuine zero-error linear codes, with the same
number of transmitted scalar symbols. -/
def code (e : F ≃ₛₗ[σ.toRingHom] G)
    {A U : Fin 3 → Submodule K F} {n : ℕ} (c : ScalarBroadcastCode A U n) :
    ScalarBroadcastCode (fun i => (A i).map e.toLinearMap)
      (fun i => (U i).map e.toLinearMap) n where
  encode := conjugate σ (dual σ e) (coordinates σ n) c.encode
  decode i := conjugate σ
    (prod σ (coordinates σ n) (dual σ (e.submoduleMap (A i))))
    (dual σ (e.submoduleMap (U i))) (c.decode i)
  zero_error x i := by
    have hobs : (dual σ (e.submoduleMap (A i))).symm
        (dualObserve ((A i).map e.toLinearMap) x) =
        dualObserve (A i) ((dual σ e).symm x) := by
      ext a
      rfl
    have h := c.zero_error ((dual σ e).symm x) i
    apply LinearMap.ext
    intro u
    have hh := LinearMap.congr_fun h ((e.submoduleMap (U i)).symm u)
    change σ ((c.decode i)
      ((coordinates σ n).symm ((coordinates σ n) (c.encode ((dual σ e).symm x))),
       (dual σ (e.submoduleMap (A i))).symm
         (dualObserve ((A i).map e.toLinearMap) x))
      ((e.submoduleMap (U i)).symm u)) = x u
    rw [LinearEquiv.symm_apply_apply, hobs, hh]
    change σ (σ.symm (x (e (e.symm (u : G))))) = x u
    simp

/-- The actual encoder images are equivalent, not merely bounded by the
same nominal transmission length. -/
def codeRangeEquiv (e : F ≃ₛₗ[σ.toRingHom] G)
    {A U : Fin 3 → Submodule K F} {n : ℕ} (c : ScalarBroadcastCode A U n) :
    Set.range c.encode ≃ Set.range (code σ e c).encode where
  toFun y := ⟨coordinates σ n y, by
    rcases y with ⟨y,x,rfl⟩
    exact ⟨dual σ e x, by simp [code, conjugate]⟩⟩
  invFun y := ⟨(coordinates σ n).symm y, by
    rcases y with ⟨y,x,rfl⟩
    exact ⟨(dual σ e).symm x, by simp [code, conjugate]⟩⟩
  left_inv y := by apply Subtype.ext; exact (coordinates σ n).symm_apply_apply y
  right_inv y := by apply Subtype.ext; exact (coordinates σ n).apply_symm_apply y

/-- Exact attained-alphabet cost is invariant under field transport. -/
theorem code_cost (e : F ≃ₛₗ[σ.toRingHom] G)
    {A U : Fin 3 → Submodule K F} {n : ℕ} (c : ScalarBroadcastCode A U n) :
    Real.logb (Nat.card L) (Nat.card (Set.range (code σ e c).encode)) =
      Real.logb (Nat.card K) (Nat.card (Set.range c.encode)) := by
  rw [← Nat.card_congr σ.toEquiv, ← Nat.card_congr (codeRangeEquiv σ e c)]

/-- Semilinear field changes preserve dimensions even without finiteness. -/
theorem finrank (e : F ≃ₛₗ[σ.toRingHom] G) :
    Module.finrank K F = Module.finrank L G := by
  have h := lift_rank_eq_of_equiv_equiv σ e.toAddEquiv σ.bijective
    (fun r m => e.map_smulₛₗ r m)
  simpa only [Module.finrank, Cardinal.toNat_lift] using congrArg Cardinal.toNat h

theorem finrank_map (e : F ≃ₛₗ[σ.toRingHom] G) (P : Submodule K F) :
    Module.finrank L (P.map e.toLinearMap) = Module.finrank K P :=
  (finrank σ (e.submoduleMap P)).symm

theorem condRank_map [FiniteDimensional K F] [FiniteDimensional L G] (e : F ≃ₛₗ[σ.toRingHom] G) (P Q : Submodule K F) :
    condRank (P.map e.toLinearMap) (Q.map e.toLinearMap) = condRank P Q := by
  unfold condRank
  rw [← Submodule.map_sup]
  rw [finrank_map, finrank_map]

theorem actualNumericLP_map [FiniteDimensional K F] [FiniteDimensional L G]
    (e : F ≃ₛₗ[σ.toRingHom] G) (A U : Fin 3 → Submodule K F) :
    Allocation.actualNumericLP (fun i => (A i).map e.toLinearMap)
      (fun i => (U i).map e.toLinearMap) = Allocation.actualNumericLP A U := by
  simp only [Allocation.actualNumericLP, Allocation.commonRank, Allocation.pairRank,
    Allocation.pairSumRank, Allocation.enlargedRank, Allocation.demandRank,
    ← Submodule.map_inf e.toLinearMap e.injective, ← Submodule.map_sup, condRank_map]

end UploadBroadcast.SemilinearTransport
