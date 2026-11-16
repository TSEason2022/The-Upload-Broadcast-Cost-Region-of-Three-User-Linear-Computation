import UploadBroadcast.ResonantProfile
import UploadBroadcast.GeneralBroadcastOptimum
import UploadBroadcast.Examples

/-! A nonlinear scalar obstruction in the actual operational Task.Code model,
for the five-bit resonant example. -/
namespace UploadBroadcast.BinaryOperationalTightness
open ResonantEndomorphisms
abbrev K := ZMod 2
abbrev F := Ambient K K

def task : Task K F := ResonantRelay.task K K 0 LinearMap.id

def sourceOne : Source K F 1 where
  toFun p _ := p.2.2.2.1+p.2.2.2.2
  map_add' := by intro a b; ext i; simp; ring
  map_smul' := by intro a b; ext i; simp [mul_add]

def sourceTwo : Source K F 1 where
  toFun p _ := p.2.2.1+p.2.2.2.2
  map_add' := by intro a b; ext i; simp; ring
  map_smul' := by intro a b; ext i; simp [mul_add]

theorem side_zero_one : observe K F (task.A 2) 0=observe K F (task.A 2) sourceOne := by
  ext p i
  have hp : p.val.1=0 ∧ p.val.2.1=0 ∧ p.val.2.2.2.1+p.val.2.2.2.2=0 := p.property
  change 0=p.val.2.2.2.1+p.val.2.2.2.2
  exact hp.2.2.symm

theorem side_zero_two : observe K F (task.A 0) 0=observe K F (task.A 0) sourceTwo := by
  ext p i
  have hp : p.val.2.1=0 ∧ p.val.2.2.1=0 ∧ p.val.2.2.2.2=0 := p.property
  change 0=p.val.2.2.1+p.val.2.2.2.2
  simp [hp.2.1,hp.2.2]

theorem side_one_two : observe K F (task.A 1) sourceOne=observe K F (task.A 1) sourceTwo := by
  ext p i
  have hp : p.val.1=0 ∧ p.val.2.2.1=0 ∧ p.val.2.2.2.1=0 := p.property
  change p.val.2.2.2.1+p.val.2.2.2.2=p.val.2.2.1+p.val.2.2.2.2
  rw [hp.2.1,hp.2.2]

theorem signal_zero_one : observe K F (task.U 2) 0≠observe K F (task.U 2) sourceOne := by
  intro h
  let d : task.U 2 := ⟨(1,1,0,1,0),by
    change (1:K)=1+(0:K→ₗ[K]K) 1 ∧ (1:K)+0=LinearMap.id (1:K)
    simp⟩
  have hh := congrArg (fun f : task.U 2 →ₗ[K] (Fin 1→K) => f d 0) h
  norm_num [observe,sourceOne,d] at hh

theorem signal_zero_two : observe K F (task.U 0) 0≠observe K F (task.U 0) sourceTwo := by
  intro h
  let d : task.U 0 := ⟨(0,1,1,0,0),by change (1:K)=1 ∧ (0:K)=0; simp⟩
  have hh := congrArg (fun f : task.U 0 →ₗ[K] (Fin 1→K) => f d 0) h
  norm_num [observe,sourceTwo,d] at hh

theorem signal_one_two : observe K F (task.U 1) sourceOne≠observe K F (task.U 1) sourceTwo := by
  intro h
  let d : task.U 1 := ⟨(1,0,1,0,0),by change (1:K)=1 ∧ (0:K)=0; simp⟩
  have hh := congrArg (fun f : task.U 1 →ₗ[K] (Fin 1→K) => f d 0) h
  norm_num [observe,sourceOne,sourceTwo,d] at hh

/-- Equal side observations and unequal demands force different transmitted
messages for arbitrary nonlinear encoders and decoders. -/
theorem transmitted_ne {M : Three→Type*} {S : Type*} (c : task.Code 1 M S)
    (x y : Source K F 1) (i : Three)
    (hs : observe K F (task.A i) x=observe K F (task.A i) y)
    (hu : observe K F (task.U i) x≠observe K F (task.U i) y) :
    c.transmitted x≠c.transmitted y := by
  intro ht
  apply hu
  rw [← c.zero_error x i,← c.zero_error y i]
  change c.decode i (c.transmitted x) _=c.decode i (c.transmitted y) _
  rw [hs,ht]

/-- At least three actually attainable messages are necessary, regardless of
nominal broadcast alphabet or of the local-upload architecture. -/
theorem scalar_broadcast_card {M : Three→Type*} {S : Type*} [Finite S]
    (c : task.Code 1 M S) : 3 ≤ Nat.card (Set.range c.transmitted) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have h01 := transmitted_ne c 0 sourceOne 2 side_zero_one signal_zero_one
  have h02 := transmitted_ne c 0 sourceTwo 0 side_zero_two signal_zero_two
  have h12 := transmitted_ne c sourceOne sourceTwo 1 side_one_two signal_one_two
  let f : Fin 3 → Set.range c.transmitted := fun i =>
    ⟨c.transmitted (![0,sourceOne,sourceTwo] i),⟨![0,sourceOne,sourceTwo] i,rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

theorem full_first (r : Fin 6) : Profile.entry task (.inl r)=1 := by
  have h := ResonantRelay.full_firstProfile K K (0:K→ₗ[K]K) LinearMap.id
    (by simp) r
  simpa [task] using h

theorem full_second (i j : Three) : Profile.entry task (.inr (i,j))=3/2 := by
  have h := ResonantRelay.full_secondProfile K K (0:K→ₗ[K]K) LinearMap.id
    (by simpa using Function.surjective_id) (fun w _ hw => hw) i j
  simp only [Module.finrank_self, Nat.cast_one, mul_one] at h
  change 2 * Profile.entry task (.inr (i,j))=3 at h
  linarith

theorem rankBound_eq : Profile.rankBound task=3/2 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro r _
    cases r with
    | inl r => rw [full_first]; norm_num
    | inr r => rw [full_second]
  · rw [← full_second 0 0]
    exact Profile.entry_le_rankBound task _

theorem broadcastOptimum_eq : broadcastOptimum task.A task.U=3/2 := by
  rw [task_general_broadcastOptimum_eq_rankBound task,rankBound_eq]

/-- The factor-two necessity is genuinely nonlinear in the operational model:
no scalar fixed-length zero-error code can attain the fully informed optimum. -/
theorem scalar_broadcast_cost_strict {M : Three→Type*} {S : Type*} [Finite S]
    (c : task.Code 1 M S) : broadcastOptimum task.A task.U<c.broadcastCost := by
  have hc : (3:ℝ) ≤ Nat.card (Set.range c.transmitted) := by
    exact_mod_cast scalar_broadcast_card c
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by norm_num : (0:ℝ)<3) hc
  have hstrict := Real.logb_lt_logb (by norm_num : (1:ℝ)<2)
    (by norm_num : (0:ℝ)<8) (by norm_num : (8:ℝ)<3^2)
  rw [Examples.logb_two_eight,Real.logb_pow] at hstrict
  norm_num at hstrict
  rw [broadcastOptimum_eq]
  have hcard : Nat.card K=2 := by simp [K,Nat.card_eq_fintype_card]
  simp only [Task.Code.broadcastCost,hcard,Nat.cast_ofNat,Nat.cast_one,div_one]
  linarith

/-- Even nonlinear attainment of this optimum needs at least two instances. -/
theorem two_le_blocklength_of_broadcast_optimal {L : ℕ} {M : Three→Type*}
    {S : Type*} [Finite S] (c : task.Code L M S) (hL : 0<L)
    (hc : c.broadcastCost=broadcastOptimum task.A task.U) : 2≤L := by
  by_contra hn
  have he : L=1 := by omega
  subst L
  have hs := scalar_broadcast_cost_strict c
  rw [hc] at hs
  exact lt_irrefl _ hs

end UploadBroadcast.BinaryOperationalTightness
