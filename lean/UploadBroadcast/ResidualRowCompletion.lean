import UploadBroadcast.ResidualUpload

/-!
# Simultaneous row completion in explicit residual normal-form coordinates

There are three row blocks, each lacking a pure demand at its indexed user,
and one two-row diamond block. An empty-demand block can be included in the
first row block. This file proves the row construction in these exact
coordinates. Extracting these coordinates from an arbitrary triple is a
separate normal-form transport theorem.
-/
namespace UploadBroadcast.ResidualRowCompletion
open Module ResidualUpload
variable {K H₁ H₂ H₃ D : Type*} [Field K]
  [AddCommGroup H₁] [Module K H₁] [AddCommGroup H₂] [Module K H₂]
  [AddCommGroup H₃] [Module K H₃] [AddCommGroup D] [Module K D]

abbrev Rows (H₁ H₂ H₃ D : Type*) := H₁ × H₂ × H₃ × D × D

/-- All pure-row and retained mixed-row uploads at once. -/
def rowUpload : Rows H₁ H₂ H₃ D →ₗ[K] (Rows H₁ H₂ H₃ D × Rows H₁ H₂ H₃ D) where
  toFun t := ((t.1,0,-t.2.2.1,0,t.2.2.2.2), (0,t.2.1,t.2.2.1,t.2.2.2.1,0))
  map_add' x y := by simp [add_comm]
  map_smul' a x := by simp

local notation "J" => rowUpload (K := K) (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := D)

theorem rowUpload_injective : Function.Injective J := by
  intro x y h
  have h1 : x.1 = y.1 := congrArg (fun z => z.1.1) h
  have h2 : x.2.1 = y.2.1 := congrArg (fun z => z.2.2.1) h
  have h3 : x.2.2.1 = y.2.2.1 := congrArg (fun z => z.2.2.2.1) h
  have h4 : x.2.2.2.1 = y.2.2.2.1 := congrArg (fun z => z.2.2.2.2.1) h
  have h5 : x.2.2.2.2 = y.2.2.2.2 := congrArg (fun z => z.1.2.2.2.2) h
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5)))

/-- The relay consists exactly of generators available at users 1, 2, or 3. -/
theorem rowUpload_locally_generated :
    let P := LinearMap.range (J)
    P = (P ⊓ LinearMap.range vMap) ⊔ (P ⊓ LinearMap.range rMap) ⊔
      (P ⊓ LinearMap.range diffMap) := by
  dsimp only
  apply le_antisymm
  · rintro _ ⟨t,rfl⟩
    have h1 : J (t.1,0,0,0,t.2.2.2.2) ∈
        LinearMap.range (J) ⊓ LinearMap.range vMap := by
      exact ⟨⟨_,rfl⟩,⟨(t.1,0,0,0,t.2.2.2.2),by simp [rowUpload,vMap]⟩⟩
    have h2 : J (0,t.2.1,0,t.2.2.2.1,0) ∈
        LinearMap.range (J) ⊓ LinearMap.range rMap := by
      exact ⟨⟨_,rfl⟩,⟨(0,t.2.1,0,t.2.2.2.1,0),by simp [rowUpload,rMap]⟩⟩
    have h3 : J (0,0,t.2.2.1,0,0) ∈
        LinearMap.range (J) ⊓ LinearMap.range diffMap := by
      exact ⟨⟨_,rfl⟩,⟨(0,0,t.2.2.1,0,0),by simp [rowUpload,diffMap,vMap,rMap]⟩⟩
    convert Submodule.add_mem_sup (Submodule.add_mem_sup h1 h2) h3 using 1;
      simp [rowUpload]
  · exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left

/-- User 1 lacks only its excluded row block and the b-direction of the diamond. -/
theorem user₁_recovers (z : Rows H₁ H₂ H₃ D × Rows H₁ H₂ H₃ D)
    (h₁ : z.2.1 = 0) (hb : z.2.2.2.2.2 = 0) :
    z ∈ LinearMap.range (vMap (K := K)) ⊔ LinearMap.range J := by
  let t : Rows H₁ H₂ H₃ D := (0,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,0)
  refine Submodule.mem_sup.mpr ⟨vMap (z.1 - (J t).1), ⟨_,rfl⟩,
    J t, ⟨_,rfl⟩, ?_⟩
  ext <;> simp [vMap,rowUpload,t,h₁,hb]

/-- User 2 lacks only its excluded row block and the a-direction of the diamond. -/
theorem user₂_recovers (z : Rows H₁ H₂ H₃ D × Rows H₁ H₂ H₃ D)
    (h₂ : z.1.2.1 = 0) (ha : z.1.2.2.2.1 = 0) :
    z ∈ LinearMap.range (rMap (K := K)) ⊔ LinearMap.range J := by
  let t : Rows H₁ H₂ H₃ D := (z.1.1,0,-z.1.2.2.1,0,z.1.2.2.2.2)
  refine Submodule.mem_sup.mpr ⟨rMap (z.2 - (J t).2), ⟨_,rfl⟩,
    J t, ⟨_,rfl⟩, ?_⟩
  ext <;> simp [rMap,rowUpload,t,h₂,ha]

/-- User 3 lacks only its excluded row block; the diamond is fully recovered. -/
theorem user₃_recovers (z : Rows H₁ H₂ H₃ D × Rows H₁ H₂ H₃ D)
    (h₃ : z.1.2.2.1 + z.2.2.2.1 = 0) :
    z ∈ LinearMap.range (diffMap (K := K)) ⊔ LinearMap.range J := by
  let t : Rows H₁ H₂ H₃ D := (z.1.1+z.2.1,z.1.2.1+z.2.2.1,0,
    z.1.2.2.2.1+z.2.2.2.2.1,z.1.2.2.2.2+z.2.2.2.2.2)
  refine Submodule.mem_sup.mpr ⟨diffMap (z.2-(J t).2),⟨_,rfl⟩,
    J t,⟨_,rfl⟩,?_⟩
  have hh := eq_neg_of_add_eq_zero_left h₃
  ext <;> simp [diffMap,vMap,rMap,rowUpload,t,hh]

/-- Total row upload rank equals the number of retained rows. -/
theorem rowUpload_rank [FiniteDimensional K H₁] [FiniteDimensional K H₂]
    [FiniteDimensional K H₃] [FiniteDimensional K D] :
    finrank K (LinearMap.range (J)) =
      finrank K (Rows H₁ H₂ H₃ D) := LinearMap.finrank_range_of_inj rowUpload_injective

section Corrections
variable {P₁ P₂ P₃ : Type*}
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃]

/-- A linear row map on any private-demand subspace is the restriction of a
sum of two local correction maps. -/
theorem extend_row {P Q E : Type*} [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E]
    (L : Submodule K (P × Q)) (φ : L →ₗ[K] E) :
    ∃ (g : P →ₗ[K] E) (h : Q →ₗ[K] E), ∀ x : L, g x.val.1 + h x.val.2 = φ x := by
  obtain ⟨f,hf⟩ := φ.exists_extend
  refine ⟨f.comp (LinearMap.inl K P Q), f.comp (LinearMap.inr K P Q), ?_⟩
  intro x
  change f (x.val.1,0) + f (0,x.val.2) = φ x
  rw [← map_add]
  simpa using LinearMap.congr_fun hf x

/-- All missing coordinate corrections are compatible, even on the shared
private source P₃. Targets are independent row coordinates. -/
theorem simultaneous_corrections
    (L₁ : Submodule K (P₂ × P₃)) (L₂ : Submodule K (P₁ × P₃))
    (L₃ : Submodule K (P₁ × P₂))
    (φ₁ : L₁ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₂ : L₂ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₃ : L₃ →ₗ[K] Rows H₁ H₂ H₃ D) :
    ∃ (g₁ : P₁ →ₗ[K] Rows H₁ H₂ H₃ D)
      (g₂ : P₂ →ₗ[K] Rows H₁ H₂ H₃ D) (g₃ : P₃ →ₗ[K] Rows H₁ H₂ H₃ D),
      (∀ x : L₁,
        (φ₁ x - g₂ x.val.1 - g₃ x.val.2).1 = 0 ∧
        (φ₁ x - g₂ x.val.1 - g₃ x.val.2).2.2.2.2 = 0) ∧
      (∀ x : L₂,
        (φ₂ x - g₁ x.val.1 + g₃ x.val.2).2.1 = 0 ∧
        (φ₂ x - g₁ x.val.1 + g₃ x.val.2).2.2.2.1 = 0) ∧
      (∀ x : L₃, (φ₃ x - g₁ x.val.1 - g₂ x.val.2).2.2.1 = 0) := by
  let f₁ : L₁ →ₗ[K] (H₁ × D) :=
    { toFun := fun x => ((φ₁ x).1,(φ₁ x).2.2.2.2)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let f₂ : L₂ →ₗ[K] (H₂ × D) :=
    { toFun := fun x => ((φ₂ x).2.1,(φ₂ x).2.2.2.1)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let f₃ : L₃ →ₗ[K] H₃ :=
    { toFun := fun x => (φ₃ x).2.2.1
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  obtain ⟨a₂,a₃,ha⟩ := extend_row L₁ f₁
  obtain ⟨b₁,b₃,hb⟩ := extend_row L₂ f₂
  obtain ⟨c₁,c₂,hc⟩ := extend_row L₃ f₃
  let g₁ : P₁ →ₗ[K] Rows H₁ H₂ H₃ D :=
    { toFun := fun p => (0,(b₁ p).1,c₁ p,(b₁ p).2,0)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let g₂ : P₂ →ₗ[K] Rows H₁ H₂ H₃ D :=
    { toFun := fun p => ((a₂ p).1,0,c₂ p,0,(a₂ p).2)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let g₃ : P₃ →ₗ[K] Rows H₁ H₂ H₃ D :=
    { toFun := fun p => ((a₃ p).1,-(b₃ p).1,0,-(b₃ p).2,(a₃ p).2)
      map_add' := by intros; simp [add_comm]
      map_smul' := by intros; simp }
  refine ⟨g₁,g₂,g₃,?_,?_,?_⟩
  · intro x
    have hh := ha x
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    dsimp [f₁] at h1 h2
    dsimp [g₁,g₂,g₃]
    constructor
    · rw [← h1]; abel
    · rw [← h2]; abel
  · intro x
    have hh := hb x
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    dsimp [f₂] at h1 h2
    dsimp [g₁,g₂,g₃]
    constructor
    · rw [← h1]; abel
    · rw [← h2]; abel
  · intro x
    have hh := hc x
    dsimp [f₃] at hh
    dsimp [g₁,g₂,g₃]
    rw [← hh]
    abel
/-- Private coefficients plus the explicit row relay, with no redundant
coordinate in its domain. -/
def fullRelay : (((P₁ × P₂) × P₃) × Rows H₁ H₂ H₃ D) →ₗ[K]
    Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) where
  toFun x := (x.1,J x.2)
  map_add' x y := by simp
  map_smul' a x := by simp

local notation "FJ" => fullRelay (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
  (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := D)
local notation "P" => LinearMap.range FJ
local notation "S₁" => A₁ K P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)
local notation "S₂" => A₂ K P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)
local notation "S₃" => A₃ K P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)

theorem fullRelay_injective : Function.Injective (fullRelay (K := K) (P₁ := P₁)
    (P₂ := P₂) (P₃ := P₃) (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (D := D)) := by
  intro x y h
  have hp := congrArg (fun z : Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) => z.1) h
  change x.1 = y.1 at hp
  have ht : J x.2 = J y.2 := congrArg Prod.snd h
  exact Prod.ext hp (rowUpload_injective ht)

/-- The assembled private-plus-row relay is locally generated by the actual
three residual side-information spaces. -/
theorem fullRelay_locally_generated : P = ⨆ i : Fin 3, P ⊓ ![S₁,S₂,S₃] i := by
  apply le_antisymm
  · rintro _ ⟨⟨p,t⟩,rfl⟩
    let x₁ : ((P₁ × P₂) × P₃) × Rows H₁ H₂ H₃ D :=
      (((p.1.1,0),0),(t.1,0,0,0,t.2.2.2.2))
    let x₂ : ((P₁ × P₂) × P₃) × Rows H₁ H₂ H₃ D :=
      (((0,p.1.2),0),(0,t.2.1,0,t.2.2.2.1,0))
    let x₃ : ((P₁ × P₂) × P₃) × Rows H₁ H₂ H₃ D :=
      (((0,0),p.2),(0,0,t.2.2.1,0,0))
    have h₁ : FJ x₁ ∈ P ⊓ S₁ := by
      refine ⟨⟨_,rfl⟩,⟨(p.1.1,(t.1,0,0,0,t.2.2.2.2)),?_⟩⟩
      simp [side₁,fullRelay,rowUpload,x₁]
    have h₂ : FJ x₂ ∈ P ⊓ S₂ := by
      refine ⟨⟨_,rfl⟩,⟨(p.1.2,(0,t.2.1,0,t.2.2.2.1,0)),?_⟩⟩
      simp [side₂,fullRelay,rowUpload,x₂]
    have h₃ : FJ x₃ ∈ P ⊓ S₃ := by
      refine ⟨⟨_,rfl⟩,⟨(p.2,(0,0,t.2.2.1,0,0)),?_⟩⟩
      simp [side₃,fullRelay,rowUpload,x₃]
    have h₁' := (le_iSup (fun i : Fin 3 => P ⊓ ![S₁,S₂,S₃] i) 0) h₁
    have h₂' := (le_iSup (fun i : Fin 3 => P ⊓ ![S₁,S₂,S₃] i) 1) h₂
    have h₃' := (le_iSup (fun i : Fin 3 => P ⊓ ![S₁,S₂,S₃] i) 2) h₃
    have he : FJ x₁ + FJ x₂ + FJ x₃ = FJ (p,t) := by
      simp [fullRelay,rowUpload,x₁,x₂,x₃]
    rw [← he]
    exact Submodule.add_mem _ (Submodule.add_mem _ h₁' h₂') h₃'
  · exact iSup_le fun _ => inf_le_left

/-- Full-relay rank equals private dimensions plus retained row dimensions. -/
theorem fullRelay_rank [FiniteDimensional K P₁] [FiniteDimensional K P₂]
    [FiniteDimensional K P₃] [FiniteDimensional K H₁] [FiniteDimensional K H₂]
    [FiniteDimensional K H₃] [FiniteDimensional K D] :
    finrank K P = finrank K P₁ + finrank K P₂ + finrank K P₃ +
      finrank K (Rows H₁ H₂ H₃ D) := by
  rw [LinearMap.finrank_range_of_inj fullRelay_injective]
  simp only [Module.finrank_prod]

/-- Lift a row-space decoder to the actual private-plus-tripod coefficient
space. All private coefficients have already been uploaded. -/
theorem lift_row_recovery
    (A : Submodule K (Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)))
    (l : Rows H₁ H₂ H₃ D →ₗ[K] (Rows H₁ H₂ H₃ D × Rows H₁ H₂ H₃ D))
    (hl : ∀ t, ((0 : (P₁ × P₂) × P₃),l t) ∈ A)
    (z : Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D))
    (hz : z.2 ∈ LinearMap.range l ⊔ LinearMap.range J) : z ∈ A ⊔ P := by
  obtain ⟨a,⟨t,rfl⟩,b,⟨s,rfl⟩,he⟩ := Submodule.mem_sup.mp hz
  refine Submodule.mem_sup.mpr ⟨(0,l t),hl t,FJ (z.1,s),⟨_,rfl⟩,?_⟩
  apply Prod.ext
  · simp [fullRelay]
  · exact he

/-- Completion for the explicit normal-form signals. The shape hypotheses
state actual coefficients of signal vectors modulo the pure-demand rows:
user 1 has no pure H₁ or diamond-b demand, user 2 no pure H₂ or diamond-a
demand, and user 3 no pure H₃ demand. No relay-feasibility conclusion is
assumed. These conditions are preserved by adding the relevant side space. -/
theorem exists_simultaneous_row_completion
    (L₁ : Submodule K (P₂ × P₃)) (L₂ : Submodule K (P₁ × P₃))
    (L₃ : Submodule K (P₁ × P₂))
    (φ₁ : L₁ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₂ : L₂ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₃ : L₃ →ₗ[K] Rows H₁ H₂ H₃ D)
    (U₁ U₂ U₃ : Submodule K (Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)))
    (shape₁ : ∀ u ∈ U₁, ∃ x : L₁,
      u.1.1.2 = x.val.1 ∧ u.1.2 = x.val.2 ∧
      u.2.2.1 = (φ₁ x).1 ∧ u.2.2.2.2.2.2 = (φ₁ x).2.2.2.2)
    (shape₂ : ∀ u ∈ U₂, ∃ x : L₂,
      u.1.1.1 = x.val.1 ∧ u.1.2 = x.val.2 ∧
      u.2.1.2.1 = (φ₂ x).2.1 ∧ u.2.1.2.2.2.1 = (φ₂ x).2.2.2.1)
    (shape₃ : ∀ u ∈ U₃, ∃ x : L₃,
      u.1.1.1 = x.val.1 ∧ u.1.1.2 = x.val.2 ∧
      u.2.1.2.2.1 + u.2.2.2.2.1 = (φ₃ x).2.2.1) :
    ∃ e : Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) ≃ₗ[K]
        Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D),
      (S₁).map e.toLinearMap = S₁ ∧ (S₂).map e.toLinearMap = S₂ ∧
      (S₃).map e.toLinearMap = S₃ ∧
      U₁.map e.toLinearMap ≤ S₁ ⊔ P ∧ U₂.map e.toLinearMap ≤ S₂ ⊔ P ∧
      U₃.map e.toLinearMap ≤ S₃ ⊔ P := by
  obtain ⟨g₁,g₂,g₃,h₁,h₂,h₃⟩ := simultaneous_corrections L₁ L₂ L₃ φ₁ φ₂ φ₃
  let e := squareZeroShear (privateCorrection g₁ g₂ g₃) (privateCorrection_square_zero g₁ g₂ g₃)
  obtain ⟨hs₁,hs₂,hs₃⟩ := privateShear_preserves g₁ g₂ g₃
  refine ⟨e,hs₁,hs₂,hs₃,?_,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨x,hp₂,hp₃,hH,hb⟩ := shape₁ u hu
    apply lift_row_recovery S₁ vMap (fun t => ⟨(0,t),rfl⟩) (e u)
    apply user₁_recovers
    · have hh := (h₁ x).1
      change u.2.2.1 - ((g₂ u.1.1.2).1 + (g₃ u.1.2).1) = 0
      rw [hp₂,hp₃,hH]
      simpa only [Prod.fst_sub, sub_sub] using hh
    · have hh := (h₁ x).2
      change u.2.2.2.2.2.2 - ((g₂ u.1.1.2).2.2.2.2 + (g₃ u.1.2).2.2.2.2) = 0
      rw [hp₂,hp₃,hb]
      simpa only [Prod.snd_sub, sub_sub] using hh
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨x,hp₁,hp₃,hH,ha⟩ := shape₂ u hu
    apply lift_row_recovery S₂ rMap (fun t => ⟨(0,t),rfl⟩) (e u)
    apply user₂_recovers
    · have hh := (h₂ x).1
      change u.2.1.2.1 - ((g₁ u.1.1.1).2.1 - (g₃ u.1.2).2.1) = 0
      rw [hp₁,hp₃,hH]
      simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] at hh
      convert hh using 1; abel
    · have hh := (h₂ x).2
      change u.2.1.2.2.2.1 - ((g₁ u.1.1.1).2.2.2.1 - (g₃ u.1.2).2.2.2.1) = 0
      rw [hp₁,hp₃,ha]
      simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] at hh
      convert hh using 1; abel
  · rintro _ ⟨u,hu,rfl⟩
    obtain ⟨x,hp₁,hp₂,hH⟩ := shape₃ u hu
    apply lift_row_recovery S₃ diffMap (fun t => ⟨(0,t),by simp [side₃,diffMap,vMap,rMap]⟩) (e u)
    apply user₃_recovers
    have hh := h₃ x
    change (u.2.1.2.2.1 - ((g₁ u.1.1.1).2.2.1 - (g₃ u.1.2).2.2.1)) +
      (u.2.2.2.2.1 - ((g₂ u.1.1.2).2.2.1 + (g₃ u.1.2).2.2.1)) = 0
    have he : (u.2.1.2.2.1 - ((g₁ u.1.1.1).2.2.1 - (g₃ u.1.2).2.2.1)) +
        (u.2.2.2.2.1 - ((g₂ u.1.1.2).2.2.1 + (g₃ u.1.2).2.2.1)) =
        (u.2.1.2.2.1 + u.2.2.2.2.1) - (g₁ u.1.1.1).2.2.1 - (g₂ u.1.1.2).2.2.1 := by abel
    rw [he,hp₁,hp₂,hH]
    exact hh

/-- Actual pure demand representatives, distinct from projections of mixed graphs. -/
def pureR (B : Submodule K (Rows H₁ H₂ H₃ D)) :
    B →ₗ[K] Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) where
  toFun d := (0,(0,d.val))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def pureV (B : Submodule K (Rows H₁ H₂ H₃ D)) :
    B →ₗ[K] Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) where
  toFun d := (0,(d.val,0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Actual graph demand representatives in each of the three quotient coordinates. -/
def mixed₁ (L₁ : Submodule K (P₂ × P₃)) (φ₁ : L₁ →ₗ[K] Rows H₁ H₂ H₃ D) :
    L₁ →ₗ[K] Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) where
  toFun x := (((0,x.val.1),x.val.2),(0,φ₁ x))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def mixed₂ (L₂ : Submodule K (P₁ × P₃)) (φ₂ : L₂ →ₗ[K] Rows H₁ H₂ H₃ D) :
    L₂ →ₗ[K] Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) where
  toFun x := (((x.val.1,0),x.val.2),(φ₂ x,0))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def mixed₃ (L₃ : Submodule K (P₁ × P₂)) (φ₃ : L₃ →ₗ[K] Rows H₁ H₂ H₃ D) :
    L₃ →ₗ[K] Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D) where
  toFun x := (((x.val.1,x.val.2),0),(φ₃ x,0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

variable [FiniteDimensional K P₁] [FiniteDimensional K P₂] [FiniteDimensional K P₃]
  [FiniteDimensional K H₁] [FiniteDimensional K H₂] [FiniteDimensional K H₃]
  [FiniteDimensional K D]

/-- The completed relay, pulled back to the original mixed-demand coordinates.
The original side spaces are unchanged, and the rank is exactly dpriv+dtri. -/
theorem exists_original_coordinate_relay
    (L₁ : Submodule K (P₂ × P₃)) (L₂ : Submodule K (P₁ × P₃))
    (L₃ : Submodule K (P₁ × P₂))
    (φ₁ : L₁ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₂ : L₂ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₃ : L₃ →ₗ[K] Rows H₁ H₂ H₃ D)
    (U₁ U₂ U₃ : Submodule K (Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)))
    (shape₁ : ∀ u ∈ U₁, ∃ x : L₁,
      u.1.1.2 = x.val.1 ∧ u.1.2 = x.val.2 ∧
      u.2.2.1 = (φ₁ x).1 ∧ u.2.2.2.2.2.2 = (φ₁ x).2.2.2.2)
    (shape₂ : ∀ u ∈ U₂, ∃ x : L₂,
      u.1.1.1 = x.val.1 ∧ u.1.2 = x.val.2 ∧
      u.2.1.2.1 = (φ₂ x).2.1 ∧ u.2.1.2.2.2.1 = (φ₂ x).2.2.2.1)
    (shape₃ : ∀ u ∈ U₃, ∃ x : L₃,
      u.1.1.1 = x.val.1 ∧ u.1.1.2 = x.val.2 ∧
      u.2.1.2.2.1 + u.2.2.2.2.1 = (φ₃ x).2.2.1) :
    ∃ Q : Submodule K (Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)),
      (Q = ⨆ i : Fin 3, Q ⊓ ![S₁,S₂,S₃] i) ∧
      (∀ i : Fin 3, ![U₁,U₂,U₃] i ≤ ![S₁,S₂,S₃] i ⊔ Q) ∧
      finrank K Q = finrank K P₁ + finrank K P₂ + finrank K P₃ +
        finrank K (Rows H₁ H₂ H₃ D) := by
  obtain ⟨e,ha₁,ha₂,ha₃,hu₁,hu₂,hu₃⟩ :=
    exists_simultaneous_row_completion L₁ L₂ L₃ φ₁ φ₂ φ₃ U₁ U₂ U₃ shape₁ shape₂ shape₃
  have ha : ∀ i : Fin 3, (![S₁,S₂,S₃] i).map e.toLinearMap = ![S₁,S₂,S₃] i := by
    intro i
    fin_cases i <;> assumption
  have hu : ∀ i : Fin 3, (![U₁,U₂,U₃] i).map e.toLinearMap ≤ ![S₁,S₂,S₃] i ⊔ P := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨Q,hq,hfeas,hrank⟩ := pullback_relay ![S₁,S₂,S₃] ![U₁,U₂,U₃] e P ha
    fullRelay_locally_generated hu
  exact ⟨Q,hq,hfeas,hrank.trans fullRelay_rank⟩

/-- Row-wise upload completion for the actual generated signal subspaces in
explicit normal-form coordinates. Pure rows and mixed graphs are independent
inputs; the theorem never replaces a pure intersection by a projected demand. -/
theorem generated_signals_row_completion
    (B₁ B₂ B₃ : Submodule K (Rows H₁ H₂ H₃ D))
    (hB₁ : ∀ d ∈ B₁, d.1 = 0 ∧ d.2.2.2.2 = 0)
    (hB₂ : ∀ d ∈ B₂, d.2.1 = 0 ∧ d.2.2.2.1 = 0)
    (hB₃ : ∀ d ∈ B₃, d.2.2.1 = 0)
    (L₁ : Submodule K (P₂ × P₃)) (L₂ : Submodule K (P₁ × P₃))
    (L₃ : Submodule K (P₁ × P₂))
    (φ₁ : L₁ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₂ : L₂ →ₗ[K] Rows H₁ H₂ H₃ D)
    (φ₃ : L₃ →ₗ[K] Rows H₁ H₂ H₃ D) :
    let U₁ := S₁ ⊔ LinearMap.range (pureR (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) B₁) ⊔
      LinearMap.range (mixed₁ (P₁ := P₁) L₁ φ₁)
    let U₂ := S₂ ⊔ LinearMap.range (pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) B₂) ⊔
      LinearMap.range (mixed₂ (P₂ := P₂) L₂ φ₂)
    let U₃ := S₃ ⊔ LinearMap.range (pureV (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) B₃) ⊔
      LinearMap.range (mixed₃ (P₃ := P₃) L₃ φ₃)
    ∃ Q : Submodule K (Ambient P₁ P₂ P₃ (Rows H₁ H₂ H₃ D)),
      (Q = ⨆ i : Fin 3, Q ⊓ ![S₁,S₂,S₃] i) ∧
      (∀ i : Fin 3, ![U₁,U₂,U₃] i ≤ ![S₁,S₂,S₃] i ⊔ Q) ∧
      finrank K Q = finrank K P₁ + finrank K P₂ + finrank K P₃ +
        finrank K (Rows H₁ H₂ H₃ D) := by
  dsimp only
  apply exists_original_coordinate_relay L₁ L₂ L₃ φ₁ φ₂ φ₃
  · intro u hu
    obtain ⟨a,ha,m,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,⟨⟨p,t⟩,rfl⟩,d,⟨d,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
    have hd := hB₁ d d.property
    refine ⟨x,?_,?_,?_,?_⟩ <;> simp [side₁,pureR,mixed₁,hd]
  · intro u hu
    obtain ⟨a,ha,m,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,⟨⟨p,t⟩,rfl⟩,d,⟨d,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
    have hd := hB₂ d d.property
    refine ⟨x,?_,?_,?_,?_⟩ <;> simp [side₂,pureV,mixed₂,hd]
  · intro u hu
    obtain ⟨a,ha,m,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a,⟨⟨p,t⟩,rfl⟩,d,⟨d,rfl⟩,rfl⟩ := Submodule.mem_sup.mp ha
    have hd := hB₃ d d.property
    refine ⟨x,?_,?_,?_⟩ <;> simp [side₃,pureV,mixed₃,hd]

end Corrections

end UploadBroadcast.ResidualRowCompletion
