import UploadBroadcast.Model
import UploadBroadcast.LinearAlgebra
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Signal-intersection bridge in retained residual coordinates

This is the algebraic core of `lem:bridges`. The hypotheses describe actual
private and tripod coefficient embeddings and actual demand representatives.
The active-row hypothesis says each retained row is a sum of pure demand rows
and a lift of G(ker B). No signal-intersection inclusion is assumed.
The common parameter space L can be the direct sum of the three L_i.
-/
namespace UploadBroadcast
namespace SignalBridge
variable {K F T P₁ P₂ P₃ L : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup T] [Module K T]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup L] [Module K L]

/-- Exact residual coordinate data. `pure_i` are intersections with the tripod
quotient, not projections of mixed private/tripod demands. -/
structure Data where
  U₁ : Submodule K F
  U₂ : Submodule K F
  U₃ : Submodule K F
  p₁ : P₁ →ₗ[K] F
  p₂ : P₂ →ₗ[K] F
  p₃ : P₃ →ₗ[K] F
  v : T →ₗ[K] F
  r : T →ₗ[K] F
  D₁ : Submodule K T
  D₂ : Submodule K T
  D₃ : Submodule K T
  a₁₂ : L →ₗ[K] P₂
  a₁₃ : L →ₗ[K] P₃
  a₂₁ : L →ₗ[K] P₁
  a₂₃ : L →ₗ[K] P₃
  a₃₁ : L →ₗ[K] P₁
  a₃₂ : L →ₗ[K] P₂
  φ₁ : L →ₗ[K] T
  φ₂ : L →ₗ[K] T
  φ₃ : L →ₗ[K] T
  side₁ : ∀ d, v d ∈ U₁
  side₂ : ∀ d, r d ∈ U₂
  side₃ : ∀ d, r d - v d ∈ U₃
  private₁ : ∀ p, p₁ p ∈ U₁
  private₂ : ∀ p, p₂ p ∈ U₂
  private₃ : ∀ p, p₃ p ∈ U₃
  pure₁ : ∀ d ∈ D₁, r d ∈ U₁
  pure₂ : ∀ d ∈ D₂, v d ∈ U₂
  pure₃ : ∀ d ∈ D₃, v d ∈ U₃
  demand₁ : ∀ x, p₂ (a₁₂ x) + p₃ (a₁₃ x) + r (φ₁ x) ∈ U₁
  demand₂ : ∀ x, p₁ (a₂₁ x) + p₃ (a₂₃ x) + v (φ₂ x) ∈ U₂
  demand₃ : ∀ x, p₁ (a₃₁ x) + p₂ (a₃₂ x) + v (φ₃ x) ∈ U₃
  active : ∀ d, ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, ∃ d₃ ∈ D₃, ∃ x,
    a₂₁ x + a₃₁ x = 0 ∧ a₁₂ x + a₃₂ x = 0 ∧ a₁₃ x - a₂₃ x = 0 ∧
    d = d₁ + d₂ + d₃ + (φ₁ x + φ₂ x + φ₃ x)

variable (R : Data (K := K) (F := F) (T := T)
  (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (L := L))

/-- The manuscript's annihilator cancellation, derived from the demand vectors
and the signed private-incidence equations Bx=0. -/
theorem annihilator_v (f f₁ f₂ : F →ₗ[K] K)
    (hf : ∀ z ∈ R.U₃, f z = 0)
    (hf₁ : ∀ z ∈ R.U₁, f₁ z = 0)
    (hf₂ : ∀ z ∈ R.U₂, f₂ z = 0) (hs : f₁ + f₂ = f) :
    ∀ d, f (R.v d) = 0 := by
  have split (z : F) : f₁ z + f₂ z = f z := LinearMap.congr_fun hs z
  have vr (d : T) : f (R.r d) = f (R.v d) := by
    have h := hf _ (R.side₃ d)
    simpa only [map_sub, sub_eq_zero] using h
  have v₁ (d : T) := hf₁ _ (R.side₁ d)
  have r₂ (d : T) := hf₂ _ (R.side₂ d)
  have pv₁ (d : T) : f₁ (R.r d) = f (R.v d) := by
    have h := split (R.r d)
    rw [r₂, add_zero, vr] at h
    exact h
  have pv₂ (d : T) : f₂ (R.v d) = f (R.v d) := by
    have h := split (R.v d)
    rw [v₁, zero_add] at h
    exact h
  have p₃ (p : P₃) : f₁ (R.p₃ p) + f₂ (R.p₃ p) = 0 := by
    rw [split, hf _ (R.private₃ p)]
  intro d
  obtain ⟨d₁, hd₁, d₂, hd₂, d₃, hd₃, x, h₁, h₂, h₃, rfl⟩ := R.active d
  have z₁ : f (R.v d₁) = 0 := by rw [← pv₁]; exact hf₁ _ (R.pure₁ _ hd₁)
  have z₂ : f (R.v d₂) = 0 := by rw [← pv₂]; exact hf₂ _ (R.pure₂ _ hd₂)
  have z₃ := hf _ (R.pure₃ _ hd₃)
  have e₁ := hf₁ _ (R.demand₁ x)
  have e₂ := hf₂ _ (R.demand₂ x)
  have e₃ := hf _ (R.demand₃ x)
  simp only [map_add, pv₁, pv₂] at e₁ e₂ e₃
  have c₁ : f₂ (R.p₁ (R.a₂₁ x)) + f (R.p₁ (R.a₃₁ x)) = 0 := by
    have hc := congrArg (fun p => f₂ (R.p₁ p)) h₁
    simp only [map_add, map_zero] at hc
    rw [← split, hf₁ _ (R.private₁ _), zero_add]
    exact hc
  have c₂ : f₁ (R.p₂ (R.a₁₂ x)) + f (R.p₂ (R.a₃₂ x)) = 0 := by
    have hc := congrArg (fun p => f₁ (R.p₂ p)) h₂
    simp only [map_add, map_zero] at hc
    rw [← split, hf₂ _ (R.private₂ _), add_zero]
    exact hc
  have c₃ : f₁ (R.p₃ (R.a₁₃ x)) + f₂ (R.p₃ (R.a₂₃ x)) = 0 := by
    rw [sub_eq_zero] at h₃
    rw [h₃]
    exact p₃ _
  simp only [map_add, z₁, z₂, z₃, zero_add]
  linear_combination e₁ + e₂ + e₃ - c₁ - c₂ - c₃

/-- Actual coefficient-space intersection inclusion, valid over every field.
This is the first cyclic bridge, with arbitrary labels for the three users. -/
theorem tripod_le_signal_sup_inter :
    LinearMap.range R.v ⊔ LinearMap.range R.r ≤ R.U₃ ⊔ (R.U₁ ⊓ R.U₂) := by
  have hv (d : T) : R.v d ∈ R.U₃ ⊔ (R.U₁ ⊓ R.U₂) := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro f hf
    have hf3 : ∀ z ∈ R.U₃, f z = 0 := fun z hz =>
      ((Submodule.mem_dualAnnihilator _).mp hf) z (Submodule.mem_sup_left hz)
    have hfi : f ∈ (R.U₁ ⊓ R.U₂).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro z hz
      exact ((Submodule.mem_dualAnnihilator _).mp hf) z (Submodule.mem_sup_right hz)
    rw [Subspace.dualAnnihilator_inf_eq] at hfi
    obtain ⟨f₁, hf₁, f₂, hf₂, hs⟩ := Submodule.mem_sup.mp hfi
    exact annihilator_v R f f₁ f₂ hf3
      ((Submodule.mem_dualAnnihilator _).mp hf₁)
      ((Submodule.mem_dualAnnihilator _).mp hf₂) hs d
  apply sup_le
  · rintro _ ⟨d, rfl⟩
    exact hv d
  · rintro _ ⟨d, rfl⟩
    have h := (R.U₃ ⊔ (R.U₁ ⊓ R.U₂)).add_mem
      (Submodule.mem_sup_left (R.side₃ d)) (hv d)
    simpa only [sub_add_cancel] using h

/-- Cyclic relabeling with the actual tripod coordinate change
(v,r) ↦ (r-v,-v). The signed private incidence equations and G-sum are
preserved; this is valid in characteristic two as well. -/
def rotate : Data (K := K) (F := F) (T := T)
    (P₁ := P₃) (P₂ := P₁) (P₃ := P₂) (L := L) where
  U₁ := R.U₃
  U₂ := R.U₁
  U₃ := R.U₂
  p₁ := R.p₃
  p₂ := R.p₁
  p₃ := R.p₂
  v := R.r - R.v
  r := -R.v
  D₁ := R.D₃
  D₂ := R.D₁
  D₃ := R.D₂
  a₁₂ := -R.a₃₁
  a₁₃ := -R.a₃₂
  a₂₁ := R.a₁₃
  a₂₃ := R.a₁₂
  a₃₁ := -R.a₂₃
  a₃₂ := -R.a₂₁
  φ₁ := R.φ₃
  φ₂ := R.φ₁
  φ₃ := R.φ₂
  side₁ := R.side₃
  side₂ := fun d => R.U₁.neg_mem (R.side₁ d)
  side₃ := by
    intro d
    change -R.v d - (R.r d - R.v d) ∈ R.U₂
    have he : -R.v d - (R.r d - R.v d) = -R.r d := by abel
    rw [he]
    exact R.U₂.neg_mem (R.side₂ d)
  private₁ := R.private₃
  private₂ := R.private₁
  private₃ := R.private₂
  pure₁ := fun d hd => R.U₃.neg_mem (R.pure₃ d hd)
  pure₂ := fun d hd => R.U₁.sub_mem (R.pure₁ d hd) (R.side₁ d)
  pure₃ := fun d hd => R.U₂.sub_mem (R.side₂ d) (R.pure₂ d hd)
  demand₁ := by
    intro x
    have hh := R.U₃.neg_mem (R.demand₃ x)
    simpa only [LinearMap.neg_apply,map_neg,neg_add_rev,add_assoc,add_comm,add_left_comm] using hh
  demand₂ := by
    intro x
    have hh := R.U₁.sub_mem (R.demand₁ x) (R.side₁ (R.φ₁ x))
    convert hh using 1
    simp only [LinearMap.sub_apply]
    abel
  demand₃ := by
    intro x
    have hh := R.U₂.sub_mem (R.side₂ (R.φ₂ x)) (R.demand₂ x)
    convert hh using 1
    simp only [LinearMap.neg_apply,LinearMap.sub_apply,map_neg]
    abel
  active := by
    intro d
    obtain ⟨d₁,hd₁,d₂,hd₂,d₃,hd₃,x,h₁,h₂,h₃,he⟩ := R.active d
    refine ⟨d₃,hd₃,d₁,hd₁,d₂,hd₂,x,?_,?_,?_,?_⟩
    · simpa only [LinearMap.neg_apply,sub_eq_add_neg] using h₃
    · change -R.a₃₁ x + -R.a₂₁ x = 0
      rw [← neg_add, add_comm, h₁, neg_zero]
    · change -R.a₃₂ x - R.a₁₂ x = 0
      rw [sub_eq_add_neg,← neg_add,add_comm,h₂,neg_zero]
    · rw [he]
      abel

/-- The cyclic coordinate change preserves the entire tripod coefficient space. -/
theorem rotate_tripod_range :
    LinearMap.range (rotate R).v ⊔ LinearMap.range (rotate R).r =
      LinearMap.range R.v ⊔ LinearMap.range R.r := by
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨d,rfl⟩
      exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨d,rfl⟩) (Submodule.mem_sup_left ⟨d,rfl⟩)
    · rintro _ ⟨d,rfl⟩
      exact Submodule.neg_mem _ (Submodule.mem_sup_left ⟨d,rfl⟩)
  · apply sup_le
    · rintro _ ⟨d,rfl⟩
      have hh := Submodule.neg_mem
        (LinearMap.range (rotate R).v ⊔ LinearMap.range (rotate R).r)
        (Submodule.mem_sup_right (show (rotate R).r d ∈ LinearMap.range (rotate R).r from ⟨d,rfl⟩))
      simpa [rotate] using hh
    · rintro _ ⟨d,rfl⟩
      have hh := Submodule.sub_mem
        (LinearMap.range (rotate R).v ⊔ LinearMap.range (rotate R).r)
        (Submodule.mem_sup_left (show (rotate R).v d ∈ LinearMap.range (rotate R).v from ⟨d,rfl⟩))
        (Submodule.mem_sup_right (show (rotate R).r d ∈ LinearMap.range (rotate R).r from ⟨d,rfl⟩))
      simpa [rotate] using hh

/-- All three cyclic signal-intersection bridges follow from one active
residual data record, with no independent bridge assumptions. -/
theorem all_tripod_bridges :
    (LinearMap.range R.v ⊔ LinearMap.range R.r ≤ R.U₃ ⊔ (R.U₁ ⊓ R.U₂)) ∧
    (LinearMap.range R.v ⊔ LinearMap.range R.r ≤ R.U₂ ⊔ (R.U₃ ⊓ R.U₁)) ∧
    (LinearMap.range R.v ⊔ LinearMap.range R.r ≤ R.U₁ ⊔ (R.U₂ ⊓ R.U₃)) := by
  refine ⟨tripod_le_signal_sup_inter R,?_,?_⟩
  · have hh := tripod_le_signal_sup_inter (rotate R)
    rw [rotate_tripod_range] at hh
    exact hh
  · have hh := tripod_le_signal_sup_inter (rotate (rotate R))
    rw [rotate_tripod_range,rotate_tripod_range] at hh
    exact hh

/-- Inclusion in a sum gives an actual deterministic decoder for observations,
without choosing source or row bases. The observation codomain W can be K^n. -/
theorem exists_observation_decoder {W : Type*} [AddCommGroup W] [Module K W]
    (A B C : Submodule K F) (h : C ≤ A ⊔ B) :
    ∃ dec : (A →ₗ[K] W) → (B →ₗ[K] W) → (C →ₗ[K] W),
      ∀ x : F →ₗ[K] W, dec (x.comp A.subtype) (x.comp B.subtype) = x.comp C.subtype := by
  apply (exists_decoder_iff_fibers _ _ _).mpr
  intro x y ha hb
  ext c
  obtain ⟨a, ha', b, hb', hab⟩ := Submodule.mem_sup.mp (h c.property)
  have ea := LinearMap.congr_fun ha ⟨a, ha'⟩
  have eb := LinearMap.congr_fun hb ⟨b, hb'⟩
  change x (c : F) = y (c : F)
  rw [← hab, map_add, map_add]
  exact congrArg₂ (· + ·) ea eb

/-- An intersection observation is a genuine common function of both signal
observations; this does not assert a rank formula for projected demands. -/
theorem common_observation {W Z Y₁ Y₂ : Type*} [AddCommGroup W] [Module K W]
    (m : (F →ₗ[K] W) → Z) (t₁ : (F →ₗ[K] W) → Y₁)
    (t₂ : (F →ₗ[K] W) → Y₂)
    (u₁ : Z → Y₁ → (R.U₁ →ₗ[K] W)) (u₂ : Z → Y₂ → (R.U₂ →ₗ[K] W))
    (h₁ : ∀ x, u₁ (m x) (t₁ x) = x.comp R.U₁.subtype)
    (h₂ : ∀ x, u₂ (m x) (t₂ x) = x.comp R.U₂.subtype) :
    (∃ c₁ : Z → Y₁ → ((↥(R.U₁ ⊓ R.U₂)) →ₗ[K] W),
      ∀ x, c₁ (m x) (t₁ x) = x.comp (R.U₁ ⊓ R.U₂).subtype) ∧
    (∃ c₂ : Z → Y₂ → ((↥(R.U₁ ⊓ R.U₂)) →ₗ[K] W),
      ∀ x, c₂ (m x) (t₂ x) = x.comp (R.U₁ ⊓ R.U₂).subtype) := by
  constructor
  · refine ⟨fun z t => (u₁ z t).comp (Submodule.inclusion inf_le_left), ?_⟩
    intro x
    dsimp only
    rw [h₁]
    rfl
  · refine ⟨fun z t => (u₂ z t).comp (Submodule.inclusion inf_le_right), ?_⟩
    intro x
    dsimp only
    rw [h₂]
    rfl

/-- The third-user recovery in `bridge-third-recovery` follows from the proven
intersection inclusion. M can be the entire nonlinear upload tuple. -/
theorem exists_bridge_decoder {W Z Y₃ : Type*} [AddCommGroup W] [Module K W]
    (m : (F →ₗ[K] W) → Z) (t₃ : (F →ₗ[K] W) → Y₃)
    (u₃ : Z → Y₃ → (R.U₃ →ₗ[K] W))
    (h₃ : ∀ x, u₃ (m x) (t₃ x) = x.comp R.U₃.subtype) :
    ∃ dec : Z → ((↥(R.U₁ ⊓ R.U₂)) →ₗ[K] W) → Y₃ →
        ((↥(LinearMap.range R.v ⊔ LinearMap.range R.r)) →ₗ[K] W),
      ∀ x, dec (m x) (x.comp (R.U₁ ⊓ R.U₂).subtype) (t₃ x) =
        x.comp (LinearMap.range R.v ⊔ LinearMap.range R.r).subtype := by
  obtain ⟨d, hd⟩ := exists_observation_decoder (W := W) R.U₃ (R.U₁ ⊓ R.U₂)
    (LinearMap.range R.v ⊔ LinearMap.range R.r) (tripod_le_signal_sup_inter R)
  refine ⟨fun z θ t => d (u₃ z t) θ, ?_⟩
  intro x
  dsimp only
  rw [h₃]
  exact hd x

/-- Private-slice inversion from zero error itself. A projection isolates the
private block, all other users' sides annihilate it, and their projected
signals span it. Thus the user's own upload and its nonprivate side determine
its entire side observation, even for nonlinear codes. -/
theorem private_slice_inverse {n : ℕ} {M : Three → Type*} {S : Type*}
    (task : Task K F) (code : task.Code n M S) (i : Three)
    (P T₀ : Submodule K F) (π : F →ₗ[K] P)
    (hπP : ∀ p : P, π p = p)
    (hπT : ∀ t ∈ T₀, π t = 0)
    (hAi : task.A i = P ⊔ T₀)
    (hothers : ∀ j, j ≠ i → ∀ a ∈ task.A j, π a = 0)
    (hremote : (⨆ j : {j : Three // j ≠ i}, (task.U j.val).map π) = ⊤) :
    ∃ slice : M i → Source K T₀ n → Source K (task.A i) n,
      ∀ x, slice (code.encode i (observe K F (task.A i) x)) (observe K F T₀ x) =
        observe K F (task.A i) x := by
  classical
  apply (exists_decoder_iff_fibers _ _ _).mpr
  intro x y hm ht
  let d : P →ₗ[K] (Fin n → K) := (y-x).comp P.subtype
  let z : Source K F n := x + d.comp π
  have hzAi : observe K F (task.A i) z = observe K F (task.A i) y := by
    apply LinearMap.ext
    intro a
    obtain ⟨p,hp,t,ht',ha⟩ := Submodule.mem_sup.mp (show (a:F) ∈ P ⊔ T₀ by rw [← hAi]; exact a.property)
    have hpt : π p = ⟨p,hp⟩ := hπP ⟨p,hp⟩
    have he := LinearMap.congr_fun ht ⟨t,ht'⟩
    change x t = y t at he
    change x (a:F) + d (π (a:F)) = y (a:F)
    rw [← ha, map_add, map_add, map_add, hpt, hπT _ ht', map_zero, add_zero, map_add]
    change x p + x t + (y p - x p) = y p + y t
    rw [he]
    abel
  have hzOther (j : Three) (hj : j ≠ i) :
      observe K F (task.A j) z = observe K F (task.A j) x := by
    apply LinearMap.ext
    intro a
    change x (a:F) + d (π (a:F)) = x (a:F)
    rw [hothers j hj _ a.property, map_zero, add_zero]
  have messages : (fun j => code.encode j (observe K F (task.A j) z)) =
      (fun j => code.encode j (observe K F (task.A j) x)) := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [hzAi]
      exact hm.symm
    · rw [hzOther j hj]
  have hd : d = 0 := by
    have hk : (⊤ : Submodule K P) ≤ LinearMap.ker d := by
      rw [← hremote]
      apply iSup_le
      intro j p hp
      obtain ⟨u,hu,rfl⟩ := hp
      have he : observe K F (task.U j.val) z = observe K F (task.U j.val) x := by
        rw [← code.zero_error z j.val, ← code.zero_error x j.val, messages,
          hzOther j.val j.property]
      have hv := LinearMap.congr_fun he ⟨u,hu⟩
      change x u + d (π u) = x u at hv
      exact add_left_cancel (hv.trans (add_zero (x u)).symm)
    apply LinearMap.ext
    intro p
    exact hk (Submodule.mem_top)
  have hz : z = x := by
    dsimp [z]
    rw [hd, LinearMap.zero_comp, add_zero]
  simpa only [hz] using hzAi

/-- Applying an actual zero-error code after local slice inversion gives the
signal decoders consumed above. This includes arbitrary nonlinear encoders,
broadcasts and decoders and every blocklength. -/
theorem signalRecovery_from_slice {n : ℕ} {M : Three → Type*} {S Y : Type*}
    (task : Task K F) (code : task.Code n M S) (i : Three)
    (ti : Source K F n → Y)
    (slice : M i → Y → Source K (task.A i) n)
    (hslice : ∀ x, slice (code.encode i (observe K F (task.A i) x)) (ti x) =
      observe K F (task.A i) x) :
    ∃ u : (∀ j, M j) → Y → Source K (task.U i) n,
      ∀ x, u (fun j => code.encode j (observe K F (task.A j) x)) (ti x) =
        observe K F (task.U i) x := by
  refine ⟨fun m t => code.decode i (code.broadcast m) (slice (m i) t), ?_⟩
  intro x
  dsimp only
  rw [hslice]
  exact code.zero_error x i

end SignalBridge
end UploadBroadcast
