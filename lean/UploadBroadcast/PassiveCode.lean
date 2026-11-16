import UploadBroadcast.LinearAlgebra
import UploadBroadcast.Profile

/-! Exact nonlinear code transports for a side-only direct summand. -/
namespace UploadBroadcast
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]

/-- Linear data of deleting a side-only summand. These hypotheses concern
coefficient spaces only; no existence of a code or rate equality is assumed.
`reconstruct` says precisely that the deleted part of every demanded
coefficient is already locally known. -/
structure PassiveRetraction (T : Task K F) (R : Task K V) where
  project : F →ₗ[K] V
  embed : V →ₗ[K] F
  project_include : project.comp embed = LinearMap.id
  sideProject : ∀ i, T.A i →ₗ[K] R.A i
  sideInclude : ∀ i, R.A i →ₗ[K] T.A i
  signalProject : ∀ i, T.U i →ₗ[K] R.U i
  signalInclude : ∀ i, R.U i →ₗ[K] T.U i
  localPart : ∀ i, T.U i →ₗ[K] T.A i
  sideProject_coe : ∀ i a, (sideProject i a : V) = project a
  sideInclude_coe : ∀ i a, (sideInclude i a : F) = embed a
  signalProject_coe : ∀ i u, (signalProject i u : V) = project u
  signalInclude_coe : ∀ i u, (signalInclude i u : F) = embed u
  reconstruct : ∀ i (u : T.U i), embed (project (u : F)) + (localPart i u : F) = u

/-- Build deletion data directly from a split ambient projection. The final
hypothesis is exactly the side-only condition on the removed coefficients. -/
def passiveRetractionOfProjection (T : Task K F) (R : Task K V)
    (p : F →ₗ[K] V) (e : V →ₗ[K] F) (hpe : p.comp e = LinearMap.id)
    (hpa : ∀ i x, x ∈ T.A i → p x ∈ R.A i)
    (hea : ∀ i x, x ∈ R.A i → e x ∈ T.A i)
    (hpu : ∀ i x, x ∈ T.U i → p x ∈ R.U i)
    (heu : ∀ i x, x ∈ R.U i → e x ∈ T.U i)
    (hl : ∀ i x, x ∈ T.U i → x - e (p x) ∈ T.A i) :
    PassiveRetraction T R where
  project := p
  embed := e
  project_include := hpe
  sideProject i := (p.comp (T.A i).subtype).codRestrict (R.A i)
    (fun x => hpa i x x.property)
  sideInclude i := (e.comp (R.A i).subtype).codRestrict (T.A i)
    (fun x => hea i x x.property)
  signalProject i := (p.comp (T.U i).subtype).codRestrict (R.U i)
    (fun x => hpu i x x.property)
  signalInclude i := (e.comp (R.U i).subtype).codRestrict (T.U i)
    (fun x => heu i x x.property)
  localPart i := ((LinearMap.id - e.comp p).comp (T.U i).subtype).codRestrict
    (T.A i) (fun x => hl i x x.property)
  sideProject_coe _ _ := rfl
  sideInclude_coe _ _ := rfl
  signalProject_coe _ _ := rfl
  signalInclude_coe _ _ := rfl
  reconstruct i u := by
    change e (p (u : F)) + ((u : F) - e (p (u : F))) = u
    abel

namespace PassiveRetraction
variable {T : Task K F} {R : Task K V} (r : PassiveRetraction T R)
  {L : ℕ} {M : Three → Type*} {S : Type*}

/-- Fix every passive source symbol to zero. Works for nonlinear codes. -/
def delete (c : T.Code L M S) : R.Code L M S where
  encode i a := c.encode i (a.comp (r.sideProject i))
  broadcast := c.broadcast
  decode i b a := (c.decode i b (a.comp (r.sideProject i))).comp (r.signalInclude i)
  zero_error x i := by
    have hA : ∀ j, (observe K V (R.A j) x).comp (r.sideProject j) =
        observe K F (T.A j) (x.comp r.project) := by
      intro j
      ext a k
      change x (r.sideProject j a : V) k = x (r.project a) k
      rw [r.sideProject_coe]
    simp only [hA]
    rw [c.zero_error]
    ext u k
    change x (r.project (r.signalInclude i u : F)) k = x (u : V) k
    rw [r.signalInclude_coe]
    have h := LinearMap.congr_fun r.project_include (u : V)
    rw [show r.project (r.embed (u : V)) = u from h]

/-- Ignore passive symbols in uploads and restore their demanded parts
from local side information. No linearity of c is used. -/
def restore (c : R.Code L M S) : T.Code L M S where
  encode i a := c.encode i (a.comp (r.sideInclude i))
  broadcast := c.broadcast
  decode i b a := ((c.decode i b (a.comp (r.sideInclude i))).comp
    (r.signalProject i)) + a.comp (r.localPart i)
  zero_error x i := by
    have hA : ∀ j, (observe K F (T.A j) x).comp (r.sideInclude j) =
        observe K V (R.A j) (x.comp r.embed) := by
      intro j
      ext a k
      change x (r.sideInclude j a : F) k = x (r.embed a) k
      rw [r.sideInclude_coe]
    simp only [hA]
    rw [c.zero_error]
    ext u k
    change x (r.embed (r.signalProject i u : V)) k + x (r.localPart i u : F) k = x (u : F) k
    rw [r.signalProject_coe, ← Pi.add_apply, ← map_add, r.reconstruct]

/-- Deletion never enlarges any individual attainable upload alphabet. -/
theorem delete_upload_range (c : T.Code L M S) (i : Three) :
    Set.range ((r.delete c).encode i) ⊆ Set.range (c.encode i) := by
  rintro m ⟨a, rfl⟩
  exact ⟨a.comp (r.sideProject i), rfl⟩

/-- Deletion never enlarges the attainable broadcast alphabet. -/
theorem delete_broadcast_range (c : T.Code L M S) :
    Set.range (r.delete c).transmitted ⊆ Set.range c.transmitted := by
  rintro b ⟨x, rfl⟩
  refine ⟨x.comp r.project, ?_⟩
  unfold Task.Code.transmitted delete
  congr 1
  funext i
  congr 1
  ext a k
  change x (r.project (a : F)) k = x (r.sideProject i a : V) k
  rw [r.sideProject_coe]

/-- Restoring the passive summand never enlarges upload alphabets. -/
theorem restore_upload_range (c : R.Code L M S) (i : Three) :
    Set.range ((r.restore c).encode i) ⊆ Set.range (c.encode i) := by
  rintro m ⟨a, rfl⟩
  exact ⟨a.comp (r.sideInclude i), rfl⟩

/-- Restoring the passive summand never enlarges broadcast alphabets. -/
theorem restore_broadcast_range (c : R.Code L M S) :
    Set.range (r.restore c).transmitted ⊆ Set.range c.transmitted := by
  rintro b ⟨x, rfl⟩
  refine ⟨x.comp r.embed, ?_⟩
  unfold Task.Code.transmitted restore
  congr 1
  funext i
  congr 1
  ext a k
  change x (r.embed (a : V)) k = x (r.sideInclude i a : F) k
  rw [r.sideInclude_coe]

private theorem log_range_mono {X Y Z : Type*} [Nonempty X] [Finite Z]
    (f : X → Z) (g : Y → Z) (h : Set.range f ⊆ Set.range g)
    (q : ℝ) (hq : 1 < q) :
    Real.logb q (Nat.card (Set.range f)) ≤ Real.logb q (Nat.card (Set.range g)) := by
  apply Real.logb_le_logb_of_le hq
  · exact_mod_cast (Nat.card_pos (α := Set.range f))
  · exact_mod_cast Nat.card_le_card_of_injective
      (Set.inclusion h) (Set.inclusion_injective h)

variable [Finite K] [FiniteDimensional K F] [FiniteDimensional K V]

private theorem field_card_gt_one : (1 : ℝ) < Nat.card K := by
  have h := Nat.card_le_card_of_injective (fun b : Bool => if b then (1 : K) else 0) (by
    intro a b h
    cases a <;> cases b <;> simp_all)
  have hn : 1 < Nat.card K := by simpa using h
  exact_mod_cast hn

include r

/-- Concrete code transformations prove preservation of every fixed-block
budget region, including for all nonlinear codes. -/
theorem achievableAt_eq (L : ℕ) : T.achievableAt L = R.achievableAt L := by
  ext b
  constructor
  · rintro ⟨hL, hu, hd, m, s, c, hcu, hcd⟩
    refine ⟨hL, hu, hd, m, s, r.delete c, le_trans ?_ hcu, le_trans ?_ hcd⟩
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      apply Finset.sum_le_sum
      intro i _
      exact log_range_mono _ _ (r.delete_upload_range c i) _ field_card_gt_one
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      exact log_range_mono _ _ (r.delete_broadcast_range c) _ field_card_gt_one
  · rintro ⟨hL, hu, hd, m, s, c, hcu, hcd⟩
    refine ⟨hL, hu, hd, m, s, r.restore c, le_trans ?_ hcu, le_trans ?_ hcd⟩
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      apply Finset.sum_le_sum
      intro i _
      exact log_range_mono _ _ (r.restore_upload_range c i) _ field_card_gt_one
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      exact log_range_mono _ _ (r.restore_broadcast_range c) _ field_card_gt_one

theorem costRegion_eq : T.costRegion = R.costRegion := by
  unfold Task.costRegion
  simp_rw [r.achievableAt_eq]

end PassiveRetraction
/-- Every side-only direct summand, with arbitrary overlap between the
three passive side-information spaces, supplies the required projection. -/
def sideOnlyDirectSumRetraction (T : Task K F) (S : Task K V)
    (hS : ∀ i, S.U i = S.A i) :
    PassiveRetraction (Profile.directSum T S) T :=
  passiveRetractionOfProjection (Profile.directSum T S) T
    (LinearMap.fst K F V) (LinearMap.inl K F V) (by ext; rfl)
    (by intro i x hx; exact hx.1)
    (by intro i x hx; exact ⟨hx, (S.A i).zero_mem⟩)
    (by intro i x hx; exact hx.1)
    (by intro i x hx; exact ⟨hx, (S.U i).zero_mem⟩)
    (by
      intro i x hx
      constructor
      · simp
      · simpa [hS i] using hx.2)

/-- Exact operational statement: deleting a side-only direct summand
preserves every fixed-block rate region, with no linear-code restriction. -/
theorem sideOnly_achievableAt_eq [Finite K]
    [FiniteDimensional K F] [FiniteDimensional K V]
    (T : Task K F) (S : Task K V) (hS : ∀ i, S.U i = S.A i) (L : ℕ) :
    (Profile.directSum T S).achievableAt L = T.achievableAt L :=
  (sideOnlyDirectSumRetraction T S hS).achievableAt_eq L

end UploadBroadcast
