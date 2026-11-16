import UploadBroadcast.LinearAlgebra

/-! Original-field noninteractive omniscience construction, source
`lem:ck-omniscience` and Appendix `app:omniscience-code`.
This file constructs linear uploads; numeric rate optimization is separate. -/
namespace UploadBroadcast
namespace Omniscience

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Select exactly n independent coefficient directions. -/
theorem exists_submodule_finrank [FiniteDimensional K V] {n : ℕ}
    (hn : n ≤ Module.finrank K V) :
    ∃ P : Submodule K V, Module.finrank K P = n := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hn
  exact ⟨Submodule.span K (Set.range v), by simpa using finrank_span_eq_card hv⟩

/-- Three prescribed kernel dimensions are attainable with pairwise trivial
intersections exactly under the relevant pair dimension constraints. -/
theorem exists_pairwise_disjoint_subspaces [FiniteDimensional K V]
    (t₁ t₂ t₃ : ℕ)
    (h₁₂ : t₁ + t₂ ≤ Module.finrank K V)
    (h₁₃ : t₁ + t₃ ≤ Module.finrank K V)
    (h₂₃ : t₂ + t₃ ≤ Module.finrank K V) :
    ∃ N₁ N₂ N₃ : Submodule K V,
      Module.finrank K N₁ = t₁ ∧ Module.finrank K N₂ = t₂ ∧
      Module.finrank K N₃ = t₃ ∧
      Disjoint N₁ N₂ ∧ Disjoint N₁ N₃ ∧ Disjoint N₂ N₃ := by
  obtain ⟨N₁, hd₁⟩ := exists_submodule_finrank (K := K) (V := V) (n := t₁) (by omega)
  obtain ⟨R, hR⟩ := N₁.exists_isCompl
  have hdR := Submodule.finrank_add_eq_of_isCompl hR
  obtain ⟨N₂', hd₂'⟩ := exists_submodule_finrank (K := K) (V := R) (n := t₂) (by omega)
  let N₂ := N₂'.map R.subtype
  have hN₂R : N₂ ≤ R := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hd₂ : Module.finrank K N₂ = t₂ := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hd₂'
  have h₁₂' : Disjoint N₁ N₂ := hR.disjoint.mono_right hN₂R
  obtain ⟨C, hdC, hC₁, hC₂, _⟩ := maximum_disjoint_subspace N₁ N₂ ⊥
    (by simpa using h₁₂'.eq_bot)
  simp only [finrank_bot, Nat.max_zero, hd₁, hd₂] at hdC
  obtain ⟨N₃', hd₃'⟩ := exists_submodule_finrank (K := K) (V := C) (n := t₃) (by
    rw [hdC]
    omega)
  let N₃ := N₃'.map C.subtype
  have hN₃C : N₃ ≤ C := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hd₃ : Module.finrank K N₃ = t₃ := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hd₃'
  refine ⟨N₁, N₂, N₃, hd₁, hd₂, hd₃, h₁₂', ?_, ?_⟩
  · exact ((disjoint_iff.mpr hC₁).mono_left hN₃C).symm
  · exact ((disjoint_iff.mpr hC₂).mono_left hN₃C).symm

/-- Realize a chosen kernel in an output of a prescribed (possibly padded)
length. -/
theorem exists_map_with_kernel [FiniteDimensional K V]
    (N : Submodule K V) (r : ℕ)
    (hr : Module.finrank K V - Module.finrank K N ≤ r) :
    ∃ B : V →ₗ[K] (Fin r → K), LinearMap.ker B = N := by
  have hd := N.finrank_quotient_add_finrank
  obtain ⟨j, hj⟩ := exists_injective_linearMap (K := K)
    (V := V ⧸ N) (W := Fin r → K) (by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      omega)
  refine ⟨j.comp N.mkQ, ?_⟩
  rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hj,
    Submodule.comap_bot, Submodule.ker_mkQ]

/-- Pair-stacked full-rank tripod maps B_i, over the original field. -/
theorem exists_tripod_maps [FiniteDimensional K V]
    (r₁ r₂ r₃ : ℕ)
    (h₁₂ : Module.finrank K V ≤ r₁ + r₂)
    (h₁₃ : Module.finrank K V ≤ r₁ + r₃)
    (h₂₃ : Module.finrank K V ≤ r₂ + r₃) :
    ∃ (B₁ : V →ₗ[K] (Fin r₁ → K)) (B₂ : V →ₗ[K] (Fin r₂ → K))
      (B₃ : V →ₗ[K] (Fin r₃ → K)),
      Function.Injective (B₁.prod B₂) ∧ Function.Injective (B₁.prod B₃) ∧
      Function.Injective (B₂.prod B₃) := by
  let c := Module.finrank K V
  obtain ⟨N₁, N₂, N₃, hd₁, hd₂, hd₃, hN₁₂, hN₁₃, hN₂₃⟩ :=
    exists_pairwise_disjoint_subspaces (K := K) (V := V) (c-r₁) (c-r₂) (c-r₃)
      (by dsimp [c]; omega) (by dsimp [c]; omega) (by dsimp [c]; omega)
  obtain ⟨B₁, hB₁⟩ := exists_map_with_kernel N₁ r₁ (by rw [hd₁]; dsimp [c]; omega)
  obtain ⟨B₂, hB₂⟩ := exists_map_with_kernel N₂ r₂ (by rw [hd₂]; dsimp [c]; omega)
  obtain ⟨B₃, hB₃⟩ := exists_map_with_kernel N₃ r₃ (by rw [hd₃]; dsimp [c]; omega)
  refine ⟨B₁, B₂, B₃, ?_, ?_, ?_⟩ <;>
    apply LinearMap.ker_eq_bot.mp
  · rw [LinearMap.ker_prod, hB₁, hB₂, hN₁₂.eq_bot]
  · rw [LinearMap.ker_prod, hB₁, hB₃, hN₁₃.eq_bot]
  · rw [LinearMap.ker_prod, hB₂, hB₃, hN₂₃.eq_bot]

variable {Z : Type*} [AddCommGroup Z] [Module K Z]

/-- Append enough independent columns to an injective tripod map. -/
theorem exists_injective_completion [FiniteDimensional K V]
    [FiniteDimensional K Z] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Injective f)
    (hd : Module.finrank K V + Module.finrank K Z ≤ Module.finrank K W) :
    ∃ g : (V × Z) →ₗ[K] W, Function.Injective g ∧
      g.comp (LinearMap.inl K V Z) = f := by
  let e := LinearEquiv.ofInjective (LinearMap.inl K V Z) LinearMap.inl_injective
  obtain ⟨g, hg, hext⟩ := exists_injective_extension
    (LinearMap.range (LinearMap.inl K V Z)) (f.comp e.symm.toLinearMap)
    (hf.comp e.symm.injective) (by simpa only [Module.finrank_prod] using hd)
  refine ⟨g, hg, ?_⟩
  ext v
  have he := LinearMap.congr_fun hext (e v)
  simpa [e] using he

/-- The new columns are the restriction of the completed map to the
missing pairwise-known block. -/
theorem completion_apply {f : V →ₗ[K] W} {g : (V × Z) →ₗ[K] W}
    (h : g.comp (LinearMap.inl K V Z) = f) (v : V) (z : Z) :
    g (v,z) = f v + (g.comp (LinearMap.inr K V Z)) z := by
  have hv := LinearMap.congr_fun h v
  change g (v, 0) = f v at hv
  calc
    g (v,z) = g ((v,0)+(0,z)) := by simp
    _ = g (v,0) + g (0,z) := g.map_add _ _
    _ = f v + (g.comp (LinearMap.inr K V Z)) z := by rw [hv]; rfl

variable {X₁ X₂ X₃ : Type*}
  [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₂] [Module K X₂]
  [AddCommGroup X₃] [Module K X₃]

/-- The source (v,r,K₁,K₂,K₃) of the omniscience component. -/
abbrev Omega (V X₁ X₂ X₃ : Type*) := V × V × X₁ × X₂ × X₃

def side₁ (x : Omega V X₁ X₂ X₃) : V × X₂ × X₃ :=
  (x.1, x.2.2.2.1, x.2.2.2.2)
def side₂ (x : Omega V X₁ X₂ X₃) : V × X₁ × X₃ :=
  (x.2.1, x.2.2.1, x.2.2.2.2)
def side₃ (x : Omega V X₁ X₂ X₃) : V × X₁ × X₂ :=
  (x.2.1 - x.1, x.2.2.1, x.2.2.2.1)

/-- A noninteractive original-field linear upload code. Each encoder sees
only its own side information. Each decoder receives only that side and the
other two uploads, and recovers the entire source for every source value. -/
structure Code (K V X₁ X₂ X₃ : Type*) [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup X₁] [Module K X₁]
    [AddCommGroup X₂] [Module K X₂]
    [AddCommGroup X₃] [Module K X₃] (r₁ r₂ r₃ : ℕ) where
  encode₁ : (V × X₂ × X₃) →ₗ[K] (Fin r₁ → K)
  encode₂ : (V × X₁ × X₃) →ₗ[K] (Fin r₂ → K)
  encode₃ : (V × X₁ × X₂) →ₗ[K] (Fin r₃ → K)
  decode₁ : (V × X₂ × X₃) → (Fin r₂ → K) → (Fin r₃ → K) → Omega V X₁ X₂ X₃
  decode₂ : (V × X₁ × X₃) → (Fin r₁ → K) → (Fin r₃ → K) → Omega V X₁ X₂ X₃
  decode₃ : (V × X₁ × X₂) → (Fin r₁ → K) → (Fin r₂ → K) → Omega V X₁ X₂ X₃
  zero_error₁ : ∀ x, decode₁ (side₁ x) (encode₂ (side₂ x)) (encode₃ (side₃ x)) = x
  zero_error₂ : ∀ x, decode₂ (side₂ x) (encode₁ (side₁ x)) (encode₃ (side₃ x)) = x
  zero_error₃ : ∀ x, decode₃ (side₃ x) (encode₁ (side₁ x)) (encode₂ (side₂ x)) = x

/-- An upload is the sum of linear transforms of exactly the three locally
known blocks. -/
def localUpload (B : V →ₗ[K] W) (C : X₁ →ₗ[K] W) (D : X₂ →ₗ[K] W) :
    (V × X₁ × X₂) →ₗ[K] W where
  toFun x := B x.1 + C x.2.1 + D x.2.2
  map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' := by intro a x; simp [smul_add]

/-- The integer deficit inequalities suffice for noninteractive linear
omniscience over every field, with precisely the permitted output lengths.
This is the operational construction in `lem:ck-omniscience`; it does not
assume a coding theorem or an abstract achievability oracle. -/
theorem exists_code [FiniteDimensional K V]
    [FiniteDimensional K X₁] [FiniteDimensional K X₂] [FiniteDimensional K X₃]
    (r₁ r₂ r₃ : ℕ)
    (h₁ : Module.finrank K V + Module.finrank K X₁ ≤ r₂ + r₃)
    (h₂ : Module.finrank K V + Module.finrank K X₂ ≤ r₁ + r₃)
    (h₃ : Module.finrank K V + Module.finrank K X₃ ≤ r₁ + r₂) :
    Nonempty (Code K V X₁ X₂ X₃ r₁ r₂ r₃) := by
  obtain ⟨B₁, B₂, B₃, hB₁₂, hB₁₃, hB₂₃⟩ := exists_tripod_maps
    (K := K) (V := V) r₁ r₂ r₃ (by omega) (by omega) (by omega)
  have hB₁₃neg : Function.Injective (B₁.prod (-B₃)) := by
    intro v w h
    apply hB₁₃
    apply Prod.ext
    · have he := congrArg (fun z : (Fin r₁ → K) × (Fin r₃ → K) => z.1) h
      exact he
    · have he := congrArg (fun z : (Fin r₁ → K) × (Fin r₃ → K) => z.2) h
      exact neg_injective he
  obtain ⟨G₁, hG₁inj, hG₁⟩ := exists_injective_completion (Z := X₁)
    (B₂.prod B₃) hB₂₃ (by simpa using h₁)
  obtain ⟨G₂, hG₂inj, hG₂⟩ := exists_injective_completion (Z := X₂)
    (B₁.prod (-B₃)) hB₁₃neg (by simpa using h₂)
  obtain ⟨G₃, hG₃inj, hG₃⟩ := exists_injective_completion (Z := X₃)
    (B₁.prod B₂) hB₁₂ (by simpa using h₃)
  let C₂₁ := (LinearMap.fst K (Fin r₂ → K) (Fin r₃ → K)).comp
    (G₁.comp (LinearMap.inr K V X₁))
  let C₃₁ := (LinearMap.snd K (Fin r₂ → K) (Fin r₃ → K)).comp
    (G₁.comp (LinearMap.inr K V X₁))
  let C₁₂ := (LinearMap.fst K (Fin r₁ → K) (Fin r₃ → K)).comp
    (G₂.comp (LinearMap.inr K V X₂))
  let C₃₂ := (LinearMap.snd K (Fin r₁ → K) (Fin r₃ → K)).comp
    (G₂.comp (LinearMap.inr K V X₂))
  let C₁₃ := (LinearMap.fst K (Fin r₁ → K) (Fin r₂ → K)).comp
    (G₃.comp (LinearMap.inr K V X₃))
  let C₂₃ := (LinearMap.snd K (Fin r₁ → K) (Fin r₂ → K)).comp
    (G₃.comp (LinearMap.inr K V X₃))
  have hform₁ (v : V) (k : X₁) : G₁ (v,k) = (B₂ v+C₂₁ k, B₃ v+C₃₁ k) := by
    simpa [C₂₁, C₃₁] using completion_apply hG₁ v k
  have hform₂ (v : V) (k : X₂) : G₂ (v,k) = (B₁ v+C₁₂ k, -B₃ v+C₃₂ k) := by
    simpa [C₁₂, C₃₂] using completion_apply hG₂ v k
  have hform₃ (v : V) (k : X₃) : G₃ (v,k) = (B₁ v+C₁₃ k, B₂ v+C₂₃ k) := by
    simpa [C₁₃, C₂₃] using completion_apply hG₃ v k
  obtain ⟨D₁, hD₁⟩ := G₁.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hG₁inj)
  obtain ⟨D₂, hD₂⟩ := G₂.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hG₂inj)
  obtain ⟨D₃, hD₃⟩ := G₃.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hG₃inj)
  have recover₁ (v r : V) (k₁ : X₁) (k₂ : X₂) (k₃ : X₃) :
      D₁ (B₂ r+C₂₁ k₁+C₂₃ k₃-C₂₃ k₃,
        B₃ (r-v)+C₃₁ k₁+C₃₂ k₂+B₃ v-C₃₂ k₂) = (r,k₁) := by
    calc
      _ = D₁ (G₁ (r,k₁)) := by
        congr 1
        rw [hform₁]
        apply Prod.ext <;> simp only [map_sub] <;> abel
      _ = (r,k₁) := LinearMap.congr_fun hD₁ (r,k₁)
  have recover₂ (v r : V) (k₁ : X₁) (k₂ : X₂) (k₃ : X₃) :
      D₂ (B₁ v+C₁₂ k₂+C₁₃ k₃-C₁₃ k₃,
        B₃ (r-v)+C₃₁ k₁+C₃₂ k₂-B₃ r-C₃₁ k₁) = (v,k₂) := by
    calc
      _ = D₂ (G₂ (v,k₂)) := by
        congr 1
        rw [hform₂]
        apply Prod.ext <;> simp only [map_sub] <;> abel
      _ = (v,k₂) := LinearMap.congr_fun hD₂ (v,k₂)
  have recover₃ (v r : V) (k₁ : X₁) (k₂ : X₂) (k₃ : X₃) :
      D₃ (B₁ v+C₁₂ k₂+C₁₃ k₃-C₁₂ k₂,
        B₂ r+C₂₁ k₁+C₂₃ k₃-B₂ (r-v)-C₂₁ k₁) = (v,k₃) := by
    calc
      _ = D₃ (G₃ (v,k₃)) := by
        congr 1
        rw [hform₃]
        apply Prod.ext <;> simp only [map_sub] <;> abel
      _ = (v,k₃) := LinearMap.congr_fun hD₃ (v,k₃)
  refine ⟨{
    encode₁ := localUpload B₁ C₁₂ C₁₃
    encode₂ := localUpload B₂ C₂₁ C₂₃
    encode₃ := localUpload B₃ C₃₁ C₃₂
    decode₁ := fun a m₂ m₃ =>
      let missing := D₁ (m₂-C₂₃ a.2.2, m₃+B₃ a.1-C₃₂ a.2.1)
      (a.1, missing.1, missing.2, a.2.1, a.2.2)
    decode₂ := fun a m₁ m₃ =>
      let missing := D₂ (m₁-C₁₃ a.2.2, m₃-B₃ a.1-C₃₁ a.2.1)
      (missing.1, a.1, a.2.1, missing.2, a.2.2)
    decode₃ := fun a m₁ m₂ =>
      let missing := D₃ (m₁-C₁₂ a.2.2, m₂-B₂ a.1-C₂₁ a.2.1)
      (missing.1, missing.1+a.1, a.2.1, a.2.2, missing.2)
    zero_error₁ := ?_
    zero_error₂ := ?_
    zero_error₃ := ?_ }⟩
  · rintro ⟨v,r,k₁,k₂,k₃⟩
    dsimp [side₁, side₂, side₃, localUpload]
    rw [recover₁]
  · rintro ⟨v,r,k₁,k₂,k₃⟩
    dsimp [side₁, side₂, side₃, localUpload]
    rw [recover₂]
  · rintro ⟨v,r,k₁,k₂,k₃⟩
    dsimp [side₁, side₂, side₃, localUpload]
    rw [recover₃]
    simp

/-- Insert a zero side block in the last position. -/
def padLast : (V × X₁) →ₗ[K] (V × X₁ × X₂) where
  toFun x := (x.1,x.2,0)
  map_add' := by intro x y; simp
  map_smul' := by intro a x; simp

/-- Insert a zero side block in the middle position. -/
def padMiddle : (V × X₂) →ₗ[K] (V × X₁ × X₂) where
  toFun x := (x.1,0,x.2)
  map_add' := by intro x y; simp
  map_smul' := by intro a x; simp

/-- The negative tripod coordinate at User 3 when User 2's side is fixed. -/
def negPadMiddle : (V × X₂) →ₗ[K] (V × X₁ × X₂) where
  toFun x := (-x.1,0,x.2)
  map_add' := by intro x y; simp [neg_add, add_comm]
  map_smul' := by intro a x; simp

namespace Code
variable {r₁ r₂ r₃ : ℕ}
variable [FiniteDimensional K V]

/-- User 1's missing (r,K₁) must inject into the other two uploads. -/
theorem deficit₁ [FiniteDimensional K X₁] (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    Module.finrank K V + Module.finrank K X₁ ≤ r₂ + r₃ := by
  let q := (c.encode₂.comp (padLast (K := K))).prod (c.encode₃.comp (padLast (K := K)))
  have hq : Function.Injective q := by
    intro a b h
    have ha := c.zero_error₁ (0,a.1,a.2,0,0)
    have hb := c.zero_error₁ (0,b.1,b.2,0,0)
    have he := congrArg (fun p : (Fin r₂ → K) × (Fin r₃ → K) =>
      c.decode₁ (0,0,0) p.1 p.2) h
    simp only [q, LinearMap.prod_apply, LinearMap.comp_apply, padLast,
      LinearMap.coe_mk, AddHom.coe_mk] at he
    simp only [side₁, side₂, side₃, sub_zero] at ha hb
    have hs := ha.symm.trans (he.trans hb)
    have hfst := congrArg (fun x : Omega V X₁ X₂ X₃ => x.2.1) hs
    have hsnd := congrArg (fun x : Omega V X₁ X₂ X₃ => x.2.2.1) hs
    exact Prod.ext hfst hsnd
  have hd := LinearMap.finrank_le_finrank_of_injective hq
  simpa using hd

/-- User 2's missing (v,K₂) must inject into the other two uploads. -/
theorem deficit₂ [FiniteDimensional K X₂] (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    Module.finrank K V + Module.finrank K X₂ ≤ r₁ + r₃ := by
  let q := (c.encode₁.comp (padLast (K := K))).prod
    (c.encode₃.comp (negPadMiddle (K := K)))
  have hq : Function.Injective q := by
    intro a b h
    have ha := c.zero_error₂ (a.1,0,0,a.2,0)
    have hb := c.zero_error₂ (b.1,0,0,b.2,0)
    have he := congrArg (fun p : (Fin r₁ → K) × (Fin r₃ → K) =>
      c.decode₂ (0,0,0) p.1 p.2) h
    simp only [q, LinearMap.prod_apply, LinearMap.comp_apply, padLast, negPadMiddle,
      LinearMap.coe_mk, AddHom.coe_mk] at he
    simp only [side₁, side₂, side₃, zero_sub] at ha hb
    have hs := ha.symm.trans (he.trans hb)
    have hfst := congrArg (fun x : Omega V X₁ X₂ X₃ => x.1) hs
    have hsnd := congrArg (fun x : Omega V X₁ X₂ X₃ => x.2.2.2.1) hs
    exact Prod.ext hfst hsnd
  have hd := LinearMap.finrank_le_finrank_of_injective hq
  simpa using hd

/-- User 3's missing (v,K₃) must inject into the other two uploads. -/
theorem deficit₃ [FiniteDimensional K X₃] (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    Module.finrank K V + Module.finrank K X₃ ≤ r₁ + r₂ := by
  let q := (c.encode₁.comp (padMiddle (K := K))).prod
    (c.encode₂.comp (padMiddle (K := K)))
  have hq : Function.Injective q := by
    intro a b h
    have ha := c.zero_error₃ (a.1,a.1,0,0,a.2)
    have hb := c.zero_error₃ (b.1,b.1,0,0,b.2)
    have he := congrArg (fun p : (Fin r₁ → K) × (Fin r₂ → K) =>
      c.decode₃ (0,0,0) p.1 p.2) h
    simp only [q, LinearMap.prod_apply, LinearMap.comp_apply, padMiddle,
      LinearMap.coe_mk, AddHom.coe_mk] at he
    simp only [side₁, side₂, side₃, sub_self] at ha hb
    have hs := ha.symm.trans (he.trans hb)
    have hfst := congrArg (fun x : Omega V X₁ X₂ X₃ => x.1) hs
    have hsnd := congrArg (fun x : Omega V X₁ X₂ X₃ => x.2.2.2.2) hs
    exact Prod.ext hfst hsnd
  have hd := LinearMap.finrank_le_finrank_of_injective hq
  simpa using hd

/-- Replace each padded upload vector by coordinates on its exact attained
linear image. This preserves decoding and charges only attainable symbols. -/
noncomputable def compress (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    Code K V X₁ X₂ X₃
      (Module.finrank K (LinearMap.range c.encode₁))
      (Module.finrank K (LinearMap.range c.encode₂))
      (Module.finrank K (LinearMap.range c.encode₃)) := by
  let e₁ := (Module.finBasis K (LinearMap.range c.encode₁)).equivFun
  let e₂ := (Module.finBasis K (LinearMap.range c.encode₂)).equivFun
  let e₃ := (Module.finBasis K (LinearMap.range c.encode₃)).equivFun
  exact {
    encode₁ := e₁.toLinearMap.comp c.encode₁.rangeRestrict
    encode₂ := e₂.toLinearMap.comp c.encode₂.rangeRestrict
    encode₃ := e₃.toLinearMap.comp c.encode₃.rangeRestrict
    decode₁ := fun a m₂ m₃ => c.decode₁ a (e₂.symm m₂) (e₃.symm m₃)
    decode₂ := fun a m₁ m₃ => c.decode₂ a (e₁.symm m₁) (e₃.symm m₃)
    decode₃ := fun a m₁ m₂ => c.decode₃ a (e₁.symm m₁) (e₂.symm m₂)
    zero_error₁ := by intro x; simpa using c.zero_error₁ x
    zero_error₂ := by intro x; simpa using c.zero_error₂ x
    zero_error₃ := by intro x; simpa using c.zero_error₃ x }

/-- Deficit inequalities for actual upload ranks, without charging padding. -/
theorem rank_deficits [FiniteDimensional K X₁] [FiniteDimensional K X₂]
    [FiniteDimensional K X₃] (c : Code K V X₁ X₂ X₃ r₁ r₂ r₃) :
    Module.finrank K V + Module.finrank K X₁ ≤
      Module.finrank K (LinearMap.range c.encode₂) + Module.finrank K (LinearMap.range c.encode₃) ∧
    Module.finrank K V + Module.finrank K X₂ ≤
      Module.finrank K (LinearMap.range c.encode₁) + Module.finrank K (LinearMap.range c.encode₃) ∧
    Module.finrank K V + Module.finrank K X₃ ≤
      Module.finrank K (LinearMap.range c.encode₁) + Module.finrank K (LinearMap.range c.encode₂) :=
  ⟨c.compress.deficit₁, c.compress.deficit₂, c.compress.deficit₃⟩

end Code

/-- Exact integer-length feasibility for the omniscience component. -/
theorem nonempty_code_iff [FiniteDimensional K V]
    [FiniteDimensional K X₁] [FiniteDimensional K X₂] [FiniteDimensional K X₃]
    (r₁ r₂ r₃ : ℕ) :
    Nonempty (Code K V X₁ X₂ X₃ r₁ r₂ r₃) ↔
      Module.finrank K V + Module.finrank K X₁ ≤ r₂+r₃ ∧
      Module.finrank K V + Module.finrank K X₂ ≤ r₁+r₃ ∧
      Module.finrank K V + Module.finrank K X₃ ≤ r₁+r₂ := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.deficit₁, c.deficit₂, c.deficit₃⟩
  · rintro ⟨h₁,h₂,h₃⟩
    exact exists_code r₁ r₂ r₃ h₁ h₂ h₃

end Omniscience
end UploadBroadcast
