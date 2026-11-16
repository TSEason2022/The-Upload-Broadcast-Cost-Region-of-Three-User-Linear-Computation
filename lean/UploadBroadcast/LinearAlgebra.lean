import UploadBroadcast.Model
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Abel

/-! Subspace and linear-map lemmas used in the paper's reductions.
These statements do not assert the unformalized coding equivalences. -/
namespace UploadBroadcast

variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The algebraic identity at the start of `lem:pis`. -/
theorem relay_decomposition (A U P : Submodule K F)
    (hAU : A ≤ U) (hUP : U ≤ A ⊔ P) : U = A ⊔ (U ⊓ P) := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a, ha, p, hp, hap⟩ := Submodule.mem_sup.mp (hUP hu)
    have hpU : p ∈ U := by
      have heq : p = u - a := by rw [← hap]; abel
      rw [heq]
      exact U.sub_mem hu (hAU ha)
    exact Submodule.mem_sup.mpr ⟨a, ha, p, ⟨hpU, hp⟩, hap⟩
  · exact sup_le hAU inf_le_left

/-- Adding a map which factors through B cannot change G on ker B;
this is the coordinate-change invariant in `eq:upload-matrices`. -/
theorem gauge_invariance (B : F →ₗ[K] V) (G : F →ₗ[K] W)
    (h : V →ₗ[K] W) (x : F) (hx : x ∈ LinearMap.ker B) :
    (G + h.comp B) x = G x := by
  simp only [LinearMap.mem_ker] at hx
  simp [hx]

/-- The relay restriction contains precisely the locally available
coefficients belonging to that relay. -/
theorem relay_side_le_signal (A U P : Submodule K F) (h : A ≤ U) :
    A ⊓ P ≤ U ⊓ P := inf_le_inf h le_rfl

/-- The induced relay task has the same conditional demand dimension
as the original task (`lem:pis`, sentence immediately following the proof). -/
theorem relay_condRank [FiniteDimensional K F]
    (A U P : Submodule K F) (hAU : A ≤ U) (hUP : U ≤ A ⊔ P) :
    condRank (U ⊓ P) (A ⊓ P) = condRank U A := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A (U ⊓ P)
  have hinf : A ⊓ (U ⊓ P) = A ⊓ P := by
    rw [← inf_assoc, inf_eq_left.mpr hAU]
  rw [← relay_decomposition A U P hAU hUP, hinf] at hdim
  unfold condRank
  rw [sup_eq_right.mpr hAU,
    sup_eq_right.mpr (inf_le_inf hAU le_rfl)]
  omega

/-- A linear map which vanishes on ker B factors through B. This proves
the cancellation assertion immediately before `eq:b`, without assuming
B is surjective. -/
theorem factors_through_of_ker_le (B : F →ₗ[K] V) (G : F →ₗ[K] W)
    (hker : LinearMap.ker B ≤ LinearMap.ker G) :
    ∃ h : V →ₗ[K] W, h.comp B = G := by
  let g : LinearMap.range B →ₗ[K] W :=
    ((LinearMap.ker B).liftQ G hker).comp B.quotKerEquivRange.symm.toLinearMap
  obtain ⟨h, hh⟩ := g.exists_extend
  refine ⟨h, ?_⟩
  ext x
  have he := LinearMap.congr_fun hh (B.rangeRestrict x)
  change h (B x) = ((LinearMap.ker B).liftQ G hker)
    (B.quotKerEquivRange.symm ⟨B x, ⟨x, rfl⟩⟩) at he
  rw [LinearMap.quotKerEquivRange_symm_apply_image] at he
  exact he

/-- Equality of restrictions is exactly the freedom to add a map factoring
through B. This is the precise gauge classification used by the active-row
reduction. -/
theorem equal_on_ker_iff_gauge (B : F →ₗ[K] V) (G G' : F →ₗ[K] W) :
    (∀ x ∈ LinearMap.ker B, G' x = G x) ↔
      ∃ h : V →ₗ[K] W, G' = G + h.comp B := by
  constructor
  · intro h
    have hk : LinearMap.ker B ≤ LinearMap.ker (G' - G) := by
      intro x hx
      simp [LinearMap.mem_ker, h x hx]
    obtain ⟨f, hf⟩ := factors_through_of_ker_le B (G' - G) hk
    refine ⟨f, ?_⟩
    rw [hf]
    abel
  · rintro ⟨h, rfl⟩ x hx
    exact gauge_invariance B G h x hx

/-- The stacked-rank formula `eq:b`: only the restriction of G to ker B
contributes rank beyond B. No rank identities are assumed. -/
theorem rank_restrict_ker [FiniteDimensional K F]
    (B : F →ₗ[K] V) (G : F →ₗ[K] W) :
    Module.finrank K (LinearMap.range (G.comp (LinearMap.ker B).subtype)) =
      Module.finrank K (LinearMap.range (B.prod G)) -
        Module.finrank K (LinearMap.range B) := by
  have hB := B.finrank_range_add_finrank_ker
  have hBG := (B.prod G).finrank_range_add_finrank_ker
  have hG := (G.comp (LinearMap.ker B).subtype).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (G.comp (LinearMap.ker B).subtype) =
      (LinearMap.ker B ⊓ LinearMap.ker G).comap (LinearMap.ker B).subtype := by
    ext x
    simp [LinearMap.mem_ker, x.property]
  have hd := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : LinearMap.ker B ⊓ LinearMap.ker G ≤ LinearMap.ker B)).finrank_eq
  rw [hk, hd] at hG
  rw [LinearMap.ker_prod] at hBG
  omega

/-- Compatible linear observations on two coefficient subspaces extend
to an actual source. This justifies the auxiliary-source step of `lem:pis`. -/
theorem exists_joint_extension (P A : Submodule K F)
    (p : P →ₗ[K] W) (a : A →ₗ[K] W)
    (hpa : ∀ (v : P) (w : A), (v : F) = w → p v = a w) :
    ∃ x : F →ₗ[K] W, x.comp P.subtype = p ∧ x.comp A.subtype = a := by
  let fp : LinearPMap K F W := ⟨P, p⟩
  let fa : LinearPMap K F W := ⟨A, a⟩
  let h : ∀ (v : fp.domain) (w : fa.domain), (v : F) = w → fp v = fa w := hpa
  let f := fp.sup fa h
  obtain ⟨x, hx⟩ := f.toFun.exists_extend
  refine ⟨x, ?_, ?_⟩
  · ext v
    have he := LinearMap.congr_fun hx
      (Submodule.inclusion (LinearPMap.left_le_sup fp fa h).1 v)
    exact he.trans ((LinearPMap.left_le_sup fp fa h).2 rfl).symm
  · ext v
    have he := LinearMap.congr_fun hx
      (Submodule.inclusion (LinearPMap.right_le_sup fp fa h).1 v)
    exact he.trans ((LinearPMap.right_le_sup fp fa h).2 rfl).symm

/-- A change in relay observations vanishing on the side/relay intersection
is realized by a global source change invisible to the side information. -/
theorem exists_extension_zero_on (P A : Submodule K F) (p : P →ₗ[K] W)
    (hp : ∀ z (hz : z ∈ A ⊓ P), p ⟨z, hz.2⟩ = 0) :
    ∃ x : F →ₗ[K] W, x.comp P.subtype = p ∧ x.comp A.subtype = 0 := by
  apply exists_joint_extension P A p 0
  intro v w h
  have hvA : (v : F) ∈ A := h.symm ▸ w.property
  exact hp v ⟨hvA, v.property⟩

/-- Exact zero-error indistinguishability equivalence for an arbitrary
(possibly nonlinear) fixed broadcast function of the relay observations.
By `Function.factorsThrough_iff`, each side is equivalent to existence of
a deterministic decoder. Taking W = K^L proves this at every blocklength.
This is the substantive decoder-equivalence part of `lem:pis`. -/
theorem relay_decoder_fibers {S : Type*} (A U P : Submodule K F)
    (hAU : A ≤ U) (hUP : U ≤ A ⊔ P) (g : (P →ₗ[K] W) → S) :
    (∀ (x y : F →ₗ[K] W),
      g (x.comp P.subtype) = g (y.comp P.subtype) →
      x.comp A.subtype = y.comp A.subtype →
      x.comp U.subtype = y.comp U.subtype) ↔
    (∀ (p q : P →ₗ[K] W), g p = g q →
      (∀ z (hz : z ∈ A ⊓ P), p ⟨z, hz.2⟩ = q ⟨z, hz.2⟩) →
      ∀ z (hz : z ∈ U ⊓ P), p ⟨z, hz.2⟩ = q ⟨z, hz.2⟩) := by
  constructor
  · intro h p q hg ha
    obtain ⟨y, hy⟩ := q.exists_extend
    obtain ⟨d, hdP, hdA⟩ := exists_extension_zero_on P A (p - q) (by
      intro z hz
      simp [ha z hz])
    have hp : (d + y).comp P.subtype = p := by
      rw [LinearMap.add_comp, hdP, hy]
      abel
    have hA : (d + y).comp A.subtype = y.comp A.subtype := by
      rw [LinearMap.add_comp, hdA, zero_add]
    have hU := h (d + y) y (by simpa only [hp, hy] using hg) hA
    intro z hz
    have he := LinearMap.congr_fun hU ⟨z, hz.1⟩
    have hpx := LinearMap.congr_fun hp ⟨z, hz.2⟩
    have hqy := LinearMap.congr_fun hy ⟨z, hz.2⟩
    exact hpx.symm.trans (he.trans hqy)
  · intro h x y hg ha
    have hi := h (x.comp P.subtype) (y.comp P.subtype) hg (by
      intro z hz
      exact LinearMap.congr_fun ha ⟨z, hz.1⟩)
    ext u
    have hu : (u : F) ∈ A ⊔ (U ⊓ P) := by
      rw [← relay_decomposition A U P hAU hUP]
      exact u.property
    obtain ⟨a, haA, p, hp, hap⟩ := Submodule.mem_sup.mp hu
    have hae := LinearMap.congr_fun ha ⟨a, haA⟩
    have hpe := hi p hp
    change x (u : F) = y (u : F)
    rw [← hap, map_add, map_add]
    exact congrArg₂ (· + ·) hae hpe

/-- A deterministic decoder exists exactly when its desired output is
constant on fibers of its two observations. -/
theorem exists_decoder_iff_fibers {X Y Z D : Type*} [Nonempty D]
    (f : X → Y) (a : X → Z) (u : X → D) :
    (∃ d : Y → Z → D, ∀ x, d (f x) (a x) = u x) ↔
      ∀ x y, f x = f y → a x = a y → u x = u y := by
  constructor
  · rintro ⟨d, hd⟩ x y hf ha
    rw [← hd x, ← hd y, hf, ha]
  · intro h
    have hf : Function.FactorsThrough u (fun x => (f x, a x)) := by
      intro x y hxy
      exact h x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
    obtain ⟨d, hd⟩ := (Function.factorsThrough_iff u).mp hf
    exact ⟨fun y z => d (y, z), fun x => (congrFun hd x).symm⟩

/-- Every relay source is the restriction of an original source; hence
restricting to P does not shrink or enlarge the attainable alphabet of g. -/
theorem relay_attainable_range {S : Type*} (P : Submodule K F)
    (g : (P →ₗ[K] W) → S) :
    Set.range (fun x : F →ₗ[K] W => g (x.comp P.subtype)) = Set.range g := by
  apply Set.Subset.antisymm
  · rintro s ⟨x, rfl⟩
    exact ⟨x.comp P.subtype, rfl⟩
  · rintro s ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := p.exists_extend
    exact ⟨x, congrArg g hx⟩

/-- Full deterministic-decoder version of the relay-space reduction
`lem:pis`. The broadcast function is unchanged, its alphabet is unchanged
by `relay_attainable_range`, and W may be the block space K^L. -/
theorem relay_decoder_equivalence {S : Type*} (A U P : Submodule K F)
    (hAU : A ≤ U) (hUP : U ≤ A ⊔ P) (g : (P →ₗ[K] W) → S) :
    (∃ d : S → (A →ₗ[K] W) → (U →ₗ[K] W),
      ∀ x : F →ₗ[K] W, d (g (x.comp P.subtype)) (x.comp A.subtype) =
        x.comp U.subtype) ↔
    (∃ d : S → (↥(A ⊓ P) →ₗ[K] W) → (↥(U ⊓ P) →ₗ[K] W),
      ∀ p : P →ₗ[K] W,
        d (g p) (p.comp (Submodule.inclusion inf_le_right)) =
          p.comp (Submodule.inclusion inf_le_right)) := by
  rw [exists_decoder_iff_fibers, exists_decoder_iff_fibers]
  have hh := relay_decoder_fibers A U P hAU hUP g
  simpa only [LinearMap.ext_iff, Subtype.forall] using hh

/-- An injective linear map exists whenever the finite dimension permits it. -/
theorem exists_injective_linearMap [FiniteDimensional K V] [FiniteDimensional K W]
    (hdim : Module.finrank K V ≤ Module.finrank K W) :
    ∃ f : V →ₗ[K] W, Function.Injective f := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  exact ⟨(Finsupp.linearCombination K v).comp (Module.finBasis K V).repr.toLinearMap,
    hv.finsuppLinearCombination_injective.comp (Module.finBasis K V).repr.injective⟩

/-- Extend an injection on a subspace while retaining injectivity, provided
the target has sufficient dimension. -/
theorem exists_injective_extension [FiniteDimensional K V] [FiniteDimensional K W]
    (P : Submodule K V) (f : P →ₗ[K] W) (hf : Function.Injective f)
    (hdim : Module.finrank K V ≤ Module.finrank K W) :
    ∃ g : V →ₗ[K] W, Function.Injective g ∧ g.comp P.subtype = f := by
  obtain ⟨Q, hPQ⟩ := P.exists_isCompl
  obtain ⟨R, hR⟩ := (LinearMap.range f).exists_isCompl
  have hP := Submodule.finrank_add_eq_of_isCompl hPQ
  have hW := Submodule.finrank_add_eq_of_isCompl hR
  have hfr := f.finrank_range_add_finrank_ker
  simp only [LinearMap.ker_eq_bot.mpr hf, finrank_bot, add_zero] at hfr
  obtain ⟨j, hj⟩ := exists_injective_linearMap
    (K := K) (V := Q) (W := R) (by omega)
  let g := LinearMap.ofIsCompl hPQ f (R.subtype.comp j)
  have hgP : g.comp P.subtype = f := by
    ext p
    exact LinearMap.ofIsCompl_left_apply hPQ p
  have hgQ : g.comp Q.subtype = R.subtype.comp j := by
    ext q
    exact LinearMap.ofIsCompl_right_apply hPQ q
  refine ⟨g, ?_, hgP⟩
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  have hvt : v ∈ P ⊔ Q := by rw [hPQ.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvt
  have he : f ⟨a, ha⟩ + (j ⟨b, hb⟩ : W) = 0 := by
    have hev : g v = 0 := hv
    rw [← hab, map_add] at hev
    rw [show g a = f ⟨a, ha⟩ from LinearMap.congr_fun hgP ⟨a, ha⟩,
      show g b = (j ⟨b, hb⟩ : W) from LinearMap.congr_fun hgQ ⟨b, hb⟩] at hev
    exact hev
  have hfaR : f ⟨a, ha⟩ ∈ R := by
    have heq : f ⟨a, ha⟩ = -(j ⟨b, hb⟩ : W) := eq_neg_of_add_eq_zero_left he
    rw [heq]
    exact R.neg_mem (j ⟨b, hb⟩).property
  have hfa : f ⟨a, ha⟩ = 0 := by
    have hm : f ⟨a, ha⟩ ∈ LinearMap.range f ⊓ R := ⟨⟨⟨a, ha⟩, rfl⟩, hfaR⟩
    rw [hR.disjoint.eq_bot] at hm
    exact hm
  have ha0 : a = 0 := congrArg Subtype.val (hf (hfa.trans f.map_zero.symm))
  have hjb : j ⟨b, hb⟩ = 0 := by
    apply Subtype.ext
    simpa only [hfa, zero_add, Submodule.coe_zero] using he
  have hb0 : b = 0 := congrArg Subtype.val (hj (hjb.trans j.map_zero.symm))
  simpa [ha0, hb0] using hab.symm

/-- A single linear map may be chosen injective on each of two subspaces,
using a target at least as large as each subspace. -/
theorem exists_map_injective_on_pair [FiniteDimensional K F] [FiniteDimensional K W]
    (A B : Submodule K F)
    (hA : Module.finrank K A ≤ Module.finrank K W)
    (hB : Module.finrank K B ≤ Module.finrank K W) :
    ∃ f : F →ₗ[K] W, Function.Injective (f.comp A.subtype) ∧
      Function.Injective (f.comp B.subtype) := by
  obtain ⟨a, ha⟩ := exists_injective_linearMap (K := K) hA
  let P : Submodule K B := A.comap B.subtype
  let i : P →ₗ[K] A :=
    (B.subtype.comp P.subtype).codRestrict A (fun z => z.property)
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : F)) h
  obtain ⟨b, hb, hext⟩ := exists_injective_extension P (a.comp i) (ha.comp hi) hB
  have hab : ∀ (v : A) (w : B), (v : F) = w → a v = b w := by
    intro v w h
    have hw : w ∈ P := by
      change (w : F) ∈ A
      rw [← h]
      exact v.property
    have he := LinearMap.congr_fun hext ⟨w, hw⟩
    change b w = a (i ⟨w, hw⟩) at he
    rw [he]
    congr 1
    exact Subtype.ext h
  obtain ⟨f, hfA, hfB⟩ := exists_joint_extension A B a b hab
  exact ⟨f, hfA ▸ ha, hfB ▸ hb⟩

/-- The separation hypothesis in `lem:binary-common-complement` permits
simultaneous injectivity on three subspaces over every field. -/
theorem exists_map_injective_on_separated_triple
    [FiniteDimensional K F] [FiniteDimensional K W]
    (A B C : Submodule K F) (hdis : Disjoint A (B ⊔ C))
    (hA : Module.finrank K A ≤ Module.finrank K W)
    (hB : Module.finrank K B ≤ Module.finrank K W)
    (hC : Module.finrank K C ≤ Module.finrank K W) :
    ∃ f : F →ₗ[K] W, Function.Injective (f.comp A.subtype) ∧
      Function.Injective (f.comp B.subtype) ∧ Function.Injective (f.comp C.subtype) := by
  obtain ⟨a, ha⟩ := exists_injective_linearMap (K := K) hA
  obtain ⟨bc, hb, hc⟩ := exists_map_injective_on_pair B C hB hC
  have habc : ∀ (v : A) (w : ↥(B ⊔ C)), (v : F) = w →
      a v = (bc.comp (B ⊔ C).subtype) w := by
    intro v w h
    have hv : (v : F) = 0 := by
      have hm : (v : F) ∈ A ⊓ (B ⊔ C) := ⟨v.property, h.symm ▸ w.property⟩
      rw [hdis.eq_bot] at hm
      exact hm
    have hv0 : v = 0 := Subtype.ext hv
    have hw0 : w = 0 := Subtype.ext (h.symm.trans hv)
    simp [hv0, hw0]
  obtain ⟨f, hfA, hfBC⟩ := exists_joint_extension A (B ⊔ C) a
    (bc.comp (B ⊔ C).subtype) habc
  have hfB : f.comp B.subtype = bc.comp B.subtype := by
    ext b
    exact LinearMap.congr_fun hfBC ⟨b, (show B ≤ B ⊔ C from le_sup_left) b.property⟩
  have hfC : f.comp C.subtype = bc.comp C.subtype := by
    ext c
    exact LinearMap.congr_fun hfBC ⟨c, (show C ≤ B ⊔ C from le_sup_right) c.property⟩
  exact ⟨f, hfA ▸ ha, hfB ▸ hb, hfC ▸ hc⟩

/-- Injectivity on a coefficient subspace means that subspace misses the kernel. -/
theorem disjoint_ker_of_restrict_injective (A : Submodule K F)
    (f : F →ₗ[K] W) (hf : Function.Injective (f.comp A.subtype)) :
    Disjoint (LinearMap.ker f) A := by
  rw [Submodule.disjoint_def]
  intro v hv hA
  have hzero : (f.comp A.subtype) ⟨v, hA⟩ = (f.comp A.subtype) 0 := by
    simpa only [map_zero] using hv
  exact congrArg Subtype.val (hf hzero)

/-- A restriction injecting into the range gives the corresponding rank lower bound. -/
theorem finrank_le_range_of_restrict_injective [FiniteDimensional K F]
    (A : Submodule K F) (f : F →ₗ[K] W)
    (hf : Function.Injective (f.comp A.subtype)) :
    Module.finrank K A ≤ Module.finrank K (LinearMap.range f) := by
  apply LinearMap.finrank_le_finrank_of_injective
    (f := f.rangeRestrict.comp A.subtype)
  intro x y h
  exact hf (congrArg (fun z : LinearMap.range f => (z : W)) h)

/-- **A maximum disjoint subspace**, `lem:binary-common-complement`.
The field is arbitrary, including the binary field. The proof constructs a
map injective on all three given subspaces, proves its rank is the maximum
of their dimensions, and takes its kernel. -/
theorem maximum_disjoint_subspace [FiniteDimensional K F]
    (T₁ T₂ T₃ : Submodule K F) (hsep : T₁ ⊓ (T₂ ⊔ T₃) = ⊥) :
    ∃ C : Submodule K F,
      Module.finrank K C = Module.finrank K F -
        max (Module.finrank K T₁) (max (Module.finrank K T₂) (Module.finrank K T₃)) ∧
      C ⊓ T₁ = ⊥ ∧ C ⊓ T₂ = ⊥ ∧ C ⊓ T₃ = ⊥ := by
  let m := max (Module.finrank K T₁)
    (max (Module.finrank K T₂) (Module.finrank K T₃))
  have hdim : Module.finrank K (Fin m → K) = m := by simp
  have h₁ : Module.finrank K T₁ ≤ Module.finrank K (Fin m → K) := by
    rw [hdim]
    exact le_max_left _ _
  have h₂ : Module.finrank K T₂ ≤ Module.finrank K (Fin m → K) := by
    rw [hdim]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : Module.finrank K T₃ ≤ Module.finrank K (Fin m → K) := by
    rw [hdim]
    exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨f, hf₁, hf₂, hf₃⟩ := exists_map_injective_on_separated_triple
    T₁ T₂ T₃ (disjoint_iff.mpr hsep) h₁ h₂ h₃
  have hr₁ := finrank_le_range_of_restrict_injective T₁ f hf₁
  have hr₂ := finrank_le_range_of_restrict_injective T₂ f hf₂
  have hr₃ := finrank_le_range_of_restrict_injective T₃ f hf₃
  have hlo : m ≤ Module.finrank K (LinearMap.range f) :=
    max_le hr₁ (max_le hr₂ hr₃)
  have hhi : Module.finrank K (LinearMap.range f) ≤ m :=
    (LinearMap.range f).finrank_le.trans_eq hdim
  have hr : Module.finrank K (LinearMap.range f) = m := le_antisymm hhi hlo
  have hnull := f.finrank_range_add_finrank_ker
  rw [hr] at hnull
  refine ⟨LinearMap.ker f, ?_,
    (disjoint_ker_of_restrict_injective T₁ f hf₁).eq_bot,
    (disjoint_ker_of_restrict_injective T₂ f hf₂).eq_bot,
    (disjoint_ker_of_restrict_injective T₃ f hf₃).eq_bot⟩
  change Module.finrank K (LinearMap.ker f) = Module.finrank K F - m
  omega

end UploadBroadcast
