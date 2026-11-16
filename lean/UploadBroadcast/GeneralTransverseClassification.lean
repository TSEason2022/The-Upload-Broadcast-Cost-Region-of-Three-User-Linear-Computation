import UploadBroadcast.ResonantFlagNormalization
import UploadBroadcast.MarkedSubspace
import UploadBroadcast.TaskQuiverBridge

/-!
# Classification from actual transverse flags

The tripod multiplicity is not assumed to be one. In diagonal coordinates,
its multiplicity is the dimension of the kernel of a surjection. Marked
nilpotent indecomposability forces that kernel to be one-dimensional.
-/
namespace UploadBroadcast.GeneralTransverseClassification
open TaskDecomposition ResonantFlagNormalization
variable {K Z Y F : Type*} [Field K]
  [AddCommGroup Z] [Module K Z] [AddCommGroup Y] [Module K Y]
  [AddCommGroup F] [Module K F]

def diagonalA : Submodule K (Z × Z × Y) where
  carrier := {p | p.2.1 = 0 ∧ p.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def diagonalB : Submodule K (Z × Z × Y) where
  carrier := {p | p.1 = 0 ∧ p.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def diagonalC (L : Z →ₗ[K] Y) : Submodule K (Z × Z × Y) where
  carrier := {p | p.2.1 = p.1 ∧ p.2.2 = L p.1}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq; simp_all
  smul_mem' := by intro a p hp; simp_all

def diagonalU : Submodule K (Z × Z × Y) :=
  LinearMap.ker ((LinearMap.fst K Z Y).comp (LinearMap.snd K Z (Z × Y)))
def diagonalV : Submodule K (Z × Z × Y) := LinearMap.ker (LinearMap.fst K Z (Z × Y))

def diagonalW (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z) : Submodule K (Z × Z × Y) where
  carrier := {p | p.2.1 = p.1 + T (p.2.2 - L p.1)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change p.2.1 + q.2.1 = p.1 + q.1 + T (p.2.2 + q.2.2 - L (p.1 + q.1))
    rw [map_add, show p.2.2 + q.2.2 - (L p.1 + L q.1) =
      (p.2.2 - L p.1) + (q.2.2 - L q.1) by abel, map_add, hp, hq]
    abel
  smul_mem' := by intro a p hp; simpa [smul_sub, smul_add] using congrArg (a • ·) hp

def diagonalSpaces (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z) : Fin 6 → Submodule K (Z × Z × Y) :=
  ![diagonalA, diagonalB, diagonalC L, diagonalU, diagonalV, diagonalW L T]

def diagonalEnd (P : Module.End K Z) (Q : Module.End K Y) : Module.End K (Z × Z × Y) :=
  P.prodMap (P.prodMap Q)

lemma diagonalEnd_stable (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z)
    (P : Module.End K Z) (Q : Module.End K Y)
    (hL : ∀ z, L (P z) = Q (L z)) (hT : ∀ y, P (T y) = T (Q y)) :
    Stable (diagonalSpaces L T) (diagonalEnd P Q) := by
  intro i p hp
  fin_cases i
  · change p.2.1 = 0 ∧ p.2.2 = 0 at hp
    change P p.2.1 = 0 ∧ Q p.2.2 = 0
    simp [hp.1,hp.2]
  · change p.1 = 0 ∧ p.2.2 = 0 at hp
    change P p.1 = 0 ∧ Q p.2.2 = 0
    simp [hp.1,hp.2]
  · change p.2.1 = p.1 ∧ p.2.2 = L p.1 at hp
    change P p.2.1 = P p.1 ∧ Q p.2.2 = L (P p.1)
    simp [hp.1,hp.2,hL]
  · change p.2.1 = 0 at hp
    change P p.2.1 = 0
    simp [hp]
  · change p.1 = 0 at hp
    change P p.1 = 0
    simp [hp]
  · change p.2.1 = p.1 + T (p.2.2 - L p.1) at hp
    change P p.2.1 = P p.1 + T (Q p.2.2 - L (P p.1))
    rw [hp,map_add,hT,hL,map_sub]

lemma diagonalEnd_pow_first (P : Module.End K Z) (Q : Module.End K Y)
    (n : ℕ) (p : Z × Z × Y) : ((diagonalEnd P Q ^ n) p).1 = (P ^ n) p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change P (((diagonalEnd P Q) ^ n) p).1 = P ((P ^ n) p.1)
    rw [ih]

/-- The diagonal operator kills the whole tripod kernel, so it cannot be a unit. -/
theorem diagonal_operator_nilpotent [Finite K] [FiniteDimensional K Z] [FiniteDimensional K Y]
    (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z)
    (hk : LinearMap.ker L ≠ ⊥) (hi : Indecomposable (diagonalSpaces L T) ⊤) :
    IsNilpotent (T.comp L) := by
  let P := T.comp L
  let Q := L.comp T
  let f : stableEnd (diagonalSpaces L T) := ⟨diagonalEnd P Q,
    diagonalEnd_stable L T P Q (fun _ => rfl) (fun _ => rfl)⟩
  obtain hn | hu := stableEnd.nilpotent_or_unit hi f
  · obtain ⟨n,hn⟩ := hn
    refine ⟨n, LinearMap.ext fun z => ?_⟩
    have hh := congrArg (fun g : stableEnd (diagonalSpaces L T) =>
      ((g : Module.End K (Z × Z × Y)) (z,0,0)).1) hn
    change ((diagonalEnd P Q ^ n) (z,0,0)).1 = 0 at hh
    simpa only [diagonalEnd_pow_first] using hh
  · obtain ⟨z,hz,hzne⟩ := (Submodule.ne_bot_iff _).mp hk
    obtain ⟨u,hu⟩ := hu
    have hz' : (f : Module.End K (Z × Z × Y)) (z,0,0) = 0 := by
      change (T (L z), T (L 0), L (T 0)) = 0
      simp [show L z = 0 from hz]
    have hh : ((↑u⁻¹ : stableEnd (diagonalSpaces L T)) : Module.End K (Z × Z × Y))
        ((f : Module.End K (Z × Z × Y)) (z,0,0)) = (z,0,0) := by
      rw [← hu]
      exact congrArg (fun g : stableEnd (diagonalSpaces L T) =>
        (g : Module.End K (Z × Z × Y)) (z,0,0)) (Units.inv_mul u)
    rw [hz',map_zero] at hh
    exact False.elim (hzne (congrArg Prod.fst hh).symm)

/-- A marked endomorphism descends along the surjection and preserves its graph. -/
theorem descend_marked_end (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z)
    (hs : Function.Surjective L) (P : Module.End K Z)
    (hc : Commute P (T.comp L)) (hk : ∀ z ∈ LinearMap.ker L, P z ∈ LinearMap.ker L) :
    ∃ Q : Module.End K Y, (∀ z, L (P z) = Q (L z)) ∧ (∀ y, P (T y) = T (Q y)) := by
  obtain ⟨t,ht⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  have hLt (y : Y) : L (t y) = y := LinearMap.congr_fun ht y
  let Q := L.comp (P.comp t)
  have hL (z : Z) : L (P z) = Q (L z) := by
    have hz : z-t (L z) ∈ LinearMap.ker L := by
      change L (z-t (L z)) = 0
      simp [hLt]
    have hp := hk _ hz
    change L (P (z-t (L z))) = 0 at hp
    simpa only [map_sub, sub_eq_zero] using hp
  refine ⟨Q,hL,?_⟩
  intro y
  obtain ⟨z,rfl⟩ := hs y
  rw [← hL]
  exact LinearMap.congr_fun hc.eq z

/-- All marked commuting projections are trivial, by lifting them to the flags. -/
theorem marked_projections_trivial (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z)
    (hs : Function.Surjective L) (hi : Indecomposable (diagonalSpaces L T) ⊤)
    (P : Module.End K Z) (hc : Commute P (T.comp L))
    (hk : ∀ z ∈ LinearMap.ker L, P z ∈ LinearMap.ker L)
    (hid : ∀ z, P (P z) = P z) : P = 0 ∨ P = 1 := by
  obtain ⟨Q,hL,hT⟩ := descend_marked_end L T hs P hc hk
  have hQ (y : Y) : Q (Q y) = Q y := by
    obtain ⟨z,rfl⟩ := hs y
    rw [← hL,← hL,hid]
  obtain hz | ho := hi.projection_eq_zero_or_id (diagonalEnd P Q)
    (diagonalEnd_stable L T P Q hL hT)
    (by intro p; exact Prod.ext (hid _) (Prod.ext (hid _) (hQ _)))
  · left
    exact LinearMap.ext fun z => congrArg Prod.fst (LinearMap.congr_fun hz (z,0,0))
  · right
    exact LinearMap.ext fun z => congrArg Prod.fst (LinearMap.congr_fun ho (z,0,0))

/-- Arbitrary positive tripod multiplicity collapses to one. -/
theorem tripod_kernel_finrank_one [Finite K] [FiniteDimensional K Z] [FiniteDimensional K Y]
    (L : Z →ₗ[K] Y) (T : Y →ₗ[K] Z) (hs : Function.Surjective L)
    (hk : LinearMap.ker L ≠ ⊥) (hi : Indecomposable (diagonalSpaces L T) ⊤) :
    Module.finrank K (LinearMap.ker L) = 1 := by
  obtain ⟨_,_,hr⟩ := MarkedSubspace.single_chain_and_marked_kernel (T.comp L)
    (diagonal_operator_nilpotent L T hk hi) (LinearMap.ker L) hk
    (by intro z hz; change T (L z) = 0; rw [show L z = 0 from hz,map_zero])
    (marked_projections_trivial L T hs hi)
  exact hr


lemma finrank_add_le_of_disjoint [FiniteDimensional K F]
    (A U : Submodule K F) (h : Disjoint A U) :
    Module.finrank K A + Module.finrank K U ≤ Module.finrank K F := by
  have he := Submodule.finrank_sup_add_finrank_inf_eq A U
  rw [h.eq_bot,finrank_bot,add_zero] at he
  rw [← he]
  exact Submodule.finrank_le _

/-- The six transverse inequalities and zero defect force all side dimensions
and all enlarged dimensions to agree, with every cross pair complementary. -/
theorem transverse_dimension_equalities [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hzero : Module.finrank K U + Module.finrank K V + Module.finrank K W +
      Module.finrank K A + Module.finrank K B + Module.finrank K C = 3*Module.finrank K F)
    (hAV : Disjoint A V) (hAW : Disjoint A W) (hBU : Disjoint B U)
    (hBW : Disjoint B W) (hCU : Disjoint C U) (hCV : Disjoint C V) :
    Module.finrank K A = Module.finrank K C ∧ Module.finrank K B = Module.finrank K C ∧
    Module.finrank K U = Module.finrank K W ∧ Module.finrank K V = Module.finrank K W ∧
    Module.finrank K C + Module.finrank K W = Module.finrank K F := by
  have h₁ := finrank_add_le_of_disjoint A V hAV
  have h₂ := finrank_add_le_of_disjoint A W hAW
  have h₃ := finrank_add_le_of_disjoint B U hBU
  have h₄ := finrank_add_le_of_disjoint B W hBW
  have h₅ := finrank_add_le_of_disjoint C U hCU
  have h₆ := finrank_add_le_of_disjoint C V hCV
  omega

/-- From arbitrary actual transverse flags, zero defect and positive excess,
indecomposability derives the T₀+nδ dimensions. No root norm or one-dimensional
tripod premise occurs in this theorem. The passive n=0 case is retained. -/
theorem transverse_indec_dimensions [Finite K] [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hCW : C ≤ W)
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (hzero : Module.finrank K U + Module.finrank K V + Module.finrank K W +
      Module.finrank K A + Module.finrank K B + Module.finrank K C = 3*Module.finrank K F)
    (hpos : Module.finrank K F < Module.finrank K A + Module.finrank K B + Module.finrank K C)
    (hAV : Disjoint A V) (hAW : Disjoint A W) (hBU : Disjoint B U)
    (hBW : Disjoint B W) (hCU : Disjoint C U) (hCV : Disjoint C V)
    (hi : Indecomposable (flagSpaces A B C U V W) ⊤) :
    ∃ n : ℕ, Module.finrank K F = 3*n+2 ∧
      Module.finrank K A = n+1 ∧ Module.finrank K B = n+1 ∧ Module.finrank K C = n+1 ∧
      Module.finrank K U = 2*n+1 ∧ Module.finrank K V = 2*n+1 ∧ Module.finrank K W = 2*n+1 := by
  obtain ⟨ha,hb,hu,hv,hf⟩ := transverse_dimension_equalities A B C U V W hzero
    hAV hAW hBU hBW hCU hCV
  have hcAV : IsCompl A V := (Submodule.isCompl_iff_disjoint A V (by omega)).mpr hAV
  have hcBU : IsCompl B U := (Submodule.isCompl_iff_disjoint B U (by omega)).mpr hBU
  have hcBW : IsCompl B W := (Submodule.isCompl_iff_disjoint B W (by omega)).mpr hBW
  obtain ⟨e,L,heC,heU,heV,heA,heB⟩ := exists_diagonal_frame A B C U V
    hAU hBV hcAV hcBU hCU hCV ha.symm hb.symm
  have hs := diagonal_map_surjective A B C e L heC heA heB hspan
  obtain ⟨T,hT⟩ := third_space_graph B C W e L heC heB hCW hcBW
  obtain ⟨hmA,hmB,hmC⟩ := diagonal_frame_side_membership A B C e L heC heA heB
  have he : ∀ i p, e p ∈ flagSpaces A B C U V W i ↔ p ∈ diagonalSpaces L T i := by
    intro i p
    fin_cases i
    · exact hmA p
    · exact hmB p
    · exact hmC p
    · exact heU p
    · exact heV p
    · exact hT p
  have hdim := e.finrank_eq
  simp only [Module.finrank_prod] at hdim
  have hkerdim := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at hkerdim
  have hk : LinearMap.ker L ≠ ⊥ := by
    intro hz
    rw [hz,finrank_bot] at hkerdim
    omega
  have hCp : 0 < Module.finrank K C := by omega
  letI : Nontrivial C := Module.nontrivial_of_finrank_pos hCp
  have hi' := indecomposable_in_coordinates (diagonalSpaces L T)
    (flagSpaces A B C U V W) e he hi
  have hr := tripod_kernel_finrank_one L T hs hk hi'
  refine ⟨Module.finrank K ↥(U ⊓ V), ?_⟩
  omega


/-- The passive endpoint is the zero-private-block tripod. -/
abbrev PassiveTripodSpaces (K : Type*) [Field K] :=
  ResonantEndomorphisms.spaces K (Fin 0 → K) 0 0

/-- Classification at the passive endpoint, which has no private demand. -/
theorem classify_passive_transverse_flags [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hCW : C ≤ W)
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (hF : Module.finrank K F = 2)
    (hA : Module.finrank K A = 1) (hB : Module.finrank K B = 1)
    (hC : Module.finrank K C = 1)
    (hU : Module.finrank K U = 1) (hV : Module.finrank K V = 1)
    (hW : Module.finrank K W = 1)
    (hAV : Disjoint A V) (hBU : Disjoint B U)
    (hCU : Disjoint C U) (hCV : Disjoint C V) (hBW : Disjoint B W) :
    ConfigurationIso (flagSpaces A B C U V W) (PassiveTripodSpaces K) := by
  obtain ⟨hY,J,h,e,he⟩ := normalize_transverse_flags A B C U V W hAU hBV hCW hspan
    0 (by simpa using hF) (by simpa using hA) (by simpa using hB) (by simpa using hC)
    (by simpa using hU) (by simpa using hV) (by simpa using hW) hAV hBU hCU hCV hBW
  letI : Subsingleton ↥(U ⊓ V) := Module.finrank_zero_iff.mp hY
  let g : ↥(U ⊓ V) ≃ₗ[K] (Fin 0 → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using hY)
  obtain ⟨f,hf,hf'⟩ := ResonantClassification.graph_configurationIso_of_conjugacy J h
    (0 : Module.End K (Fin 0 → K)) (0 : (Fin 0 → K) →ₗ[K] K) g
    (fun _ => Subsingleton.elim _ _)
    (by intro x; rw [Subsingleton.elim x 0]; simp)
  refine ⟨e.symm.trans f, ?_, ?_⟩
  · intro i x hx
    apply hf i
    apply (he i (e.symm x)).mp
    simpa using hx
  · intro i x hx
    apply (he i (f.symm x)).mpr
    exact hf' i x hx

/-- Complete original-field classification with an honest passive boundary.
The second alternative is the manuscript's R_(n+1) family. -/
theorem classify_transverse_indec [Finite K] [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hCW : C ≤ W)
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (hzero : Module.finrank K U + Module.finrank K V + Module.finrank K W +
      Module.finrank K A + Module.finrank K B + Module.finrank K C = 3*Module.finrank K F)
    (hpos : Module.finrank K F < Module.finrank K A + Module.finrank K B + Module.finrank K C)
    (hAV : Disjoint A V) (hAW : Disjoint A W) (hBU : Disjoint B U)
    (hBW : Disjoint B W) (hCU : Disjoint C U) (hCV : Disjoint C V)
    (hi : Indecomposable (flagSpaces A B C U V W) ⊤) :
    (A = U ∧ B = V ∧ C = W ∧
      ConfigurationIso (flagSpaces A B C U V W) (PassiveTripodSpaces K)) ∨
    ∃ n : ℕ, ConfigurationIso (flagSpaces A B C U V W)
      (ResonantEndomorphisms.spaces K (JordanResonance.V K n)
        (JordanResonance.shift K n) (JordanResonance.head K n)) := by
  obtain ⟨n,hF,hA,hB,hC,hU,hV,hW⟩ := transverse_indec_dimensions A B C U V W
    hAU hBV hCW hspan hzero hpos hAV hAW hBU hBW hCU hCV hi
  cases n with
  | zero =>
    left
    refine ⟨Submodule.eq_of_le_of_finrank_eq hAU (by omega),
      Submodule.eq_of_le_of_finrank_eq hBV (by omega),
      Submodule.eq_of_le_of_finrank_eq hCW (by omega), ?_⟩
    exact classify_passive_transverse_flags A B C U V W hAU hBV hCW hspan
      (by simpa using hF) (by simpa using hA) (by simpa using hB) (by simpa using hC)
      (by simpa using hU) (by simpa using hV) (by simpa using hW) hAV hBU hCU hCV hBW
  | succ n =>
    right
    exact ⟨n,classify_transverse_resonant_flags A B C U V W hAU hBV hCW hspan
      n hF hA hB hC hU hV hW hAV hBU hCU hCV hBW hi⟩

/-- Any genuinely enlarged flag excludes the passive tripod. Positive excess
alone does not exclude it. -/
theorem classify_active_transverse_indec [Finite K] [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hCW : C ≤ W)
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (hzero : Module.finrank K U + Module.finrank K V + Module.finrank K W +
      Module.finrank K A + Module.finrank K B + Module.finrank K C = 3*Module.finrank K F)
    (hpos : Module.finrank K F < Module.finrank K A + Module.finrank K B + Module.finrank K C)
    (hAV : Disjoint A V) (hAW : Disjoint A W) (hBU : Disjoint B U)
    (hBW : Disjoint B W) (hCU : Disjoint C U) (hCV : Disjoint C V)
    (hi : Indecomposable (flagSpaces A B C U V W) ⊤)
    (hactive : A ≠ U ∨ B ≠ V ∨ C ≠ W) :
    ∃ n : ℕ, ConfigurationIso (flagSpaces A B C U V W)
      (ResonantEndomorphisms.spaces K (JordanResonance.V K n)
        (JordanResonance.shift K n) (JordanResonance.head K n)) := by
  obtain ⟨ha,hb,hc,_⟩ | hr := classify_transverse_indec A B C U V W
    hAU hBV hCW hspan hzero hpos hAV hAW hBU hBW hCU hCV hi
  · rcases hactive with h | h | h
    · exact False.elim (h ha)
    · exact False.elim (h hb)
    · exact False.elim (h hc)
  · exact hr


/-- The graph model with the same arm labels as an actual task. -/
def graphTask (K X : Type*) [Field K] [AddCommGroup X] [Module K X]
    (J : Module.End K X) (h : X →ₗ[K] K) :
    TaskDecomposition.Task K (ResonantEndomorphisms.Ambient K X) where
  A := ![ResonantEndomorphisms.side₁ K X, ResonantEndomorphisms.side₂ K X,
    ResonantEndomorphisms.side₃ K X]
  U := ![ResonantEndomorphisms.total₁ K X, ResonantEndomorphisms.total₂ K X,
    ResonantEndomorphisms.total₃ K X J h]
  nested := by
    intro i p hp
    fin_cases i
    · change p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.2 = 0 at hp
      exact ⟨hp.1.trans hp.2.1.symm,hp.2.2⟩
    · change p.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.1 = 0 at hp
      exact ⟨hp.1.trans hp.2.1.symm,hp.2.2⟩
    · change p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2.2.1 + p.2.2.2.2 = 0 at hp
      change p.2.1 = p.1 + J p.1 ∧ p.2.2.2.1 + p.2.2.2.2 = h p.1
      simp [hp.1,hp.2.1,hp.2.2]

lemma task_indec_six (T : TaskDecomposition.Task K F) (hi : Indecomposable T.spaces ⊤) :
    Indecomposable (flagSpaces (T.A 0) (T.A 1) (T.A 2) (T.U 0) (T.U 1) (T.U 2)) ⊤ := by
  apply indecomposable_of_projection_eq_zero_or_id hi.1
  intro f hf hid
  apply hi.projection_eq_zero_or_id f _ hid
  rintro ⟨i,b⟩ p hp
  fin_cases i <;> cases b
  · exact hf 0 p hp
  · exact hf 3 p hp
  · exact hf 1 p hp
  · exact hf 4 p hp
  · exact hf 2 p hp
  · exact hf 5 p hp

lemma task_configurationIso_of_six (T : TaskDecomposition.Task K F)
    (S : TaskDecomposition.Task K Z)
    (h : ConfigurationIso
      (flagSpaces (T.A 0) (T.A 1) (T.A 2) (T.U 0) (T.U 1) (T.U 2))
      (flagSpaces (S.A 0) (S.A 1) (S.A 2) (S.U 0) (S.U 1) (S.U 2))) :
    ConfigurationIso T.spaces S.spaces := by
  obtain ⟨e,he,he'⟩ := h
  refine ⟨e,?_,?_⟩
  · rintro ⟨i,b⟩ p hp
    fin_cases i <;> cases b
    · exact he 0 p hp
    · exact he 3 p hp
    · exact he 1 p hp
    · exact he 4 p hp
    · exact he 2 p hp
    · exact he 5 p hp
  · rintro ⟨i,b⟩ p hp
    fin_cases i <;> cases b
    · exact he' 0 p hp
    · exact he' 3 p hp
    · exact he' 1 p hp
    · exact he' 4 p hp
    · exact he' 2 p hp
    · exact he' 5 p hp

section ActualTasks
variable {K₀ F₀ : Type} [Field K₀] [Finite K₀] [AddCommGroup F₀] [Module K₀ F₀]
  [FiniteDimensional K₀ F₀]

/-- Source-facing dimension theorem. The cross-intersections are geometric
hypotheses, to be supplied by the regular-factor separation theorem. -/
theorem task_transverse_indec_dimensions (T : TaskDecomposition.Task K₀ F₀)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K₀ F₀ < Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2))
    (hcross : ∀ i j : Fin 3, i ≠ j → Disjoint (T.U i) (T.A j)) :
    ∃ n : ℕ, T.dimensionVector =
      ⟨3*(n:ℤ)+2,2*(n:ℤ)+1,2*(n:ℤ)+1,2*(n:ℤ)+1,
        (n:ℤ)+1,(n:ℤ)+1,(n:ℤ)+1⟩ := by
  have hz : Module.finrank K₀ (T.U 0) + Module.finrank K₀ (T.U 1) +
      Module.finrank K₀ (T.U 2) + Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2) = 3*Module.finrank K₀ F₀ := by
    simp only [ReflectionReduction.defect,Task.dimensionVector] at hzero
    omega
  obtain ⟨n,hF,hA,hB,hC,hU,hV,hW⟩ := transverse_indec_dimensions
    (T.A 0) (T.A 1) (T.A 2) (T.U 0) (T.U 1) (T.U 2)
    (T.nested 0) (T.nested 1) (T.nested 2) hspan hz hpos
    (hcross 1 0 (by decide)).symm (hcross 2 0 (by decide)).symm
    (hcross 0 1 (by decide)).symm (hcross 2 1 (by decide)).symm
    (hcross 0 2 (by decide)).symm (hcross 1 2 (by decide)).symm (task_indec_six T hi)
  refine ⟨n,?_⟩
  simp only [Task.dimensionVector,hF,hA,hB,hC,hU,hV,hW,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one]

/-- Original-field classification for the active source task, with the exact
source labels preserved by an actual ambient linear equivalence. -/
theorem classify_active_task (T : TaskDecomposition.Task K₀ F₀)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K₀ F₀ < Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2))
    (hcross : ∀ i j : Fin 3, i ≠ j → Disjoint (T.U i) (T.A j))
    (hactive : ∃ i, T.A i ≠ T.U i) :
    ∃ n : ℕ, ConfigurationIso T.spaces
      (graphTask K₀ (JordanResonance.V K₀ n)
        (JordanResonance.shift K₀ n) (JordanResonance.head K₀ n)).spaces := by
  have hz : Module.finrank K₀ (T.U 0) + Module.finrank K₀ (T.U 1) +
      Module.finrank K₀ (T.U 2) + Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2) = 3*Module.finrank K₀ F₀ := by
    simp only [ReflectionReduction.defect,Task.dimensionVector] at hzero
    omega
  have ha : T.A 0 ≠ T.U 0 ∨ T.A 1 ≠ T.U 1 ∨ T.A 2 ≠ T.U 2 := by
    obtain ⟨i,hi⟩ := hactive
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  obtain ⟨n,hn⟩ := classify_active_transverse_indec
    (T.A 0) (T.A 1) (T.A 2) (T.U 0) (T.U 1) (T.U 2)
    (T.nested 0) (T.nested 1) (T.nested 2) hspan hz hpos
    (hcross 1 0 (by decide)).symm (hcross 2 0 (by decide)).symm
    (hcross 0 1 (by decide)).symm (hcross 2 1 (by decide)).symm
    (hcross 0 2 (by decide)).symm (hcross 1 2 (by decide)).symm (task_indec_six T hi) ha
  exact ⟨n,task_configurationIso_of_six T _ hn⟩


/-- The derived dimensions imply both real-root norm and excess one; neither
was assumed in the classification argument. -/
theorem task_transverse_tits_and_excess (T : TaskDecomposition.Task K₀ F₀)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K₀ F₀ < Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2))
    (hcross : ∀ i j : Fin 3, i ≠ j → Disjoint (T.U i) (T.A j)) :
    ReflectionReduction.tits T.dimensionVector = 1 ∧
      Structural.excess T.dimensionVector.f T.dimensionVector.a₁
        T.dimensionVector.a₂ T.dimensionVector.a₃ = 1 := by
  obtain ⟨n,hn⟩ := task_transverse_indec_dimensions T hi hzero hspan hpos hcross
  rw [hn]
  constructor <;> simp only [ReflectionReduction.tits,Structural.tits,Structural.excess] <;> ring

/-- Source-facing complete classification, retaining T₀ when no demand is active. -/
theorem classify_transverse_task (T : TaskDecomposition.Task K₀ F₀)
    (hi : Indecomposable T.spaces ⊤)
    (hzero : ReflectionReduction.defect T.dimensionVector = 0)
    (hspan : (T.A 0 ⊔ T.A 1) ⊔ T.A 2 = ⊤)
    (hpos : Module.finrank K₀ F₀ < Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2))
    (hcross : ∀ i j : Fin 3, i ≠ j → Disjoint (T.U i) (T.A j)) :
    ((∀ i, T.A i = T.U i) ∧
      ConfigurationIso T.spaces (graphTask K₀ (Fin 0 → K₀) 0 0).spaces) ∨
    ∃ n : ℕ, ConfigurationIso T.spaces
      (graphTask K₀ (JordanResonance.V K₀ n)
        (JordanResonance.shift K₀ n) (JordanResonance.head K₀ n)).spaces := by
  have hz : Module.finrank K₀ (T.U 0) + Module.finrank K₀ (T.U 1) +
      Module.finrank K₀ (T.U 2) + Module.finrank K₀ (T.A 0) +
      Module.finrank K₀ (T.A 1) + Module.finrank K₀ (T.A 2) = 3*Module.finrank K₀ F₀ := by
    simp only [ReflectionReduction.defect,Task.dimensionVector] at hzero
    omega
  obtain ⟨ha,hb,hc,hiso⟩ | ⟨n,hn⟩ := classify_transverse_indec
    (T.A 0) (T.A 1) (T.A 2) (T.U 0) (T.U 1) (T.U 2)
    (T.nested 0) (T.nested 1) (T.nested 2) hspan hz hpos
    (hcross 1 0 (by decide)).symm (hcross 2 0 (by decide)).symm
    (hcross 0 1 (by decide)).symm (hcross 2 1 (by decide)).symm
    (hcross 0 2 (by decide)).symm (hcross 1 2 (by decide)).symm (task_indec_six T hi)
  · left
    refine ⟨?_,task_configurationIso_of_six T _ hiso⟩
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · exact Or.inr ⟨n,task_configurationIso_of_six T _ hn⟩

end ActualTasks
end UploadBroadcast.GeneralTransverseClassification
