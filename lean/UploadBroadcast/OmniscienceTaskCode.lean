import UploadBroadcast.OmniscienceOptimal
import UploadBroadcast.LinearCode
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! Actual coefficient-task adapters for original-field omniscience uploads. -/
namespace UploadBroadcast.OmniscienceOperational
open Module
variable {K V X₁ X₂ X₃ : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₂] [Module K X₂] [AddCommGroup X₃] [Module K X₃]

abbrev Space (V X₁ X₂ X₃ : Type*) := Omniscience.Omega V X₁ X₂ X₃

def coeff₁ : (V × X₂ × X₃) →ₗ[K] Space V X₁ X₂ X₃ where
  toFun x := (x.1,0,0,x.2.1,x.2.2)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def coeff₂ : (V × X₁ × X₃) →ₗ[K] Space V X₁ X₂ X₃ where
  toFun x := (0,x.1,x.2.1,0,x.2.2)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def coeff₃ : (V × X₁ × X₂) →ₗ[K] Space V X₁ X₂ X₃ where
  toFun x := (-x.1,x.1,x.2.1,x.2.2,0)
  map_add' _ _ := by simp [add_comm]
  map_smul' _ _ := by ext <;> simp

theorem coeff₁_injective : Function.Injective (coeff₁ (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z : Space V X₁ X₂ X₃ => z.1) h)
    (Prod.ext (congrArg (fun z => z.2.2.2.1) h) (congrArg (fun z => z.2.2.2.2) h))
theorem coeff₂_injective : Function.Injective (coeff₂ (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.2.1) h)
    (Prod.ext (congrArg (fun z => z.2.2.1) h) (congrArg (fun z => z.2.2.2.2) h))
theorem coeff₃_injective : Function.Injective (coeff₃ (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.2.1) h)
    (Prod.ext (congrArg (fun z => z.2.2.1) h) (congrArg (fun z => z.2.2.2.1) h))

def sides : Three → Submodule K (Space V X₁ X₂ X₃) :=
  ![LinearMap.range coeff₁,LinearMap.range coeff₂,LinearMap.range coeff₃]

theorem sides₀₁_span : sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 0 ⊔ sides 1 = ⊤ := by
  apply top_unique
  intro x _
  refine Submodule.mem_sup.mpr ⟨coeff₁ (x.1,x.2.2.2.1,x.2.2.2.2),⟨_,rfl⟩,
    coeff₂ (x.2.1,x.2.2.1,0),⟨_,rfl⟩,?_⟩
  simp [coeff₁,coeff₂]

def task : Task K (Space V X₁ X₂ X₃) where
  A := sides
  U _ := ⊤
  side_le_signal _ := le_top
  feasible _ := by
    rw [← sides₀₁_span]
    exact sup_le (le_iSup _ 0) (le_iSup _ 1)

variable {A B C W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup W] [Module K W]

/-- Restricting a source to product coordinates is an exact linear equivalence. -/
def homTriple : ((A × B × C) →ₗ[K] W) ≃ₗ[K] ((A →ₗ[K] W) × (B →ₗ[K] W) × (C →ₗ[K] W)) :=
  (LinearMap.coprodEquiv K).symm.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl K _) (LinearMap.coprodEquiv K).symm)

/-- The dual-coordinate/value-source identification, including vector blocks. -/
def sourceCoordinates : (Space V X₁ X₂ X₃ →ₗ[K] W) ≃ₗ[K]
    Space (V →ₗ[K] W) (X₁ →ₗ[K] W) (X₂ →ₗ[K] W) (X₃ →ₗ[K] W) :=
  (LinearMap.coprodEquiv K).symm.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl K _)
      ((LinearMap.coprodEquiv K).symm.trans
        (LinearEquiv.prodCongr (LinearEquiv.refl K _) homTriple)))

noncomputable def sideValues₁ : ((sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 0) →ₗ[K] W) ≃ₗ[K]
    ((V →ₗ[K] W) × (X₂ →ₗ[K] W) × (X₃ →ₗ[K] W)) :=
  (LinearEquiv.arrowCongr (LinearEquiv.ofInjective coeff₁ coeff₁_injective).symm
    (LinearEquiv.refl K W)).trans homTriple
noncomputable def sideValues₂ : ((sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 1) →ₗ[K] W) ≃ₗ[K]
    ((V →ₗ[K] W) × (X₁ →ₗ[K] W) × (X₃ →ₗ[K] W)) :=
  (LinearEquiv.arrowCongr (LinearEquiv.ofInjective coeff₂ coeff₂_injective).symm
    (LinearEquiv.refl K W)).trans homTriple
noncomputable def sideValues₃ : ((sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 2) →ₗ[K] W) ≃ₗ[K]
    ((V →ₗ[K] W) × (X₁ →ₗ[K] W) × (X₂ →ₗ[K] W)) :=
  (LinearEquiv.arrowCongr (LinearEquiv.ofInjective coeff₃ coeff₃_injective).symm
    (LinearEquiv.refl K W)).trans homTriple

theorem observe₁ (x : Space V X₁ X₂ X₃ →ₗ[K] W) :
    sideValues₁ (x.comp (sides 0).subtype) = Omniscience.side₁ (sourceCoordinates x) := by
  ext a <;> rfl
theorem observe₂ (x : Space V X₁ X₂ X₃ →ₗ[K] W) :
    sideValues₂ (x.comp (sides 1).subtype) = Omniscience.side₂ (sourceCoordinates x) := by
  ext a <;> rfl
theorem observe₃ (x : Space V X₁ X₂ X₃ →ₗ[K] W) :
    sideValues₃ (x.comp (sides 2).subtype) = Omniscience.side₃ (sourceCoordinates x) := by
  apply Prod.ext
  · ext a
    change x (-a,a,0,0,0) = x (0,a,0,0,0) - x (a,0,0,0,0)
    rw [← map_sub]
    congr 1
    ext <;> simp
  · apply Prod.ext
    · ext a
      change x (-0,0,a,0,0) = x (0,0,a,0,0)
      simp
    · ext a
      change x (-0,0,0,a,0) = x (0,0,0,a,0)
      simp

namespace Code
variable {L r₁ r₂ r₃ : ℕ}
  (c : Omniscience.Code K (Source K V L) (Source K X₁ L)
    (Source K X₂ L) (Source K X₃ L) r₁ r₂ r₃)

abbrev lengths (r₁ r₂ r₃ : ℕ) : Three → ℕ := ![r₁,r₂,r₃]

/-- Each adapted upload is a linear function of that user's actual observation. -/
noncomputable def encode : ∀ i : Three,
    Source K ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).A i) L →ₗ[K]
      (Fin (lengths r₁ r₂ r₃ i) → K) :=
  Fin.cons (c.encode₁.comp sideValues₁.toLinearMap)
    (Fin.cons (c.encode₂.comp sideValues₂.toLinearMap)
      (Fin.cons (c.encode₃.comp sideValues₃.toLinearMap) (fun i => Fin.elim0 i)))

noncomputable def uploads : Source K (Space V X₁ X₂ X₃) L →ₗ[K]
    (∀ i, Fin (lengths r₁ r₂ r₃ i) → K) :=
  LinearMap.pi fun i => (encode c i).comp (observeLinear L ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).A i))

theorem uploads₁ (x : Source K (Space V X₁ X₂ X₃) L) :
    uploads c x 0 = c.encode₁ (Omniscience.side₁ (sourceCoordinates x)) := by
  exact congrArg c.encode₁ (observe₁ x)
theorem uploads₂ (x : Source K (Space V X₁ X₂ X₃) L) :
    uploads c x 1 = c.encode₂ (Omniscience.side₂ (sourceCoordinates x)) := by
  exact congrArg c.encode₂ (observe₂ x)
theorem uploads₃ (x : Source K (Space V X₁ X₂ X₃) L) :
    uploads c x 2 = c.encode₃ (Omniscience.side₃ (sourceCoordinates x)) := by
  exact congrArg c.encode₃ (observe₃ x)

/-- Zero error implies the linear view map is injective, even when the supplied
value-source decoders were arbitrary functions. -/
theorem view_injective (i : Three) :
    Function.Injective ((uploads c).prod (observeLinear L ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).A i))) := by
  intro x y h
  have hu := congrArg Prod.fst h
  change uploads c x = uploads c y at hu
  have ha := congrArg Prod.snd h
  have h₁ := congrFun hu 0
  have h₂ := congrFun hu 1
  have h₃ := congrFun hu 2
  simp only [LinearMap.prod_apply,uploads₁,uploads₂,uploads₃] at h₁ h₂ h₃
  apply sourceCoordinates.injective
  fin_cases i
  · have hs := congrArg sideValues₁ ha
    change sideValues₁ (x.comp (sides 0).subtype) = sideValues₁ (y.comp (sides 0).subtype) at hs
    rw [observe₁,observe₁] at hs
    rw [← c.zero_error₁ (sourceCoordinates x), ← c.zero_error₁ (sourceCoordinates y),hs,h₂,h₃]
  · have hs := congrArg sideValues₂ ha
    change sideValues₂ (x.comp (sides 1).subtype) = sideValues₂ (y.comp (sides 1).subtype) at hs
    rw [observe₂,observe₂] at hs
    rw [← c.zero_error₂ (sourceCoordinates x), ← c.zero_error₂ (sourceCoordinates y),hs,h₁,h₃]
  · have hs := congrArg sideValues₃ ha
    change sideValues₃ (x.comp (sides 2).subtype) = sideValues₃ (y.comp (sides 2).subtype) at hs
    rw [observe₃,observe₃] at hs
    rw [← c.zero_error₃ (sourceCoordinates x), ← c.zero_error₃ (sourceCoordinates y),hs,h₁,h₂]

/-- Kernel factorization produces genuine linear decoders; no linearity of the
original decoders is assumed or inferred without proof. -/
theorem exists_decoders :
    ∃ d : ∀ i : Three,
      ((∀ j, Fin (lengths r₁ r₂ r₃ j) → K) × Source K ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).A i) L) →ₗ[K]
        Source K ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).U i) L,
      ∀ x i, d i (uploads c x, observe K _ ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).A i) x) = observe K _ ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).U i) x := by
  choose d hd using fun i => factors_through_of_ker_le
    ((uploads c).prod (observeLinear L ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).A i))) (observeLinear L ((task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).U i))
      (by rw [LinearMap.ker_eq_bot.mpr (view_injective c i)]; exact bot_le)
  exact ⟨d,fun x i => LinearMap.congr_fun (hd i) x⟩

/-- A basis relabeling of the upload tuple lets the relay broadcast a single
ordinary original-field vector of the sum of the nominal upload lengths. -/
noncomputable def relayEquiv (r : Three → ℕ) :
    (∀ i, Fin (r i) → K) ≃ₗ[K] (Fin (∑ i, r i) → K) :=
  LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_pi_fintype])

/-- The actual coefficient-space, length-L linear code. -/
noncomputable def toLinearCode :
    (task (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).LinearCode
      L (lengths r₁ r₂ r₃) (∑ i, lengths r₁ r₂ r₃ i) where
  encode := encode c
  broadcast := (relayEquiv (K := K) (lengths r₁ r₂ r₃)).toLinearMap
  decode i := (Classical.choose (exists_decoders c) i).comp
    ((relayEquiv (K := K) (lengths r₁ r₂ r₃)).symm.toLinearMap.prodMap LinearMap.id)
  zero_error x i := by
    simpa only [LinearMap.comp_apply,LinearMap.prodMap_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply,LinearMap.id_apply] using
        Classical.choose_spec (exists_decoders c) x i

variable [Finite K] [FiniteDimensional K V] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃]

/-- All local observation values occur. The adapter preserves the actual
upload alphabet, rather than merely preserving a nominal length bound. -/
theorem uploadCost : (toLinearCode c).toCode.uploadCost = c.alphabetCost / L := by
  rw [Task.LinearCode.uploadCost_eq_rank,Omniscience.Code.alphabetCost_eq_totalRank]
  congr 1
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero,add_zero]
  change (finrank K (LinearMap.range (c.encode₁.comp sideValues₁.toLinearMap)) : ℝ) +
    ((finrank K (LinearMap.range (c.encode₂.comp sideValues₂.toLinearMap)) : ℝ) +
      (finrank K (LinearMap.range (c.encode₃.comp sideValues₃.toLinearMap)) : ℝ)) = _
  rw [sideValues₁.range_comp,sideValues₂.range_comp,sideValues₃.range_comp]
  simp [Omniscience.Code.totalRank,Nat.cast_add,add_assoc]

/-- The relay's attainable broadcast alphabet obeys the nominal vector bound. -/
theorem broadcastCost_le : (toLinearCode c).toCode.broadcastCost ≤
    ((r₁ : ℝ) + r₂ + r₃) / L := by
  rw [Task.LinearCode.broadcastCost_eq_rank]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := (LinearMap.range (toLinearCode c).transmittedLinear).finrank_le
  have hr : (∑ i, lengths r₁ r₂ r₃ i) = r₁+r₂+r₃ := by
    simp [lengths,Fin.sum_univ_succ,add_assoc]
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,hr] at h
  exact_mod_cast h

end Code

variable [FiniteDimensional K V] [FiniteDimensional K X₁]
  [FiniteDimensional K X₂] [FiniteDimensional K X₃]

/-- The three actual conditional ranks are the missing private block plus
one tripod row. -/
theorem deficits :
    condRank (⊤ : Submodule K (Space V X₁ X₂ X₃)) (sides 0) = finrank K V + finrank K X₁ ∧
    condRank (⊤ : Submodule K (Space V X₁ X₂ X₃)) (sides 1) = finrank K V + finrank K X₂ ∧
    condRank (⊤ : Submodule K (Space V X₁ X₂ X₃)) (sides 2) = finrank K V + finrank K X₃ := by
  have h₁ : finrank K (sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 0) =
      finrank K V + (finrank K X₂ + finrank K X₃) := by
    change finrank K (LinearMap.range coeff₁) = _
    rw [LinearMap.finrank_range_of_inj coeff₁_injective]
    simp only [Module.finrank_prod]
  have h₂ : finrank K (sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 1) =
      finrank K V + (finrank K X₁ + finrank K X₃) := by
    change finrank K (LinearMap.range coeff₂) = _
    rw [LinearMap.finrank_range_of_inj coeff₂_injective]
    simp only [Module.finrank_prod]
  have h₃ : finrank K (sides (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) 2) =
      finrank K V + (finrank K X₁ + finrank K X₂) := by
    change finrank K (LinearMap.range coeff₃) = _
    rw [LinearMap.finrank_range_of_inj coeff₃_injective]
    simp only [Module.finrank_prod]
  have hd : finrank K (Space V X₁ X₂ X₃) =
      finrank K V + (finrank K V + (finrank K X₁ + (finrank K X₂ + finrank K X₃))) := by
    simp only [Space,Omniscience.Omega,Module.finrank_prod]
  constructor
  · unfold condRank
    rw [sup_top_eq,finrank_top,h₁,hd]
    omega
  constructor
  · unfold condRank
    rw [sup_top_eq,finrank_top,h₂,hd]
    omega
  · unfold condRank
    rw [sup_top_eq,finrank_top,h₃,hd]
    omega

/-- The canonical task's code optimum is the maximum of its three actual
deficits and half their sum. -/
theorem optimum_eq_deficits :
    Omniscience.optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) =
      Allocation.omniscienceValue
        (condRank (⊤ : Submodule K (Space V X₁ X₂ X₃)) (sides 0))
        (condRank (⊤ : Submodule K (Space V X₁ X₂ X₃)) (sides 1))
        (condRank (⊤ : Submodule K (Space V X₁ X₂ X₃)) (sides 2)) := by
  obtain ⟨h₁,h₂,h₃⟩ := deficits (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)
  simp only [Omniscience.optimum,h₁,h₂,h₃,Nat.cast_add]

/-- Passing to the block-source coordinate values multiplies all deficits,
and hence the omniscience optimum, by the actual blocklength. -/
theorem optimum_source (L : ℕ) :
    Omniscience.optimum (K := K) (V := Source K V L) (X₁ := Source K X₁ L)
      (X₂ := Source K X₂ L) (X₃ := Source K X₃ L) =
        L * Omniscience.optimum (K := K) (V := V) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  unfold Omniscience.optimum
  simpa [Source,Module.finrank_linearMap,Nat.cast_mul,mul_add,mul_comm] using
    Omniscience.value_scale (L : ℝ)
      (finrank K V + finrank K X₁) (finrank K V + finrank K X₂)
      (finrank K V + finrank K X₃) (by positivity)

/-- Whenever L times the optimum is integral, an actual length-L linear task
code over the original field attains it, with no wasted nominal upload lengths. -/
theorem exists_optimal_at_block [Finite K] (L : ℕ) (hL : 0 < L) (n : ℕ)
    (hn : (n : ℝ) = L * Omniscience.optimum (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) :
    ∃ (r : Three → ℕ) (c : (task (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).LinearCode L r (∑ i, r i)),
      (∑ i, r i) = n ∧
      c.toCode.uploadCost = Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ∧
      c.toCode.broadcastCost ≤ Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  have hn' : (n : ℝ) = Omniscience.optimum (K := K) (V := Source K V L)
      (X₁ := Source K X₁ L) (X₂ := Source K X₂ L) (X₃ := Source K X₃ L) :=
    hn.trans (optimum_source L).symm
  obtain ⟨r₁,r₂,r₃,hf,he⟩ := Allocation.omniscience_integral_optimizer_nat
    (finrank K (Source K V L) + finrank K (Source K X₁ L))
    (finrank K (Source K V L) + finrank K (Source K X₂ L))
    (finrank K (Source K V L) + finrank K (Source K X₃ L)) n
    (by simpa only [Omniscience.optimum,Nat.cast_add] using hn')
  obtain ⟨c⟩ := Omniscience.exists_code (K := K) (V := Source K V L)
    (X₁ := Source K X₁ L) (X₂ := Source K X₂ L) (X₃ := Source K X₃ L)
    r₁ r₂ r₃ (by exact_mod_cast hf.2.2.2.1) (by exact_mod_cast hf.2.2.2.2.1)
      (by exact_mod_cast hf.2.2.2.2.2)
  have hrs : (r₁ : ℝ) + r₂ + r₃ = n := by
    have he' : (r₁ : ℝ) + r₂ + r₃ = Omniscience.optimum (K := K)
        (V := Source K V L) (X₁ := Source K X₁ L) (X₂ := Source K X₂ L)
        (X₃ := Source K X₃ L) := by
      simpa only [Omniscience.optimum,Nat.cast_add] using he
    exact he'.trans hn'.symm
  have halpha : c.alphabetCost = n := by
    apply le_antisymm
    · rw [c.alphabetCost_eq_totalRank]
      exact (show (c.totalRank : ℝ) ≤ (r₁ : ℝ)+r₂+r₃ by exact_mod_cast c.totalRank_le).trans_eq hrs
    · rw [hn']
      exact c.optimum_le_alphabetCost
  have hcost : (n : ℝ) / L = Omniscience.optimum (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
    rw [hn]
    have hLn : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
    field_simp
  refine ⟨Code.lengths r₁ r₂ r₃,Code.toLinearCode c,?_,?_,?_⟩
  · have hrn : r₁+r₂+r₃ = n := by exact_mod_cast hrs
    simpa [Code.lengths,Fin.sum_univ_succ,add_assoc] using hrn
  · rw [Code.uploadCost,halpha,hcost]
  · exact (Code.broadcastCost_le c).trans_eq (by rw [hrs,hcost])

/-- Every integral omniscience optimum is attained by a scalar Task.LinearCode. -/
theorem exists_scalar_optimal [Finite K] (n : ℕ)
    (hn : (n : ℝ) = Omniscience.optimum (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)) :
    ∃ (r : Three → ℕ) (c : (task (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).LinearCode 1 r (∑ i, r i)),
      (∑ i, r i) = n ∧
      c.toCode.uploadCost = Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ∧
      c.toCode.broadcastCost ≤ Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) :=
  exists_optimal_at_block 1 (by decide) n (by simpa using hn)

/-- Half-integrality gives a genuine length-two linear code over the original
finite field, with exactly the optimal attained upload cost. -/
theorem exists_two_instance_optimal [Finite K] :
    ∃ (r : Three → ℕ) (c : (task (K := K) (V := V)
      (X₁ := X₁) (X₂ := X₂) (X₃ := X₃)).LinearCode 2 r (∑ i, r i)),
      ((∑ i, r i : ℕ) : ℝ) / 2 = Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ∧
      c.toCode.uploadCost = Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) ∧
      c.toCode.broadcastCost ≤ Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
  obtain ⟨r₁,r₂,r₃,_,he⟩ := Allocation.omniscience_half_integral_nat
    (finrank K V + finrank K X₁) (finrank K V + finrank K X₂)
    (finrank K V + finrank K X₃)
  have hn : ((r₁+r₂+r₃ : ℕ) : ℝ) =
      2 * Omniscience.optimum (K := K) (V := V)
        (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) := by
    simp only [Omniscience.optimum,Nat.cast_add] at *
    linarith
  obtain ⟨r,c,hr,hu,hd⟩ := exists_optimal_at_block 2 (by decide) (r₁+r₂+r₃)
    (by simpa using hn)
  refine ⟨r,c,?_,hu,hd⟩
  rw [hr,hn]
  ring

end UploadBroadcast.OmniscienceOperational
