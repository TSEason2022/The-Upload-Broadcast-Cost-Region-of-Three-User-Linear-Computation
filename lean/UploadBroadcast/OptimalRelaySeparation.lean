import UploadBroadcast.TripodCompression
import UploadBroadcast.RelayTask
import UploadBroadcast.ResidualOperational
import UploadBroadcast.BlockLinearCode
import UploadBroadcast.OperationalBounds
import UploadBroadcast.Allocation

/-! Actual two-instance compression proves independence at minimum upload. -/
namespace UploadBroadcast
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

namespace Task.Code
variable {T : Task K F} {M : Three → Type*} {S : Type*}

/-- Scalar coding on the doubled coefficient task is a genuine length-two
code, with the same finite message alphabets. -/
def toBlockDouble (c : (Profile.directSum T T).Code 1 M S) : T.Code 2 M S where
  encode i a := c.encode i (observedDoubleBlockEquiv (T.A i) a)
  broadcast := c.broadcast
  decode i s a := (observedDoubleBlockEquiv (T.U i)).symm
    (c.decode i s (observedDoubleBlockEquiv (T.A i) a))
  zero_error x i := by
    apply (observedDoubleBlockEquiv (T.U i)).injective
    simp only [LinearEquiv.apply_symm_apply,observedDoubleBlock_observe]
    exact c.zero_error (sourceDoubleBlockEquiv x) i

theorem toBlockDouble_encode_range (c : (Profile.directSum T T).Code 1 M S) (i : Three) :
    Set.range (c.toBlockDouble.encode i) = Set.range (c.encode i) := by
  change Set.range (c.encode i ∘ observedDoubleBlockEquiv (T.A i)) = _
  rw [Set.range_comp,EquivLike.range_eq_univ (observedDoubleBlockEquiv (T.A i)),Set.image_univ]

theorem toBlockDouble_uploadCost [Finite K] [FiniteDimensional K F]
    (c : (Profile.directSum T T).Code 1 M S) :
    c.toBlockDouble.uploadCost = c.uploadCost / 2 := by
  simp only [uploadCost,toBlockDouble_encode_range,Nat.cast_ofNat,Nat.cast_one,div_one]

end Task.Code

namespace OptimalRelaySeparation

def doubleInclusion (P : Submodule K F) : (P × P) →ₗ[K] (F × F) :=
  P.subtype.prodMap P.subtype

theorem doubleInclusion_injective (P : Submodule K F) :
    Function.Injective (doubleInclusion P) := by
  intro x y h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst h)
  · exact Subtype.ext (congrArg Prod.snd h)

/-- Omniscience compression inside a relay lifts to a feasible locally
generated relay for the original doubled task. -/
theorem lift_double_relay (T : Task K F) (P : Submodule K F)
    (hfeas : T.RelayFeasible P) (Q : Submodule K (P × P))
    (hlocal : Q = ⨆ i, Q ⊓ ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype))
    (hom : ∀ i, ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype) ⊔ Q = ⊤) :
    (Profile.directSum T T).LocallyGenerated (Q.map (doubleInclusion P)) ∧
    (Profile.directSum T T).RelayFeasible (Q.map (doubleInclusion P)) := by
  constructor
  · apply le_antisymm
    · calc
        Q.map (doubleInclusion P) =
            (⨆ i, Q ⊓ ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype)).map (doubleInclusion P) :=
          congrArg (Submodule.map (doubleInclusion P)) hlocal
        _ = ⨆ i, (Q ⊓ ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype)).map (doubleInclusion P) :=
          Submodule.map_iSup _ _
        _ ≤ ⨆ i, Q.map (doubleInclusion P) ⊓ (Profile.directSum T T).A i := by
          apply iSup_mono
          intro i
          rintro _ ⟨x,hx,rfl⟩
          exact ⟨⟨x,hx.1,rfl⟩,hx.2⟩
    · exact iSup_le fun _ => inf_le_left
  · intro i x hx
    obtain ⟨a,ha,p,hp,hap⟩ := Submodule.mem_sup.mp (hfeas i hx.1)
    obtain ⟨b,hb,q,hq,hbq⟩ := Submodule.mem_sup.mp (hfeas i hx.2)
    have hm : (⟨p,hp⟩,⟨q,hq⟩) ∈
        ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype) ⊔ Q :=
      (hom i).symm ▸ Submodule.mem_top
    obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp hm
    refine Submodule.mem_sup.mpr ⟨(a,b) + doubleInclusion P u,?_,
      doubleInclusion P v,⟨v,hv,rfl⟩,?_⟩
    · exact ((T.A i).prod (T.A i)).add_mem ⟨ha,hb⟩ hu
    · rw [add_assoc,← map_add,huv]
      exact Prod.ext hap hbq

/-- A dependent induced side triple yields an actual finite length-two
code whose attained-alphabet upload cost is strictly below the relay rank. -/
theorem exists_cheaper_code [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P)
    (hAB : Disjoint ((T.A 0).comap P.subtype) ((T.A 1).comap P.subtype))
    (hAC : Disjoint ((T.A 0).comap P.subtype) ((T.A 2).comap P.subtype))
    (hBC : Disjoint ((T.A 1).comap P.subtype) ((T.A 2).comap P.subtype))
    (hdep : (T.A 2).comap P.subtype ⊓
      ((T.A 0).comap P.subtype ⊔ (T.A 1).comap P.subtype) ≠ ⊥) :
    ∃ (m : Three → ℕ) (s : ℕ) (c : T.Code 2 (fun i => Fin (m i)) (Fin s)),
      c.uploadCost < finrank K P := by
  have hs := T.induced_sides_span P hlocal
  rw [Profile.three_iSup] at hs
  obtain ⟨Q,hQ,hl,h₁,h₂,h₃⟩ := TripodCompression.exists_compressed_double_finrank
    ((T.A 0).comap P.subtype) ((T.A 1).comap P.subtype) ((T.A 2).comap P.subtype)
    hAB hAC hBC hs hdep
  have hl' : Q = ⨆ i, Q ⊓ ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype) := by
    rw [Profile.three_iSup]
    exact hl
  have hom : ∀ i, ((T.A i).comap P.subtype).prod ((T.A i).comap P.subtype) ⊔ Q = ⊤ := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₃
  obtain ⟨hQl,hQf⟩ := lift_double_relay T P hfeas Q hl' hom
  obtain ⟨owner,c,hc⟩ := ResidualOperational.finiteCode_of_local_relay
    (Profile.directSum T T) (Q.map (doubleInclusion P)) hQl hQf
  letI := c.finite_upload
  letI := c.finite_broadcast
  obtain ⟨m,s,d,hdu,_⟩ := c.toCode.toBlockDouble.finite_relabel
  refine ⟨m,s,d,?_⟩
  rw [hdu,Task.Code.toBlockDouble_uploadCost]
  have hdim : finrank K (Q.map (doubleInclusion P)) = finrank K Q :=
    (Submodule.equivMapOfInjective (doubleInclusion P) (doubleInclusion_injective P) Q).finrank_eq.symm
  have hc' : c.toCode.uploadCost ≤ (finrank K Q : ℝ) :=
    hc.trans_eq (congrArg (fun n : ℕ => (n : ℝ)) hdim)
  have hQ' : (finrank K Q : ℝ) < 2 * finrank K P := by exact_mod_cast hQ
  linarith

/-- The compression argument needs only a lower bound for actual length-two
codes. This form applies to a blocked task once its codes are flattened. -/
theorem induced_separation_of_two_code_lower [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P)
    (hAB : Disjoint ((T.A 0).comap P.subtype) ((T.A 1).comap P.subtype))
    (hAC : Disjoint ((T.A 0).comap P.subtype) ((T.A 2).comap P.subtype))
    (hBC : Disjoint ((T.A 1).comap P.subtype) ((T.A 2).comap P.subtype))
    (hmin : ∀ (m : Three → ℕ) (s : ℕ)
      (c : T.Code 2 (fun i => Fin (m i)) (Fin s)), (finrank K P : ℝ) ≤ c.uploadCost) :
    (T.A 2).comap P.subtype ⊓
      ((T.A 0).comap P.subtype ⊔ (T.A 1).comap P.subtype) = ⊥ := by
  by_contra hdep
  obtain ⟨m,s,c,hc⟩ := exists_cheaper_code T P hlocal hfeas hAB hAC hBC hdep
  exact (not_lt_of_ge (hmin m s c)) hc

/-- Minimum operational upload forbids any tripod in the induced relay
sides. This uses an actual cheaper finite-alphabet code, not a surrogate
rank objective or a presumed normal-form optimum. -/
theorem minimum_induced_separation [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P)
    (hAB : Disjoint ((T.A 0).comap P.subtype) ((T.A 1).comap P.subtype))
    (hAC : Disjoint ((T.A 0).comap P.subtype) ((T.A 2).comap P.subtype))
    (hBC : Disjoint ((T.A 1).comap P.subtype) ((T.A 2).comap P.subtype))
    (hmin : (finrank K P : ℝ) = T.uploadOptimum) :
    (T.A 2).comap P.subtype ⊓
      ((T.A 0).comap P.subtype ⊔ (T.A 1).comap P.subtype) = ⊥ := by
  by_contra hdep
  obtain ⟨m,s,c,hc⟩ := exists_cheaper_code T P hlocal hfeas hAB hAC hBC hdep
  have h := c.uploadOptimum_le (by decide)
  rw [← hmin] at h
  exact (not_lt_of_ge h) hc


/-- Pairwise disjointness plus the absence of a last tripod is full
three-way independence, not merely pairwise disjointness. -/
theorem independent_of_separation (A : Three → Submodule K F)
    (hAB : Disjoint (A 0) (A 1))
    (hC : Disjoint (A 2) (A 0 ⊔ A 1)) : iSupIndep A := by
  have hA : Disjoint (A 0) (A 1 ⊔ A 2) := by
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp hy
    have hc' : c ∈ A 0 ⊔ A 1 := by
      have he : c = x-b := by rw [← hbc]; abel
      rw [he]
      exact (A 0 ⊔ A 1).sub_mem (Submodule.mem_sup_left hx) (Submodule.mem_sup_right hb)
    have hc0 := Submodule.disjoint_def.mp hC c hc hc'
    have hxb : x = b := by simpa [hc0] using hbc.symm
    exact Submodule.disjoint_def.mp hAB x hx (hxb.symm ▸ hb)
  have hB : Disjoint (A 1) (A 0 ⊔ A 2) := by
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    obtain ⟨a,ha,c,hc,hac⟩ := Submodule.mem_sup.mp hy
    have hc' : c ∈ A 0 ⊔ A 1 := by
      have he : c = x-a := by rw [← hac]; abel
      rw [he]
      exact (A 0 ⊔ A 1).sub_mem (Submodule.mem_sup_right hx) (Submodule.mem_sup_left ha)
    have hc0 := Submodule.disjoint_def.mp hC c hc hc'
    have hxa : x = a := by simpa [hc0] using hac.symm
    exact Submodule.disjoint_def.mp hAB x (hxa.symm ▸ ha) hx
  intro i
  fin_cases i
  · simpa [Profile.three_iSup] using hA
  · simpa [Profile.three_iSup] using hB
  · simpa [Profile.three_iSup] using hC

/-- The direct-sum conclusion of minimum-residual-relay independence. -/
theorem minimum_induced_independent [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P)
    (hAB : Disjoint ((T.A 0).comap P.subtype) ((T.A 1).comap P.subtype))
    (hAC : Disjoint ((T.A 0).comap P.subtype) ((T.A 2).comap P.subtype))
    (hBC : Disjoint ((T.A 1).comap P.subtype) ((T.A 2).comap P.subtype))
    (hmin : (finrank K P : ℝ) = T.uploadOptimum) :
    iSupIndep (fun i => (T.A i).comap P.subtype) ∧
      (⨆ i, (T.A i).comap P.subtype) = ⊤ := by
  exact ⟨independent_of_separation _ hAB (disjoint_iff.mpr
    (minimum_induced_separation T P hlocal hfeas hAB hAC hBC hmin)),
    T.induced_sides_span P hlocal⟩


/-- A spanning triple whose dimensions add to the ambient dimension is a
three-way direct sum. -/
theorem independent_of_rank_sum [FiniteDimensional K F]
    (A : Three → Submodule K F) (hspan : (⨆ i, A i) = ⊤)
    (hdim : finrank K (A 0) + finrank K (A 1) + finrank K (A 2) = finrank K F) :
    iSupIndep A := by
  rw [Profile.three_iSup] at hspan
  have hab := Submodule.finrank_sup_add_finrank_inf_eq (A 0) (A 1)
  have hc := Submodule.finrank_sup_add_finrank_inf_eq (A 0 ⊔ A 1) (A 2)
  rw [hspan,finrank_top] at hc
  apply independent_of_separation A
  · apply disjoint_iff.mpr
    apply Submodule.finrank_eq_zero.mp
    omega
  · apply disjoint_iff.mpr
    apply Submodule.finrank_eq_zero.mp
    rw [inf_comm]
    omega

/-- Independence is invariant under user permutation and implies exactly
the binary broadcast separation condition in any user order. -/
theorem independent_permuted_separation (A : Three → Submodule K F)
    (hA : iSupIndep A) (p : Equiv.Perm Three) :
    A (p 0) ⊓ (A (p 1) ⊔ A (p 2)) = ⊥ := by
  have h := (hA.comp p.injective) 0
  have hd : Disjoint (A (p 0)) (A (p 1) ⊔ A (p 2)) := by
    simpa [Profile.three_iSup] using h
  exact hd.eq_bot

/-- Feasible omniscience gives the exact induced side dimension directly
from the actual coefficient spaces. -/
theorem omniscience_induced_rank [FiniteDimensional K F]
    (T : Task K F) (hU : ∀ i, T.U i = ⊤)
    (P : Submodule K F) (hfeas : T.RelayFeasible P) (i : Three) :
    finrank K ((T.A i).comap P.subtype) + condRank ⊤ (T.A i) = finrank K P := by
  have hs : T.A i ⊔ P = ⊤ := top_unique (by simpa only [hU] using hfeas i)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (T.A i) P
  have hm := Submodule.finrank_map_subtype_eq P ((T.A i).comap P.subtype)
  rw [Submodule.map_comap_subtype,inf_comm] at hm
  rw [hs,finrank_top,hm] at hd
  have hle := (T.A i).finrank_le
  unfold condRank
  rw [sup_top_eq,finrank_top]
  omega

/-- An optimal omniscience relay always has binary-separated induced
sides after a permutation. In the balanced case the side ranks sum to the
relay rank. In the dominating case a maximizing-deficit side is zero. -/
theorem omniscience_minimum_separation [FiniteDimensional K F]
    (T : Task K F) (hU : ∀ i, T.U i = ⊤)
    (P : Submodule K F) (hlocal : T.LocallyGenerated P) (hfeas : T.RelayFeasible P)
    (hmin : (finrank K P : ℝ) = Allocation.omniscienceValue
      (condRank ⊤ (T.A 0)) (condRank ⊤ (T.A 1)) (condRank ⊤ (T.A 2))) :
    ∃ p : Equiv.Perm Three,
      (T.A (p 0)).comap P.subtype ⊓
        ((T.A (p 1)).comap P.subtype ⊔ (T.A (p 2)).comap P.subtype) = ⊥ := by
  let A : Three → Submodule K P := fun i => (T.A i).comap P.subtype
  have hd (i : Three) : (finrank K (A i) : ℝ) + condRank ⊤ (T.A i) = finrank K P := by
    exact_mod_cast omniscience_induced_rank T hU P hfeas i
  have hz (i : Three) (he : (finrank K P : ℝ) = condRank ⊤ (T.A i)) : A i = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have h := hd i
    have : (finrank K (A i) : ℝ) = 0 := by linarith
    exact_mod_cast this
  unfold Allocation.omniscienceValue at hmin
  rcases max_choice (max (condRank ⊤ (T.A 0) : ℝ) (condRank ⊤ (T.A 1)))
    (max (condRank ⊤ (T.A 2) : ℝ)
      (((condRank ⊤ (T.A 0) : ℝ) + condRank ⊤ (T.A 1) + condRank ⊤ (T.A 2))/2)) with he | he
  · rw [he] at hmin
    rcases max_choice (condRank ⊤ (T.A 0) : ℝ) (condRank ⊤ (T.A 1)) with he | he
    · rw [he] at hmin
      refine ⟨Equiv.refl Three,?_⟩
      change A 0 ⊓ (A 1 ⊔ A 2) = ⊥
      rw [hz 0 hmin,bot_inf_eq]
    · rw [he] at hmin
      refine ⟨Equiv.swap 0 1,?_⟩
      have hh := hz 1 hmin
      change A ((Equiv.swap 0 1) 0) ⊓ _ = ⊥
      rw [Equiv.swap_apply_left,hh,bot_inf_eq]
  · rw [he] at hmin
    rcases max_choice (condRank ⊤ (T.A 2) : ℝ)
      (((condRank ⊤ (T.A 0) : ℝ) + condRank ⊤ (T.A 1) + condRank ⊤ (T.A 2))/2) with he | he
    · rw [he] at hmin
      refine ⟨Equiv.swap 0 2,?_⟩
      have hh := hz 2 hmin
      change A ((Equiv.swap 0 2) 0) ⊓ _ = ⊥
      rw [Equiv.swap_apply_left,hh,bot_inf_eq]
    · rw [he] at hmin
      have hsum : finrank K (A 0) + finrank K (A 1) + finrank K (A 2) = finrank K P := by
        have h₀ := hd 0
        have h₁ := hd 1
        have h₂ := hd 2
        have : (finrank K (A 0) : ℝ) + finrank K (A 1) + finrank K (A 2) = finrank K P := by linarith
        exact_mod_cast this
      exact ⟨Equiv.refl Three,independent_permuted_separation A
        (independent_of_rank_sum A (T.induced_sides_span P hlocal) hsum) (Equiv.refl Three)⟩


/-- Separation inside a relay is exactly separation of the corresponding
intersection subspaces in the original ambient space. -/
theorem induced_separation_iff (A : Three → Submodule K F) (P : Submodule K F)
    (p : Equiv.Perm Three) :
    (A (p 0)).comap P.subtype ⊓
      ((A (p 1)).comap P.subtype ⊔ (A (p 2)).comap P.subtype) = ⊥ ↔
    (P ⊓ A (p 0)) ⊓ ((P ⊓ A (p 1)) ⊔ (P ⊓ A (p 2))) = ⊥ := by
  have hmap : (((A (p 0)).comap P.subtype ⊓
      ((A (p 1)).comap P.subtype ⊔ (A (p 2)).comap P.subtype))).map P.subtype =
      (P ⊓ A (p 0)) ⊓ ((P ⊓ A (p 1)) ⊔ (P ⊓ A (p 2))) := by
    rw [Submodule.map_inf _ P.subtype_injective,Submodule.map_sup]
    simp only [Submodule.map_comap_subtype]
  constructor
  · intro h
    rw [← hmap,h,Submodule.map_bot]
  · intro h
    apply Submodule.map_injective_of_injective P.subtype_injective
    rw [hmap,h,Submodule.map_bot]

/-- Pairwise disjoint original sides remain pairwise disjoint on a relay. -/
theorem induced_disjoint (A B P : Submodule K F) (hAB : Disjoint A B) :
    Disjoint (A.comap P.subtype) (B.comap P.subtype) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  exact Subtype.ext (Submodule.disjoint_def.mp hAB (x : F) hx hy)

/-- Source lemma `optimal-residual-sides`, in scalar coefficient form:
a minimum operational-upload residual relay is the direct sum of its
three induced sides. Pairwise disjointness is imposed on the actual
original residual sides, not on hypothetical coordinates. -/
theorem optimal_residual_sides [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P)
    (hAB : Disjoint (T.A 0) (T.A 1)) (hAC : Disjoint (T.A 0) (T.A 2))
    (hBC : Disjoint (T.A 1) (T.A 2))
    (hmin : (finrank K P : ℝ) = T.uploadOptimum) :
    iSupIndep (fun i => (T.A i).comap P.subtype) ∧
      (⨆ i, (T.A i).comap P.subtype) = ⊤ :=
  minimum_induced_independent T P hlocal hfeas
    (induced_disjoint _ _ P hAB) (induced_disjoint _ _ P hAC) (induced_disjoint _ _ P hBC) hmin


/-- The same direct-sum statement in the original ambient space, in exactly
the manuscript's intersection notation. -/
theorem optimal_residual_sides_ambient [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P)
    (hAB : Disjoint (T.A 0) (T.A 1)) (hAC : Disjoint (T.A 0) (T.A 2))
    (hBC : Disjoint (T.A 1) (T.A 2))
    (hmin : (finrank K P : ℝ) = T.uploadOptimum) :
    iSupIndep (fun i => P ⊓ T.A i) ∧ P = ⨆ i, P ⊓ T.A i := by
  have hc := minimum_induced_separation T P hlocal hfeas
    (induced_disjoint _ _ P hAB) (induced_disjoint _ _ P hAC) (induced_disjoint _ _ P hBC) hmin
  have hm := congrArg (Submodule.map P.subtype) hc
  rw [Submodule.map_inf _ P.subtype_injective,Submodule.map_sup,
    Submodule.map_bot] at hm
  simp only [Submodule.map_comap_subtype] at hm
  exact ⟨independent_of_separation _ (hAB.mono inf_le_right inf_le_right)
    (disjoint_iff.mpr hm),hlocal⟩

variable {G : Type*} [AddCommGroup G] [Module K G]

/-- Local generation is preserved by assembling independent task components. -/
theorem product_locally_generated (T : Task K F) (R : Task K G)
    (P : Submodule K F) (Q : Submodule K G)
    (hP : T.LocallyGenerated P) (hQ : R.LocallyGenerated Q) :
    (Profile.directSum T R).LocallyGenerated (P.prod Q) := by
  unfold Task.LocallyGenerated at hP hQ ⊢
  rw [Profile.three_iSup] at hP hQ ⊢
  change P.prod Q = _
  simp only [Profile.directSum,Submodule.prod_inf_prod,Submodule.prod_sup_prod]
  rw [← hP,← hQ]


/-- Feasibility also assembles on the actual product relay. -/
theorem product_relay_feasible (T : Task K F) (R : Task K G)
    (P : Submodule K F) (Q : Submodule K G)
    (hP : T.RelayFeasible P) (hQ : R.RelayFeasible Q) :
    (Profile.directSum T R).RelayFeasible (P.prod Q) := by
  intro i
  change (T.U i).prod (R.U i) ≤ (T.A i).prod (R.A i) ⊔ P.prod Q
  rw [Submodule.prod_sup_prod]
  exact Submodule.prod_mono (hP i) (hQ i)

/-- Residual independence and the proven omniscience alternative imply the
actual binary separation condition for the assembled relay, after a user
permutation. The resulting condition uses the original combined task. -/
theorem binary_relay_separation [Finite K] [FiniteDimensional K F] [FiniteDimensional K G]
    (T : Task K F) (O : Task K G)
    (P : Submodule K F) (Q : Submodule K G)
    (hPl : T.LocallyGenerated P) (hPf : T.RelayFeasible P)
    (hAB : Disjoint (T.A 0) (T.A 1)) (hAC : Disjoint (T.A 0) (T.A 2))
    (hBC : Disjoint (T.A 1) (T.A 2))
    (hPmin : (finrank K P : ℝ) = T.uploadOptimum)
    (hOU : ∀ i, O.U i = ⊤) (hQl : O.LocallyGenerated Q) (hQf : O.RelayFeasible Q)
    (hQmin : (finrank K Q : ℝ) = Allocation.omniscienceValue
      (condRank ⊤ (O.A 0)) (condRank ⊤ (O.A 1)) (condRank ⊤ (O.A 2))) :
    ∃ p : Equiv.Perm Three,
      (⨆ i, ((Profile.directSum T O).A i).comap (P.prod Q).subtype) = ⊤ ∧
      ((Profile.directSum T O).A (p 0)).comap (P.prod Q).subtype ⊓
        (((Profile.directSum T O).A (p 1)).comap (P.prod Q).subtype ⊔
          ((Profile.directSum T O).A (p 2)).comap (P.prod Q).subtype) = ⊥ := by
  obtain ⟨hPi,_⟩ := optimal_residual_sides T P hPl hPf hAB hAC hBC hPmin
  obtain ⟨p,hp⟩ := omniscience_minimum_separation O hOU Q hQl hQf hQmin
  refine ⟨p,(Profile.directSum T O).induced_sides_span (P.prod Q)
    (product_locally_generated T O P Q hPl hQl),?_⟩
  apply (induced_separation_iff (Profile.directSum T O).A (P.prod Q) p).mpr
  have hPsep := (induced_separation_iff T.A P p).mp
    (independent_permuted_separation _ hPi p)
  have hQsep := (induced_separation_iff O.A Q p).mp hp
  simp only [Profile.directSum,Submodule.prod_inf_prod,Submodule.prod_sup_prod]
  rw [hPsep,hQsep,Submodule.prod_bot]

end OptimalRelaySeparation
end UploadBroadcast
