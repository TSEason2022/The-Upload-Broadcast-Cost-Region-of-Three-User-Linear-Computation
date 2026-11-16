import UploadBroadcast.ScalarBroadcast
import UploadBroadcast.PairSelection
import UploadBroadcast.AllocationNat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace UploadBroadcast.ScalarIncidence
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

abbrev Groups (r x y z l : ℕ) := Fin r ⊕ ((Fin x ⊕ (Fin y ⊕ Fin z)) ⊕ Fin l)

def Local (r x y z l : ℕ) : Fin 3 → Type
  | 0 => Fin r ⊕ ((Fin z ⊕ Fin y) ⊕ Fin l)
  | 1 => Fin r ⊕ ((Fin z ⊕ Fin x) ⊕ Fin l)
  | 2 => Fin r ⊕ ((Fin y ⊕ Fin x) ⊕ Fin l)

instance (r x y z l : ℕ) (i : Fin 3) : Fintype (Local r x y z l i) := by
  match i with
  | 0 => exact inferInstanceAs (Fintype (Fin r ⊕ ((Fin z ⊕ Fin y) ⊕ Fin l)))
  | 1 => exact inferInstanceAs (Fintype (Fin r ⊕ ((Fin z ⊕ Fin x) ⊕ Fin l)))
  | 2 => exact inferInstanceAs (Fintype (Fin r ⊕ ((Fin y ⊕ Fin x) ⊕ Fin l)))

instance (r x y z l : ℕ) (i : Fin 3) : DecidableEq (Local r x y z l i) := by
  match i with
  | 0 => exact inferInstanceAs (DecidableEq (Fin r ⊕ ((Fin z ⊕ Fin y) ⊕ Fin l)))
  | 1 => exact inferInstanceAs (DecidableEq (Fin r ⊕ ((Fin z ⊕ Fin x) ⊕ Fin l)))
  | 2 => exact inferInstanceAs (DecidableEq (Fin r ⊕ ((Fin y ⊕ Fin x) ⊕ Fin l)))

def inclusion (r x y z l : ℕ) : (i : Fin 3) → Local r x y z l i → Groups r x y z l
  | 0 => Sum.elim Sum.inl (Sum.elim
    (Sum.elim (fun j => Sum.inr (Sum.inl (Sum.inr (Sum.inr j))))
      (fun j => Sum.inr (Sum.inl (Sum.inr (Sum.inl j)))))
    (fun j => Sum.inr (Sum.inr j)))
  | 1 => Sum.elim Sum.inl (Sum.elim
    (Sum.elim (fun j => Sum.inr (Sum.inl (Sum.inr (Sum.inr j))))
      (fun j => Sum.inr (Sum.inl (Sum.inl j))))
    (fun j => Sum.inr (Sum.inr j)))
  | 2 => Sum.elim Sum.inl (Sum.elim
    (Sum.elim (fun j => Sum.inr (Sum.inl (Sum.inr (Sum.inl j))))
      (fun j => Sum.inr (Sum.inl (Sum.inl j))))
    (fun j => Sum.inr (Sum.inr j)))

theorem inclusion_injective (r x y z l : ℕ) (i : Fin 3) :
    Function.Injective (inclusion r x y z l i) := by
  fin_cases i <;> intro a b h <;>
    rcases a with a | (a | a) | a <;> rcases b with b | (b | b) | b <;>
    simp_all [inclusion]

def Space (U : Fin 3 → Submodule K F) {r x y z l : ℕ} : Groups r x y z l → Type _
  | Sum.inl _ => ↥(U 0 ⊓ U 1 ⊓ U 2)
  | Sum.inr (Sum.inl (Sum.inl _)) => ↥(U 1 ⊓ U 2)
  | Sum.inr (Sum.inl (Sum.inr (Sum.inl _))) => ↥(U 0 ⊓ U 2)
  | Sum.inr (Sum.inl (Sum.inr (Sum.inr _))) => ↥(U 0 ⊓ U 1)
  | Sum.inr (Sum.inr _) => ↥(alignedRelation (U 0) (U 1) (U 2))

instance (U : Fin 3 → Submodule K F) {r x y z l : ℕ} (g : Groups r x y z l) :
    AddCommGroup (Space U g) := by
  rcases g with g | (g | g | g) | g <;> unfold Space <;> infer_instance

instance (U : Fin 3 → Submodule K F) {r x y z l : ℕ} (g : Groups r x y z l) :
    Module K (Space U g) := by
  rcases g with g | (g | g | g) | g <;> unfold Space <;> infer_instance

instance (U : Fin 3 → Submodule K F) [FiniteDimensional K F]
    {r x y z l : ℕ} (g : Groups r x y z l) : FiniteDimensional K (Space U g) := by
  rcases g with g | (g | g | g) | g <;> unfold Space <;> infer_instance

noncomputable instance (U : Fin 3 → Submodule K F) [Finite K] [FiniteDimensional K F]
    {r x y z l : ℕ} (g : Groups r x y z l) : Fintype (Space U g) := by
  letI : Finite (Space U g) := Finite.of_injective
    (Module.finBasis K (Space U g)).equivFun (Module.finBasis K (Space U g)).equivFun.injective
  exact Fintype.ofFinite _

def relationProjection (U : Fin 3 → Submodule K F) (i : Fin 3) :
    alignedRelation (U 0) (U 1) (U 2) →ₗ[K] F :=
  (match i with
    | 0 => LinearMap.fst K F (F × F)
    | 1 => (LinearMap.fst K F F).comp (LinearMap.snd K F (F × F))
    | 2 => (LinearMap.snd K F F).comp (LinearMap.snd K F (F × F))).comp
      (alignedRelation (U 0) (U 1) (U 2)).subtype

def projection (U : Fin 3 → Submodule K F) (i : Fin 3) {r x y z l : ℕ} :
    (g : Groups r x y z l) → Space U g →ₗ[K] F
  | Sum.inl _ => (U 0 ⊓ U 1 ⊓ U 2).subtype
  | Sum.inr (Sum.inl (Sum.inl _)) => (U 1 ⊓ U 2).subtype
  | Sum.inr (Sum.inl (Sum.inr (Sum.inl _))) => (U 0 ⊓ U 2).subtype
  | Sum.inr (Sum.inl (Sum.inr (Sum.inr _))) => (U 0 ⊓ U 1).subtype
  | Sum.inr (Sum.inr _) => relationProjection U i

def enlarged (U : Fin 3 → Submodule K F) : Fin 3 → Submodule K F :=
  ![U 0 ⊓ (U 1 ⊔ U 2), U 1 ⊓ (U 0 ⊔ U 2), U 2 ⊓ (U 0 ⊔ U 1)]

def allowed (U : Fin 3 → Submodule K F) (i : Fin 3) {r x y z l : ℕ} :
    Groups r x y z l → Submodule K F
  | Sum.inl _ => U 0 ⊓ U 1 ⊓ U 2
  | Sum.inr (Sum.inl (Sum.inl _)) => U 1 ⊓ U 2
  | Sum.inr (Sum.inl (Sum.inr (Sum.inl _))) => U 0 ⊓ U 2
  | Sum.inr (Sum.inl (Sum.inr (Sum.inr _))) => U 0 ⊓ U 1
  | Sum.inr (Sum.inr _) => enlarged U i

/-- Every admissible local column has a parameter lift. -/
theorem projection_lift (U : Fin 3 → Submodule K F) (i : Fin 3)
    {r x y z l : ℕ} (g : Groups r x y z l) (v : F) (hv : v ∈ allowed U i g) :
    ∃ t : Space U g, projection U i g t = v := by
  rcases g with g | (g | g | g) | g
  · exact ⟨⟨v,hv⟩,rfl⟩
  · exact ⟨⟨v,hv⟩,rfl⟩
  · exact ⟨⟨v,hv⟩,rfl⟩
  · exact ⟨⟨v,hv⟩,rfl⟩
  · fin_cases i
    · exact alignedRelation_lift_first _ _ _ v hv
    · exact alignedRelation_lift_second _ _ _ v hv
    · exact alignedRelation_lift_third _ _ _ v hv

/-- Incident shared columns belong to the user's signal subspace. -/
theorem local_allowed_le (U : Fin 3 → Submodule K F)
    {r x y z l : ℕ} (i : Fin 3) (j : Local r x y z l i) :
    allowed U i (inclusion r x y z l i j) ≤ U i := by
  fin_cases i <;> rcases j with j | (j | j) | j
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left
  · exact inf_le_left
  · exact inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right
  · exact inf_le_left
  · exact inf_le_left
  · exact inf_le_right
  · exact inf_le_right
  · exact inf_le_right
  · exact inf_le_left

theorem projection_mem (U : Fin 3 → Submodule K F) (i : Fin 3)
    {r x y z l : ℕ} (g : Groups r x y z l) (t : Space U g) :
    projection U i g t ∈ allowed U i g := by
  rcases g with g | (g | g | g) | g
  · exact t.property
  · exact t.property
  · exact t.property
  · exact t.property
  · obtain ⟨h₀,h₁,h₂,he⟩ := t.property
    fin_cases i
    · refine ⟨h₀,Submodule.mem_sup.mpr ⟨-(t.1.2.1), (U 1).neg_mem h₁,t.1.2.2,h₂,?_⟩⟩
      change -t.1.2.1+t.1.2.2=t.1.1
      rw [← he]; abel
    · refine ⟨h₁,Submodule.mem_sup.mpr ⟨-(t.1.1), (U 0).neg_mem h₀,t.1.2.2,h₂,?_⟩⟩
      change -t.1.1+t.1.2.2=t.1.2.1
      rw [← he]; abel
    · exact ⟨h₂,Submodule.mem_sup.mpr ⟨t.1.1,h₀,t.1.2.1,h₁,he⟩⟩

theorem local_projection_mem (U : Fin 3 → Submodule K F)
    {r x y z l : ℕ} (i : Fin 3) (j : Local r x y z l i)
    (t : Space U (inclusion r x y z l i j)) :
    projection U i (inclusion r x y z l i j) t ∈ U i :=
  local_allowed_le U i j (projection_mem U i _ t)

theorem aligned_add (U : Fin 3 → Submodule K F)
    (t : alignedRelation (U 0) (U 1) (U 2)) :
    relationProjection U 0 t + relationProjection U 1 t = relationProjection U 2 t :=
  t.property.2.2.2

/-- Separate invertible column witnesses derived from the numerical scalar
allocation, before any field-size coordination. -/
theorem separate_incidence_witnesses [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i) (s : ScalarAllocation A U) :
    ∃ (indiv : ∀ i, Fin (s.h i) → F)
      (selected : ∀ i, Local s.r s.x s.y s.z s.al i → F),
      (∀ i j, indiv i j ∈ U i) ∧
      (∀ i j, selected i j ∈ allowed U i (inclusion s.r s.x s.y s.z s.al i j)) ∧
      (∀ i, LinearIndependent K (Sum.elim
        (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) (indiv i)) (selected i))) := by
  have hw (i : Fin 3) : ∃ (w : Fin (s.h i) → F)
      (v : Local s.r s.x s.y s.z s.al i → F),
      (∀ j, w j ∈ U i) ∧
      (∀ j, v j ∈ allowed U i (inclusion s.r s.x s.y s.z s.al i j)) ∧
      LinearIndependent K (Sum.elim
        (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) w) v) := by
    fin_cases i
    · obtain ⟨c,p,q,v,w,hc,hp,hq,hv,hw,hi,_⟩ := exists_user_column_witness
        (A 0) (U 0 ⊓ U 1 ⊓ U 2) (U 0 ⊓ U 1) (U 0 ⊓ U 2)
        (U 0 ⊓ (U 1 ⊔ U 2)) (U 0) s.r s.z s.y s.al (s.h 0)
        (hAU 0) (inf_le_left) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (inf_le_inf le_rfl le_sup_left) (inf_le_inf le_rfl le_sup_right) inf_le_left (s.hcommon 0)
        (s.hpair01.trans (min_le_left _ _)) (s.hpair02.trans (min_le_left _ _))
        (by simpa [Allocation.pairSumRank,inf_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hpairs0)
        (by simpa [Allocation.enlargedRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hal0)
        (by simpa [Allocation.demandRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.total0)
      refine ⟨w,Sum.elim c (Sum.elim (Sum.elim p q) v),hw,?_,hi⟩
      rintro (j | (j | j) | j)
      · exact hc j
      · exact hp j
      · exact hq j
      · exact hv j
    · obtain ⟨c,p,q,v,w,hc,hp,hq,hv,hw,hi,_⟩ := exists_user_column_witness
        (A 1) (U 0 ⊓ U 1 ⊓ U 2) (U 0 ⊓ U 1) (U 1 ⊓ U 2)
        (U 1 ⊓ (U 0 ⊔ U 2)) (U 1) s.r s.z s.x s.al (s.h 1)
        (hAU 1) (inf_le_left) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf inf_le_right (inf_le_left.trans le_sup_left)) (inf_le_inf le_rfl le_sup_right) inf_le_left (s.hcommon 1)
        (s.hpair01.trans (min_le_right _ _)) (s.hpair12.trans (min_le_left _ _))
        (by simpa [Allocation.pairSumRank,inf_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hpairs1)
        (by simpa [Allocation.enlargedRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hal1)
        (by simpa [Allocation.demandRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.total1)
      refine ⟨w,Sum.elim c (Sum.elim (Sum.elim p q) v),hw,?_,hi⟩
      rintro (j | (j | j) | j)
      · exact hc j
      · exact hp j
      · exact hq j
      · exact hv j
    · obtain ⟨c,p,q,v,w,hc,hp,hq,hv,hw,hi,_⟩ := exists_user_column_witness
        (A 2) (U 0 ⊓ U 1 ⊓ U 2) (U 0 ⊓ U 2) (U 1 ⊓ U 2)
        (U 2 ⊓ (U 0 ⊔ U 1)) (U 2) s.r s.y s.x s.al (s.h 2)
        (hAU 2) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf inf_le_right (inf_le_left.trans le_sup_left)) (le_inf inf_le_right (inf_le_left.trans le_sup_right)) inf_le_left (s.hcommon 2)
        (s.hpair02.trans (min_le_right _ _)) (s.hpair12.trans (min_le_right _ _))
        (by simpa [Allocation.pairSumRank,inf_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hpairs2)
        (by simpa [Allocation.enlargedRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hal2)
        (by simpa [Allocation.demandRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.total2)
      refine ⟨w,Sum.elim c (Sum.elim (Sum.elim p q) v),hw,?_,hi⟩
      rintro (j | (j | j) | j)
      · exact hc j
      · exact hp j
      · exact hq j
      · exact hv j
  choose indiv selected hi hs hli using hw
  exact ⟨indiv,selected,hi,hs,hli⟩

end UploadBroadcast.ScalarIncidence
