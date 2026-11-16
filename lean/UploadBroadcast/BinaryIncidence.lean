import UploadBroadcast.ScalarIncidence
import UploadBroadcast.BinaryCommon

namespace UploadBroadcast.BinaryIncidence
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

abbrev Remaining (x y z l : ℕ) := (Fin x ⊕ (Fin y ⊕ Fin z)) ⊕ Fin l

def Local (x y z l : ℕ) : Fin 3 → Type
  | 0 => (Fin z ⊕ Fin y) ⊕ Fin l
  | 1 => (Fin z ⊕ Fin x) ⊕ Fin l
  | 2 => (Fin y ⊕ Fin x) ⊕ Fin l

instance (x y z l : ℕ) (i : Fin 3) : Fintype (Local x y z l i) := by
  match i with
  | 0 => exact inferInstanceAs (Fintype ((Fin z ⊕ Fin y) ⊕ Fin l))
  | 1 => exact inferInstanceAs (Fintype ((Fin z ⊕ Fin x) ⊕ Fin l))
  | 2 => exact inferInstanceAs (Fintype ((Fin y ⊕ Fin x) ⊕ Fin l))

instance (x y z l : ℕ) (i : Fin 3) : DecidableEq (Local x y z l i) := by
  match i with
  | 0 => exact inferInstanceAs (DecidableEq ((Fin z ⊕ Fin y) ⊕ Fin l))
  | 1 => exact inferInstanceAs (DecidableEq ((Fin z ⊕ Fin x) ⊕ Fin l))
  | 2 => exact inferInstanceAs (DecidableEq ((Fin y ⊕ Fin x) ⊕ Fin l))

def inclusion (x y z l : ℕ) : (i : Fin 3) → Local x y z l i → Remaining x y z l
  | 0 => Sum.elim (Sum.elim (fun j => Sum.inl (Sum.inr (Sum.inr j)))
      (fun j => Sum.inl (Sum.inr (Sum.inl j)))) Sum.inr
  | 1 => Sum.elim (Sum.elim (fun j => Sum.inl (Sum.inr (Sum.inr j)))
      (fun j => Sum.inl (Sum.inl j))) Sum.inr
  | 2 => Sum.elim (Sum.elim (fun j => Sum.inl (Sum.inr (Sum.inl j)))
      (fun j => Sum.inl (Sum.inl j))) Sum.inr

theorem inclusion_injective (x y z l : ℕ) (i : Fin 3) :
    Function.Injective (inclusion x y z l i) := by
  fin_cases i <;> intro a b h <;>
    rcases a with (a | a) | a <;> rcases b with (b | b) | b <;> simp_all [inclusion]

abbrev Space (U : Fin 3 → Submodule K F) {x y z l : ℕ} (g : Remaining x y z l) :=
  ScalarIncidence.Space U (r := 0) (Sum.inr g)

abbrev projection (U : Fin 3 → Submodule K F) (i : Fin 3)
    {x y z l : ℕ} (g : Remaining x y z l) : Space U g →ₗ[K] F :=
  ScalarIncidence.projection U i (r := 0) (Sum.inr g)

abbrev allowed (U : Fin 3 → Submodule K F) (i : Fin 3)
    {x y z l : ℕ} (g : Remaining x y z l) : Submodule K F :=
  ScalarIncidence.allowed U i (r := 0) (Sum.inr g)

theorem projection_lift (U : Fin 3 → Submodule K F) (i : Fin 3)
    {x y z l : ℕ} (g : Remaining x y z l) (v : F) (hv : v ∈ allowed U i g) :
    ∃ t : Space U g, projection U i g t = v :=
  ScalarIncidence.projection_lift U i _ v hv

theorem local_projection_mem (U : Fin 3 → Submodule K F)
    {x y z l : ℕ} (i : Fin 3) (j : Local x y z l i)
    (t : Space U (inclusion x y z l i j)) :
    projection U i (inclusion x y z l i j) t ∈ U i := by
  fin_cases i <;> rcases j with (j | j) | j
  all_goals first
    | exact ScalarIncidence.local_projection_mem U 0 (r := 0) (Sum.inr (Sum.inl (Sum.inl j))) t
    | exact ScalarIncidence.local_projection_mem U 0 (r := 0) (Sum.inr (Sum.inl (Sum.inr j))) t
    | exact ScalarIncidence.local_projection_mem U 0 (r := 0) (Sum.inr (Sum.inr j)) t
    | exact ScalarIncidence.local_projection_mem U 1 (r := 0) (Sum.inr (Sum.inl (Sum.inl j))) t
    | exact ScalarIncidence.local_projection_mem U 1 (r := 0) (Sum.inr (Sum.inl (Sum.inr j))) t
    | exact ScalarIncidence.local_projection_mem U 1 (r := 0) (Sum.inr (Sum.inr j)) t
    | exact ScalarIncidence.local_projection_mem U 2 (r := 0) (Sum.inr (Sum.inl (Sum.inl j))) t
    | exact ScalarIncidence.local_projection_mem U 2 (r := 0) (Sum.inr (Sum.inl (Sum.inr j))) t
    | exact ScalarIncidence.local_projection_mem U 2 (r := 0) (Sum.inr (Sum.inr j)) t

def pair_support {x y z : ℕ} : Fin x ⊕ (Fin y ⊕ Fin z) → Finset (Fin 3)
  | Sum.inl _ => {1,2}
  | Sum.inr (Sum.inl _) => {0,2}
  | Sum.inr (Sum.inr _) => {0,1}

theorem pair_support_card_le {x y z : ℕ} (g : Fin x ⊕ (Fin y ⊕ Fin z)) :
    (pair_support g).card ≤ 2 := by
  rcases g with g | g | g <;> simp [pair_support]

theorem pair_not_incident {x y z l : ℕ} (g : Fin x ⊕ (Fin y ⊕ Fin z))
    (i : Fin 3) (hi : i ∉ pair_support g) (j : Local x y z l i) :
    inclusion x y z l i j ≠ Sum.inl g := by
  fin_cases i <;> rcases g with g | g | g <;> rcases j with (j | j) | j <;>
    simp_all [pair_support,inclusion]

def alignedIndex {x y z l : ℕ} : (i : Fin 3) → Fin l → Local x y z l i
  | 0 => Sum.inr
  | 1 => Sum.inr
  | 2 => Sum.inr

theorem inclusion_aligned {x y z l : ℕ} (i : Fin 3) (j : Fin l) :
    inclusion x y z l i (alignedIndex i j) = Sum.inr j := by
  fin_cases i <;> rfl

theorem projection_aligned (U : Fin 3 → Submodule K F) {x y z l : ℕ}
    (i : Fin 3) (j : Fin l) :
    projection U i (x:=x) (y:=y) (z:=z) (Sum.inr j) = ScalarIncidence.relationProjection U i := rfl

/-- Move the fixed common block next to the fixed side-information block. -/
theorem independent_move_common {IA IC IH IR : Type*}
    (a : IA → F) (c : IC → F) (h : IH → F) (r : IR → F)
    (hi : LinearIndependent K (Sum.elim (Sum.elim a h) (Sum.elim c r))) :
    LinearIndependent K (Sum.elim (Sum.elim (Sum.elim a c) h) r) := by
  let e : ((IA ⊕ IC) ⊕ IH) ⊕ IR → (IA ⊕ IH) ⊕ (IC ⊕ IR) :=
    Sum.elim (Sum.elim (Sum.elim (fun a => Sum.inl (Sum.inl a))
      (fun c => Sum.inr (Sum.inl c))) (fun h => Sum.inl (Sum.inr h)))
      (fun r => Sum.inr (Sum.inr r))
  have he : Function.Injective e := by
    intro x y hxy
    rcases x with ((a | c) | h) | r <;> rcases y with ((a' | c') | h') | r' <;>
      simp_all [e]
  convert hi.comp e he using 1
  funext x
  rcases x with ((a | c) | h) | r <;> rfl

/-- Genuine separate-user witnesses sharing one fixed common basis, under
exactly the binary separation hypothesis and maximal-common allocation. -/
theorem separate_incidence_witnesses [FiniteDimensional K F]
    (A U : Fin 3 → Submodule K F) (hAU : ∀ i, A i ≤ U i)
    (hsep : A 0 ⊓ (A 1 ⊔ A 2) = ⊥) (s : ScalarAllocation A U)
    (hr : s.r = Allocation.commonRank A U) :
    ∃ (c : Fin s.r → F) (indiv : ∀ i, Fin (s.h i) → F)
      (selected : ∀ i, Local s.x s.y s.z s.al i → F),
      (∀ j, c j ∈ U 0 ⊓ U 1 ⊓ U 2) ∧
      (∀ i j, indiv i j ∈ U i) ∧
      (∀ i j, selected i j ∈ allowed U i (inclusion s.x s.y s.z s.al i j)) ∧
      (∀ i, LinearIndependent K (Sum.elim
        (Sum.elim (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) c) (indiv i))
        (selected i))) := by
  obtain ⟨C,hCT,hCr,hAC⟩ := exists_separated_common_block A U hsep
  have hCr' : Module.finrank K C = s.r := hCr.trans hr.symm
  let bc := Module.finBasisOfFinrankEq K C hCr'
  let c : Fin s.r → F := fun j => bc j
  have hc : LinearIndependent K c := bc.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hcs : Submodule.span K (Set.range c) = C := span_submodule_basis C bc
  have hw (i : Fin 3) : ∃ (w : Fin (s.h i) → F)
      (v : Local s.x s.y s.z s.al i → F),
      (∀ j, w j ∈ U i) ∧
      (∀ j, v j ∈ allowed U i (inclusion s.x s.y s.z s.al i j)) ∧
      LinearIndependent K (Sum.elim
        (Sum.elim (Sum.elim (fun j => (Module.finBasis K (A i) j : F)) c) w) v) := by
    fin_cases i
    · obtain ⟨p,q,v,w,hp,hq,hv,hw,hi,_⟩ := exists_user_column_witness_fixed_common
        (A 0) C (U 0 ⊓ U 1) (U 0 ⊓ U 2)
        (U 0 ⊓ (U 1 ⊔ U 2)) (U 0) c s.z s.y s.al (s.h 0) hc hcs
        (hAU 0) (hCT.trans (inf_le_left)) (hCT.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
        (inf_le_inf le_rfl le_sup_left) (inf_le_inf le_rfl le_sup_right) inf_le_left (hAC 0)
        (by rw [hCr']; exact s.hpair01.trans (min_le_left _ _)) (by rw [hCr']; exact s.hpair02.trans (min_le_left _ _))
        (by simpa [hCr',Allocation.pairSumRank,inf_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hpairs0)
        (by simpa [hCr',Allocation.enlargedRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hal0)
        (by simpa [hCr',Allocation.demandRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.total0)
      refine ⟨w,Sum.elim (Sum.elim p q) v,hw,?_,independent_move_common _ _ _ _ hi⟩
      rintro ((j | j) | j)
      · exact hp j
      · exact hq j
      · exact hv j
    · obtain ⟨p,q,v,w,hp,hq,hv,hw,hi,_⟩ := exists_user_column_witness_fixed_common
        (A 1) C (U 0 ⊓ U 1) (U 1 ⊓ U 2)
        (U 1 ⊓ (U 0 ⊔ U 2)) (U 1) c s.z s.x s.al (s.h 1) hc hcs
        (hAU 1) (hCT.trans (inf_le_left)) (hCT.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
        (le_inf inf_le_right (inf_le_left.trans le_sup_left)) (inf_le_inf le_rfl le_sup_right) inf_le_left (hAC 1)
        (by rw [hCr']; exact s.hpair01.trans (min_le_right _ _)) (by rw [hCr']; exact s.hpair12.trans (min_le_left _ _))
        (by simpa [hCr',Allocation.pairSumRank,inf_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hpairs1)
        (by simpa [hCr',Allocation.enlargedRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hal1)
        (by simpa [hCr',Allocation.demandRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.total1)
      refine ⟨w,Sum.elim (Sum.elim p q) v,hw,?_,independent_move_common _ _ _ _ hi⟩
      rintro ((j | j) | j)
      · exact hp j
      · exact hq j
      · exact hv j
    · obtain ⟨p,q,v,w,hp,hq,hv,hw,hi,_⟩ := exists_user_column_witness_fixed_common
        (A 2) C (U 0 ⊓ U 2) (U 1 ⊓ U 2)
        (U 2 ⊓ (U 0 ⊔ U 1)) (U 2) c s.y s.x s.al (s.h 2) hc hcs
        (hAU 2) (hCT.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (hCT.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
        (le_inf inf_le_right (inf_le_left.trans le_sup_left)) (le_inf inf_le_right (inf_le_left.trans le_sup_right)) inf_le_left (hAC 2)
        (by rw [hCr']; exact s.hpair02.trans (min_le_right _ _)) (by rw [hCr']; exact s.hpair12.trans (min_le_right _ _))
        (by simpa [hCr',Allocation.pairSumRank,inf_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hpairs2)
        (by simpa [hCr',Allocation.enlargedRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.hal2)
        (by simpa [hCr',Allocation.demandRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using s.total2)
      refine ⟨w,Sum.elim (Sum.elim p q) v,hw,?_,independent_move_common _ _ _ _ hi⟩
      rintro ((j | j) | j)
      · exact hp j
      · exact hq j
      · exact hv j
  choose indiv selected hi hs hli using hw
  exact ⟨c,indiv,selected,fun j => hCT (bc j).property,hi,hs,hli⟩

end UploadBroadcast.BinaryIncidence
