import UploadBroadcast.RelayProfileTransport
import UploadBroadcast.OptimalRelaySeparation
import Mathlib.LinearAlgebra.Pi

/-! Actual finite products of coefficient tasks, their relay subspaces, and
all fifteen entries. No profile or selected-relay existence is assumed. -/
namespace UploadBroadcast.FiniteRelayAssembly
open Module
open scoped BigOperators
variable {K I : Type*} {F : I → Type*} [Field K]
  [∀ t, AddCommGroup (F t)] [∀ t, Module K (F t)]

abbrev space (A : (t : I) → Submodule K (F t)) : Submodule K (∀ t, F t) :=
  Submodule.pi Set.univ A

theorem space_inf (A B : (t : I) → Submodule K (F t)) :
    space (fun t => A t ⊓ B t) = space A ⊓ space B := by
  ext x
  simp [space,forall_and]

theorem space_sup (A B : (t : I) → Submodule K (F t)) :
    space (fun t => A t ⊔ B t) = space A ⊔ space B := by
  classical
  apply le_antisymm
  · intro x hx
    have hh : ∀ t, ∃ a ∈ A t, ∃ b ∈ B t, a+b=x t :=
      fun t => Submodule.mem_sup.mp (hx t trivial)
    choose a ha b hb hab using hh
    exact Submodule.mem_sup.mpr ⟨a,(by simpa [space] using ha),
      b,(by simpa [space] using hb),funext hab⟩
  · exact sup_le (Submodule.pi_mono fun _ _ => le_sup_left)
      (Submodule.pi_mono fun _ _ => le_sup_right)

def spaceEquiv (A : (t : I) → Submodule K (F t)) :
    space A ≃ₗ[K] (∀ t, A t) where
  toFun x t := ⟨x.1 t,x.2 t trivial⟩
  invFun x := ⟨fun t => (x t).1,fun t _ => (x t).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def task (T : (t : I) → Task K (F t)) : Task K (∀ t, F t) where
  A i := space (fun t => (T t).A i)
  U i := space (fun t => (T t).U i)
  side_le_signal i := Submodule.pi_mono fun t _ => (T t).side_le_signal i
  feasible i := by
    have h := Submodule.pi_mono (s := Set.univ) (fun t _ => (T t).feasible i)
    simpa only [Profile.three_iSup,space_sup] using h

theorem locally_generated (T : (t : I) → Task K (F t))
    (P : (t : I) → Submodule K (F t)) (hP : ∀ t, (T t).LocallyGenerated (P t)) :
    (task T).LocallyGenerated (space P) := by
  unfold Task.LocallyGenerated at hP ⊢
  simp only [Profile.three_iSup] at hP ⊢
  change space P = _
  simp only [task,← space_inf,← space_sup]
  exact congrArg space (funext hP)

theorem relay_feasible (T : (t : I) → Task K (F t))
    (P : (t : I) → Submodule K (F t)) (hP : ∀ t, (T t).RelayFeasible (P t)) :
    (task T).RelayFeasible (space P) := by
  intro i
  change space _ ≤ space _ ⊔ space _
  rw [← space_sup]
  exact Submodule.pi_mono fun t _ => hP t i

theorem inducedTask_eq (T : (t : I) → Task K (F t))
    (P : (t : I) → Submodule K (F t)) (hP : ∀ t, (T t).LocallyGenerated (P t)) :
    NonzeroDefectRelays.inducedTask (task T) (space P) (locally_generated T P hP) =
      task (fun t => NonzeroDefectRelays.inducedTask (T t) (P t) (hP t)) := by
  have ha : (NonzeroDefectRelays.inducedTask (task T) (space P) (locally_generated T P hP)).A =
      (task (fun t => NonzeroDefectRelays.inducedTask (T t) (P t) (hP t))).A := by
    funext i
    exact (space_inf _ _).symm
  have hu : (NonzeroDefectRelays.inducedTask (task T) (space P) (locally_generated T P hP)).U =
      (task (fun t => NonzeroDefectRelays.inducedTask (T t) (P t) (hP t))).U := by
    funext i
    exact (space_inf _ _).symm
  cases h : NonzeroDefectRelays.inducedTask (task T) (space P) (locally_generated T P hP)
  cases h' : task (fun t => NonzeroDefectRelays.inducedTask (T t) (P t) (hP t))
  simp_all only [Task.mk.injEq]

variable [Fintype I] [∀ t, FiniteDimensional K (F t)]

theorem finrank_space (A : (t : I) → Submodule K (F t)) :
    finrank K (space A) = ∑ t, finrank K (A t) := by
  rw [(spaceEquiv A).finrank_eq,Module.finrank_pi_fintype]

theorem condRank_space (C A : (t : I) → Submodule K (F t)) :
    condRank (space C) (space A) = ∑ t, condRank (C t) (A t) := by
  unfold condRank
  rw [← space_sup,finrank_space,finrank_space]
  exact (Finset.sum_tsub_distrib Finset.univ (fun t _ => Submodule.finrank_mono (show A t ≤ A t ⊔ C t from le_sup_left))).symm

theorem totalDemand_task (T : (t : I) → Task K (F t)) :
    Profile.totalDemand (task T) = ∑ t, Profile.totalDemand (T t) := by
  unfold Profile.totalDemand
  simp only [task,finrank_space]
  have h (i : Three) : (∑ t, finrank K ((T t).U i))-(∑ t, finrank K ((T t).A i)) =
      ∑ t, (finrank K ((T t).U i)-finrank K ((T t).A i)) := by
    exact (Finset.sum_tsub_distrib Finset.univ (fun t _ => Submodule.finrank_mono ((T t).side_le_signal i))).symm
  simp_rw [h]
  exact Finset.sum_comm

theorem firstEntry_task (T : (t : I) → Task K (F t)) (i j k : Three) :
    Profile.firstEntry (task T) i j k = ∑ t, Profile.firstEntry (T t) i j k := by
  unfold Profile.firstEntry
  rw [totalDemand_task]
  simp only [task,← space_inf,← space_sup,condRank_space,
    Nat.cast_sum,Finset.sum_sub_distrib]

theorem secondEntry_task (T : (t : I) → Task K (F t)) (i j k l : Three) :
    Profile.secondEntry (task T) i j k l = ∑ t, Profile.secondEntry (T t) i j k l := by
  unfold Profile.secondEntry
  rw [totalDemand_task]
  simp only [task,← space_inf,← space_sup,condRank_space,
    Nat.cast_sum,Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_add_distrib]

theorem entry_task (T : (t : I) → Task K (F t)) (r : Profile.Index) :
    Profile.entry (task T) r = ∑ t, Profile.entry (T t) r := by
  cases r with
  | inl r => exact firstEntry_task T _ _ _
  | inr r => exact secondEntry_task T _ _ _ _

theorem inducedRelay_entry (T : (t : I) → Task K (F t))
    (P : (t : I) → Submodule K (F t)) (hP : ∀ t, (T t).LocallyGenerated (P t))
    (r : Profile.Index) :
    Profile.entry ((task T).inducedRelay (space P) (locally_generated T P hP)) r =
      ∑ t, Profile.entry ((T t).inducedRelay (P t) (hP t)) r := by
  simp_rw [Task.inducedRelay_entry]
  rw [inducedTask_eq,entry_task]

section Product
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem inducedTask_product (T : Task K V) (R : Task K W)
    (P : Submodule K V) (Q : Submodule K W)
    (hP : T.LocallyGenerated P) (hQ : R.LocallyGenerated Q) :
    NonzeroDefectRelays.inducedTask (Profile.directSum T R) (P.prod Q)
      (OptimalRelaySeparation.product_locally_generated T R P Q hP hQ) =
      Profile.directSum (NonzeroDefectRelays.inducedTask T P hP)
        (NonzeroDefectRelays.inducedTask R Q hQ) := by
  have ha : (NonzeroDefectRelays.inducedTask (Profile.directSum T R) (P.prod Q)
      (OptimalRelaySeparation.product_locally_generated T R P Q hP hQ)).A =
      (Profile.directSum (NonzeroDefectRelays.inducedTask T P hP)
        (NonzeroDefectRelays.inducedTask R Q hQ)).A := by
    funext i
    exact Submodule.prod_inf_prod _ _ _ _
  have hu : (NonzeroDefectRelays.inducedTask (Profile.directSum T R) (P.prod Q)
      (OptimalRelaySeparation.product_locally_generated T R P Q hP hQ)).U =
      (Profile.directSum (NonzeroDefectRelays.inducedTask T P hP)
        (NonzeroDefectRelays.inducedTask R Q hQ)).U := by
    funext i
    exact Submodule.prod_inf_prod _ _ _ _
  cases h : NonzeroDefectRelays.inducedTask (Profile.directSum T R) (P.prod Q)
      (OptimalRelaySeparation.product_locally_generated T R P Q hP hQ)
  cases h' : Profile.directSum (NonzeroDefectRelays.inducedTask T P hP)
      (NonzeroDefectRelays.inducedTask R Q hQ)
  simp_all only [Task.mk.injEq]

theorem product_inducedRelay_entry (T : Task K V) (R : Task K W)
    (P : Submodule K V) (Q : Submodule K W)
    (hP : T.LocallyGenerated P) (hQ : R.LocallyGenerated Q) (r : Profile.Index) :
    Profile.entry ((Profile.directSum T R).inducedRelay (P.prod Q)
      (OptimalRelaySeparation.product_locally_generated T R P Q hP hQ)) r =
      Profile.entry (T.inducedRelay P hP) r + Profile.entry (R.inducedRelay Q hQ) r := by
  simp_rw [Task.inducedRelay_entry]
  rw [inducedTask_product,Profile.entry_directSum]

end Product
end UploadBroadcast.FiniteRelayAssembly
