import UploadBroadcast.ScalarBroadcast
import UploadBroadcast.PairSelection

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Coordinate shared coefficient blocks while keeping each user's completion
columns fixed. An injective incidence map says each parameter group supplies
at most one column to a given user. -/
theorem coordinate_block_families
    {G I : Type*} [DecidableEq G] [Fintype G] [Fintype I] [Fintype K]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (H J : I → Type*) [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (e : ∀ i, J i → G) (he : ∀ i, Function.Injective (e i))
    (fixed : ∀ i, H i → F)
    (l : ∀ i j, V (e i j) →ₗ[K] F)
    (hw : ∀ i, ∃ a : (g : G) → V g,
      LinearIndependent K (Sum.elim (fixed i) (fun j => l i j (a (e i j)))))
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ a : (g : G) → V g, ∀ i,
      LinearIndependent K (Sum.elim (fixed i) (fun j => l i j (a (e i j)))) := by
  classical
  apply homogeneous_independent_coordination V (fun i => H i ⊕ J i)
    (fun i a => Sum.elim (fixed i) (fun j => l i j (a (e i j)))) ?_ hw hcount
  intro i g a
  by_cases hg : ∃ j, e i j = g
  · obtain ⟨j,rfl⟩ := hg
    refine Or.inr ⟨Sum.inr j,l i j,fun x => ?_⟩
    funext k
    cases k with
    | inl h => simp
    | inr k =>
      by_cases hk : k = j
      · subst k; simp
      · have hne : e i k ≠ e i j := fun h => hk (he i h)
        simp [Function.update_of_ne, hk, hne]
  · refine Or.inl (fun x => ?_)
    funext k
    cases k with
    | inl h => rfl
    | inr j =>
      have hne : e i j ≠ g := fun h => hg ⟨j,h⟩
      simp [Function.update_of_ne hne]

/-- Extend dependent parameter values along an injective incidence map. -/
theorem exists_parameter_extension {G J : Type*} (V : G → Type*)
    [∀ g, Zero (V g)] (e : J → G) (he : Function.Injective e)
    (v : ∀ j, V (e j)) : ∃ a : ∀ g, V g, ∀ j, a (e j) = v j := by
  classical
  let a : ∀ g, V g := fun g => if h : ∃ j, e j = g then
    (Classical.choose_spec h) ▸ v (Classical.choose h) else 0
  refine ⟨a,fun j => ?_⟩
  dsimp only [a]
  rw [dif_pos (show ∃ k, e k = e j from ⟨j,rfl⟩)]
  have htransport (k : J) (h : e k = e j) : h ▸ v k = v j := by
    have hk := he h
    subst k
    rfl
  exact htransport _ _

/-- Separate admissible column witnesses suffice: lift each selected column,
extend its parameters to absent groups, then reconcile all users. -/
theorem coordinate_lifted_block_families
    {G I : Type*} [DecidableEq G] [Fintype G] [Fintype I] [Fintype K]
    (V : G → Type*) [∀ g, AddCommGroup (V g)] [∀ g, Module K (V g)]
    [∀ g, Fintype (V g)] [∀ g, FiniteDimensional K (V g)]
    (H J : I → Type*) [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    (e : ∀ i, J i → G) (he : ∀ i, Function.Injective (e i))
    (fixed : ∀ i, H i → F) (l : ∀ i j, V (e i j) →ₗ[K] F)
    (selected : ∀ i, J i → F)
    (hlocal : ∀ i, LinearIndependent K (Sum.elim (fixed i) (selected i)))
    (hlift : ∀ i j, ∃ v, l i j v = selected i j)
    (hcount : Fintype.card I ≤ Fintype.card K) :
    ∃ a : (g : G) → V g, ∀ i,
      LinearIndependent K (Sum.elim (fixed i) (fun j => l i j (a (e i j)))) := by
  classical
  apply coordinate_block_families V H J e he fixed l ?_ hcount
  intro i
  choose v hv using hlift i
  obtain ⟨a,ha⟩ := exists_parameter_extension V (e i) (he i) v
  refine ⟨a,?_⟩
  have hfun : (fun j => l i j (a (e i j))) = selected i := by
    funext j
    rw [ha j,hv j]
  rw [hfun]
  exact hlocal i

/-- A full-size independent coefficient family contained in a signal space
spans that space. -/
theorem independent_family_span_eq [FiniteDimensional K F]
    {J : Type*} [Fintype J] (U : Submodule K F) (v : J → F)
    (hv : LinearIndependent K v) (hmem : ∀ j, v j ∈ U)
    (hcard : Fintype.card J = Module.finrank K U) :
    Submodule.span K (Set.range v) = U := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hmem j)
  · rw [finrank_span_eq_card hv,hcard]

/-- A finite coefficient family gives a scalar code with its exact number
of listed coordinates, irrespective of the chosen finite index type. -/
theorem scalarBroadcastCode_of_indexed_span {J : Type*} [Fintype J]
    (A U : Fin 3 → Submodule K F) (v : J → F)
    (hspan : ∀ i, U i ≤ A i ⊔ Submodule.span K (Set.range v)) :
    Nonempty (ScalarBroadcastCode A U (Fintype.card J)) := by
  classical
  let e := Fintype.equivFin J
  apply scalarBroadcastCode_of_span A U (v ∘ e.symm)
  have he : Set.range (v ∘ e.symm) = Set.range v :=
    by
      ext x
      constructor
      · rintro ⟨j,rfl⟩; exact ⟨e.symm j,rfl⟩
      · rintro ⟨j,rfl⟩; exact ⟨e j,by simp⟩
  simpa only [he] using hspan

/-- Convert jointly independent coefficient blocks into actual scalar
encoders and linear decoders using an explicit finite transmitted family. -/
theorem scalarBroadcastCode_of_independent_columns [FiniteDimensional K F]
    {J : Fin 3 → Type*} [∀ i, Fintype (J i)]
    {T : Type*} [Fintype T]
    (A U : Fin 3 → Submodule K F)
    (columns : ∀ i, J i → F) (transmitted : T → F)
    (hind : ∀ i, LinearIndependent K (columns i))
    (hmem : ∀ i j, columns i j ∈ U i)
    (hcard : ∀ i, Fintype.card (J i) = Module.finrank K (U i))
    (hdecode : ∀ i j, columns i j ∈ A i ⊔ Submodule.span K (Set.range transmitted)) :
    Nonempty (ScalarBroadcastCode A U (Fintype.card T)) := by
  apply scalarBroadcastCode_of_indexed_span A U transmitted
  intro i
  rw [← independent_family_span_eq (U i) (columns i) (hind i) (hmem i) (hcard i)]
  exact Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hdecode i j)

/-- Actual transmitted coordinates: one common block, three pair blocks,
two aligned blocks, and all individual completion blocks. -/
abbrev ScalarTransmissionIndex (r x y z l : ℕ) (h : Fin 3 → ℕ) :=
  Fin r ⊕ ((Fin x ⊕ (Fin y ⊕ Fin z)) ⊕
    ((Fin l ⊕ Fin l) ⊕ ((i : Fin 3) × Fin (h i))))

/-- The explicit coefficient list of the scalar construction. -/
def scalarTransmitted {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (c : Fin r → F) (p12 : Fin x → F) (p02 : Fin y → F) (p01 : Fin z → F)
    (al₀ al₁ : Fin l → F) (indiv : ∀ i, Fin (h i) → F) :
    ScalarTransmissionIndex r x y z l h → F :=
  Sum.elim c (Sum.elim (Sum.elim p12 (Sum.elim p02 p01))
    (Sum.elim (Sum.elim al₀ al₁) (fun j => indiv j.1 j.2)))

/-- The scalar length is the paper's allocation cost. -/
theorem scalarTransmission_card (r x y z l : ℕ) (h : Fin 3 → ℕ) :
    Fintype.card (ScalarTransmissionIndex r x y z l h) =
      r+x+y+z+2*l+h 0+h 1+h 2 := by
  simp [ScalarTransmissionIndex, Fintype.card_sigma, Fin.sum_univ_succ]
  omega

/-- Each allocated broadcast block lies in the span of the explicit list. -/
theorem scalarTransmitted_mem {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (c : Fin r → F) (p12 : Fin x → F) (p02 : Fin y → F) (p01 : Fin z → F)
    (al₀ al₁ : Fin l → F) (indiv : ∀ i, Fin (h i) → F) :
    let S := Submodule.span K (Set.range (scalarTransmitted c p12 p02 p01 al₀ al₁ indiv))
    (∀ j, c j ∈ S) ∧ (∀ j, p12 j ∈ S) ∧ (∀ j, p02 j ∈ S) ∧
    (∀ j, p01 j ∈ S) ∧ (∀ j, al₀ j ∈ S) ∧ (∀ j, al₁ j ∈ S) ∧
    (∀ i j, indiv i j ∈ S) := by
  dsimp only
  have hm (j : ScalarTransmissionIndex r x y z l h) :
      scalarTransmitted c p12 p02 p01 al₀ al₁ indiv j ∈
        Submodule.span K (Set.range (scalarTransmitted c p12 p02 p01 al₀ al₁ indiv)) :=
    Submodule.subset_span ⟨j,rfl⟩
  exact ⟨fun j => hm (.inl j), fun j => hm (.inr (.inl (.inl j))),
    fun j => hm (.inr (.inl (.inr (.inl j)))),
    fun j => hm (.inr (.inl (.inr (.inr j)))),
    fun j => hm (.inr (.inr (.inl (.inl j)))),
    fun j => hm (.inr (.inr (.inl (.inr j)))),
    fun i j => hm (.inr (.inr (.inr ⟨i,j⟩)))⟩

/-- User-selected column order, matching the independently selected witnesses. -/
noncomputable def scalarLocalColumns [FiniteDimensional K F] (A : Submodule K F)
    {r a b l h : ℕ} (indiv : Fin h → F) (c : Fin r → F)
    (p : Fin a → F) (q : Fin b → F) (al : Fin l → F) :
    (Fin (Module.finrank K A) ⊕ Fin h) ⊕
      (Fin r ⊕ ((Fin a ⊕ Fin b) ⊕ Fin l)) → F :=
  Sum.elim (Sum.elim (fun j => (Module.finBasis K A j : F)) indiv)
    (Sum.elim c (Sum.elim (Sum.elim p q) al))

/-- Every user-selected column is recoverable from side information and the
transmitted blocks; for User 3, apply this with the sum of aligned blocks. -/
theorem scalarLocalColumns_mem [FiniteDimensional K F] (A S : Submodule K F)
    {r a b l h : ℕ} (indiv : Fin h → F) (c : Fin r → F)
    (p : Fin a → F) (q : Fin b → F) (al : Fin l → F)
    (hi : ∀ j, indiv j ∈ S) (hc : ∀ j, c j ∈ S)
    (hp : ∀ j, p j ∈ S) (hq : ∀ j, q j ∈ S) (ha : ∀ j, al j ∈ S) :
    ∀ j, scalarLocalColumns A indiv c p q al j ∈ A ⊔ S := by
  rintro ((j|j)|(j|((j|j)|j)))
  · exact (show A ≤ A ⊔ S from le_sup_left) (Module.finBasis K A j).property
  · exact (show S ≤ A ⊔ S from le_sup_right) (hi j)
  · exact (show S ≤ A ⊔ S from le_sup_right) (hc j)
  · exact (show S ≤ A ⊔ S from le_sup_right) (hp j)
  · exact (show S ≤ A ⊔ S from le_sup_right) (hq j)
  · exact (show S ≤ A ⊔ S from le_sup_right) (ha j)

end UploadBroadcast
