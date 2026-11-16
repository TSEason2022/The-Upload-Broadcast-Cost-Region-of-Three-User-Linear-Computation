import UploadBroadcast.ScalarAssembly
import UploadBroadcast.BinaryCoordination
import UploadBroadcast.BinaryRelationBridge
import UploadBroadcast.BinaryIncidence

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- The determinant cofactor functional of one decoder column. -/
noncomputable def columnCofactor {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F) (j : N) : F →ₗ[K] K :=
  (LinearMap.proj j).comp ((Matrix.cramer (fun r c => p (w c) r)).comp p)

theorem columnCofactor_apply {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F) (j : N) (v : F) :
    columnCofactor p w j v =
      (Matrix.updateCol (fun r c => p (w c) r) j (p v)).det := rfl

/-- A cofactor vanishes on every other column of the decoder. -/
theorem columnCofactor_other {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F) (j k : N) (hkj : k ≠ j) :
    columnCofactor p w j (w k) = 0 := by
  rw [columnCofactor_apply]
  exact Matrix.det_updateCol_eq_zero hkj

/-- If the fixed side basis occurs away from the updated column, the
cofactor functional vanishes on the entire side-information subspace. -/
theorem columnCofactor_vanishes_side [FiniteDimensional K F]
    {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F) (j : N) (A : Submodule K F)
    (e : Fin (Module.finrank K A) → N)
    (he : ∀ k, e k ≠ j) (hw : ∀ k, w (e k) = (Module.finBasis K A k : F)) :
    ∀ v ∈ A, columnCofactor p w j v = 0 := by
  have hz : (columnCofactor p w j).comp A.subtype = 0 := by
    apply (Module.finBasis K A).ext
    intro k
    change columnCofactor p w j (Module.finBasis K A k) = 0
    rw [← hw k]
    exact columnCofactor_other p w j (e k) (he k)
  intro v hv
  exact LinearMap.congr_fun hz ⟨v,hv⟩

/-- Updating the specified coefficient column evaluates its cofactor. -/
theorem determinant_column_update {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F) (j : N) (v : F) :
    Matrix.det (fun r c => p (Function.update w j v c) r) = columnCofactor p w j v := by
  rw [columnCofactor_apply]
  congr 1
  ext r c
  by_cases hc : c = j
  · subst c; simp [Matrix.updateCol]
  · simp [Function.update_of_ne hc, Matrix.updateCol, hc]

/-- A parameter affecting at most two decoder columns can be reconciled over
any finite field of cardinality at least two, including the binary field. -/
theorem pair_column_update [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [FiniteDimensional K V]
    (N : Fin 3 → Type*) [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (p : ∀ i, F →ₗ[K] (N i → K)) (w : ∀ i, N i → F)
    (next : ∀ i, V → N i → F) (base : Fin 3 → V)
    (hbase : ∀ i, next i (base i) = w i)
    (hdet : ∀ i, Matrix.det (fun r c => p i (w i c) r) ≠ 0)
    (active : Finset (Fin 3)) (hcard : active.card ≤ Fintype.card K)
    (hinactive : ∀ i ∉ active, ∀ x, next i x = w i)
    (hactive : ∀ i ∈ active, ∃ (j : N i) (l : V →ₗ[K] F),
      ∀ x, next i x = Function.update (w i) j (l x)) :
    ∃ x, ∀ i, Matrix.det (fun r c => p i (next i x c) r) ≠ 0 := by
  classical
  choose j l hl using fun i : {i // i ∈ active} => hactive i i.property
  let f : {i // i ∈ active} → V →ₗ[K] K := fun i =>
    (columnCofactor (p i) (w i) (j i)).comp (l i)
  have hfnz (i : {i // i ∈ active}) : f i ≠ 0 := by
    intro hz
    have he : Matrix.det (fun r c => p i (next i (base i) c) r) = f i (base i) := by
      rw [hl i]
      exact determinant_column_update _ _ _ _
    rw [hbase i] at he
    exact hdet i (he.trans (by rw [hz]; rfl))
  obtain ⟨x,hx⟩ := exists_forall_linearForm_ne_zero f hfnz (by simpa using hcard)
  refine ⟨x,fun i => ?_⟩
  by_cases hi : i ∈ active
  · let k : {i // i ∈ active} := ⟨i,hi⟩
    have he := hl k x
    rw [he,determinant_column_update]
    exact hx k
  · rw [hinactive i hi x]
    exact hdet i

/-- Coordinate independent column families using any verified group updater.
The nonzero constraint is an exact decidable indicator of independence. -/
theorem independent_coordination_of_update_rule
    {G I : Type*} [DecidableEq G] [Fintype G]
    (V : G → Type*) [∀ g, Zero (V g)]
    (N : I → Type*) (w : ∀ i, ((g : G) → V g) → N i → F)
    (hw : ∀ i, ∃ a, LinearIndependent K (w i a))
    (hstep : ∀ g (a : I → ((g : G) → V g)),
      (∀ i, LinearIndependent K (w i (a i))) →
      ∃ x : V g, ∀ i, LinearIndependent K (w i (Function.update (a i) g x))) :
    ∃ a, ∀ i, LinearIndependent K (w i a) := by
  classical
  let c : I → ((g : G) → V g) → ℕ := fun i a => if LinearIndependent K (w i a) then 1 else 0
  have hc (i : I) (a) : c i a ≠ 0 ↔ LinearIndependent K (w i a) := by simp [c]
  have hw' : ∀ i, ∃ a, c i a ≠ 0 := by
    intro i
    obtain ⟨a,ha⟩ := hw i
    exact ⟨a,(hc i a).mpr ha⟩
  obtain ⟨a,ha⟩ := simultaneous_nonzero_of_update_rule V c hw' (by
    intro g a ha
    obtain ⟨x,hx⟩ := hstep g a (fun i => (hc i (a i)).mp (ha i))
    exact ⟨x,fun i => (hc i _).mpr (hx i)⟩)
  exact ⟨a,fun i => (hc i a).mp (ha i)⟩

/-- A nonzero projected decoder determinant certifies independence of the
actual coefficient columns. -/
theorem independent_of_projected_det {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F)
    (h : Matrix.det (fun r c => p (w c) r) ≠ 0) : LinearIndependent K w := by
  apply LinearIndependent.of_comp p
  exact Matrix.linearIndependent_cols_of_det_ne_zero h

/-- Coordinate projections of an independent family have determinant one. -/
theorem independent_projection_det {N : Type*} [Fintype N] [DecidableEq N]
    (p : F →ₗ[K] (N → K)) (w : N → F)
    (hp : ∀ j k, p (w j) k = if j = k then 1 else 0) :
    Matrix.det (fun r c => p (w c) r) ≠ 0 := by
  have he : (fun r c => p (w c) r) = (1 : Matrix N N K) := by
    ext r c
    simp only [hp,Matrix.one_apply]
    split_ifs <;> simp_all
  rw [he,Matrix.det_one]
  exact one_ne_zero

omit [AddCommGroup F] in
/-- Updating an incident group replaces precisely its one shared column. -/
theorem incident_block_update {G H J : Type*} [DecidableEq G] [DecidableEq H] [DecidableEq J]
    (V : G → Type*) (e : J → G) (he : Function.Injective e)
    (fixed : H → F) (proj : ∀ g, V g → F) (a : ∀ g, V g)
    (g : G) (j : J) (hj : e j = g) (x : V g) :
    Sum.elim fixed (fun k => proj (e k) (Function.update a g x (e k))) =
      Function.update (Sum.elim fixed (fun k => proj (e k) (a (e k))))
        (Sum.inr j) (proj g x) := by
  funext k
  cases k with
  | inl k => simp
  | inr k =>
    by_cases hk : k = j
    · subst k; subst g; simp
    · have hne : e k ≠ g := by intro hh; exact hk (he (hh.trans hj.symm))
      simp [Function.update_of_ne hne, hk]

omit [AddCommGroup F] in
/-- Updating an absent group leaves a decoder unchanged. -/
theorem absent_block_update {G H J : Type*} [DecidableEq G]
    (V : G → Type*) (e : J → G) (fixed : H → F) (proj : ∀ g, V g → F)
    (a : ∀ g, V g) (g : G) (hg : ∀ j, e j ≠ g) (x : V g) :
    Sum.elim fixed (fun k => proj (e k) (Function.update a g x (e k))) =
      Sum.elim fixed (fun k => proj (e k) (a (e k))) := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => simp [Function.update_of_ne (hg k)]

/-- Concrete pair-block reconciliation for the three-user incidence pattern. -/
theorem pair_incidence_update [Fintype K] [FiniteDimensional K F]
    (U : Fin 3 → Submodule K F) {x y z l : ℕ}
    (H : Fin 3 → Type*) [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (fixed : ∀ i, H i → F)
    (a : Fin 3 → ((g : BinaryIncidence.Remaining x y z l) → BinaryIncidence.Space U g))
    (hi : ∀ i, LinearIndependent K (Sum.elim (fixed i) (fun j =>
      BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
        (a i (BinaryIncidence.inclusion x y z l i j)))))
    (g : Fin x ⊕ (Fin y ⊕ Fin z)) :
    ∃ t : BinaryIncidence.Space U (Sum.inl g), ∀ i,
      LinearIndependent K (Sum.elim (fixed i) (fun j =>
        BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
          (Function.update (a i) (Sum.inl g) t (BinaryIncidence.inclusion x y z l i j)))) := by
  classical
  let N i := H i ⊕ BinaryIncidence.Local x y z l i
  let w : ∀ i, N i → F := fun i => Sum.elim (fixed i) (fun j =>
    BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
      (a i (BinaryIncidence.inclusion x y z l i j)))
  let next : ∀ i, BinaryIncidence.Space U (Sum.inl g) → N i → F := fun i t =>
    Sum.elim (fixed i) (fun j =>
      BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
        (Function.update (a i) (Sum.inl g) t (BinaryIncidence.inclusion x y z l i j)))
  choose p hp using fun i => independent_coordinate_projection (w i) (hi i)
  let active : Finset (Fin 3) := Finset.univ.filter (fun i =>
    ∃ j, BinaryIncidence.inclusion x y z l i j = Sum.inl g)
  have hc : active.card ≤ Fintype.card K := by
    apply le_trans (Finset.card_le_card (show active ⊆ BinaryIncidence.pair_support g from ?_))
      ((BinaryIncidence.pair_support_card_le g).trans Fintype.one_lt_card)
    intro i hi
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
    by_contra hn
    exact BinaryIncidence.pair_not_incident g i hn j hj
  obtain ⟨t,ht⟩ := pair_column_update N p w next (fun i => a i (Sum.inl g))
    (fun i => by simp [next,w])
    (fun i => independent_projection_det (p i) (w i) (hp i)) active hc
    (by
      intro i hi t
      apply absent_block_update (BinaryIncidence.Space U)
        (BinaryIncidence.inclusion x y z l i) (fixed i)
        (fun g => (BinaryIncidence.projection U i g : BinaryIncidence.Space U g → F))
        (a i) (Sum.inl g)
      intro j hj
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨j,hj⟩⟩))
    (by
      intro i hi
      obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
      refine ⟨Sum.inr j,BinaryIncidence.projection U i (Sum.inl g),fun t => ?_⟩
      exact incident_block_update (BinaryIncidence.Space U) _
        (BinaryIncidence.inclusion_injective x y z l i) (fixed i)
        (fun g => (BinaryIncidence.projection U i g : BinaryIncidence.Space U g → F))
        (a i) (Sum.inl g) j hj t)
  exact ⟨t,fun i => independent_of_projected_det (p i) (next i t) (ht i)⟩

/-- The aligned-group determinant forms vanish on the fixed side spaces.
The spanning side spaces exclude the odd binary obstruction. -/
theorem aligned_incidence_update
    [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (A U : Fin 3 → Submodule (ZMod 2) F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) {x y z l : ℕ}
    (H : Fin 3 → Type*) [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (fixed : ∀ i, H i → F)
    (side : ∀ i, Fin (Module.finrank (ZMod 2) (A i)) → H i)
    (hside : ∀ i k, fixed i (side i k) = (Module.finBasis (ZMod 2) (A i) k : F))
    (a : Fin 3 → ((g : BinaryIncidence.Remaining x y z l) → BinaryIncidence.Space U g))
    (hi : ∀ i, LinearIndependent (ZMod 2) (Sum.elim (fixed i) (fun j =>
      BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
        (a i (BinaryIncidence.inclusion x y z l i j)))))
    (j : Fin l) :
    ∃ t : BinaryIncidence.Space U (Sum.inr j), ∀ i,
      LinearIndependent (ZMod 2) (Sum.elim (fixed i) (fun k =>
        BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i k)
          (Function.update (a i) (Sum.inr j) t (BinaryIncidence.inclusion x y z l i k)))) := by
  classical
  let N i := H i ⊕ BinaryIncidence.Local x y z l i
  let w : ∀ i, N i → F := fun i => Sum.elim (fixed i) (fun k =>
    BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i k)
      (a i (BinaryIncidence.inclusion x y z l i k)))
  let next : ∀ i, BinaryIncidence.Space U (Sum.inr j) → N i → F := fun i t =>
    Sum.elim (fixed i) (fun k =>
      BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i k)
        (Function.update (a i) (Sum.inr j) t (BinaryIncidence.inclusion x y z l i k)))
  choose p hp using fun i => independent_coordinate_projection (w i) (hi i)
  let pos : ∀ i, N i := fun i => Sum.inr (BinaryIncidence.alignedIndex i j)
  let f : Fin 3 → F →ₗ[ZMod 2] ZMod 2 := fun i => columnCofactor (p i) (w i) (pos i)
  have hupdate (i : Fin 3) (t : BinaryIncidence.Space U (Sum.inr j)) :
      next i t = Function.update (w i) (pos i) (ScalarIncidence.relationProjection U i t) := by
    exact incident_block_update (BinaryIncidence.Space U) _
      (BinaryIncidence.inclusion_injective x y z l i) (fixed i)
      (fun g => (BinaryIncidence.projection U i g : BinaryIncidence.Space U g → F))
      (a i) (Sum.inr j) (BinaryIncidence.alignedIndex i j)
      (BinaryIncidence.inclusion_aligned i j) t
  have hlocal (i : Fin 3) (v : F) (hv : v ∈ A i) : f i v = 0 := by
    apply columnCofactor_vanishes_side (p i) (w i) (pos i) (A i)
      (fun k => Sum.inl (side i k)) (fun _ => Sum.inl_ne_inr) ?_ v hv
    exact hside i
  have hnz (i : Fin 3) : (f i).comp (ScalarIncidence.relationProjection U i) ≠ 0 := by
    intro hz
    have he := congrArg (fun v : N i → F => Matrix.det (fun r c => p i (v c) r))
      (hupdate i (a i (Sum.inr j)))
    have hn := independent_projection_det (p i) (w i) (hp i)
    have hnext : next i (a i (Sum.inr j)) = w i := by simp [next,w]
    rw [hnext] at he
    dsimp only at he
    rw [determinant_column_update] at he
    have hf : f i (ScalarIncidence.relationProjection U i (a i (Sum.inr j))) = 0 :=
      LinearMap.congr_fun hz (a i (Sum.inr j))
    exact hn (he.trans hf)
  obtain ⟨t,ht⟩ := binary_aligned_projection_group A U hAU hspan f hlocal hnz
  refine ⟨t,fun i => independent_of_projected_det (p i) (next i t) ?_⟩
  rw [hupdate,determinant_column_update]
  exact ht i

/-- Binary shared-block coordination with the common block fixed. Pair
groups affect at most two users; aligned groups use the side-space spanning
hypothesis to exclude the sole odd binary obstruction. -/
theorem binary_incidence_coordination
    [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (A U : Fin 3 → Submodule (ZMod 2) F) (hAU : ∀ i, A i ≤ U i)
    (hspan : (⨆ i, A i) = ⊤) {r x y z l : ℕ} {h : Fin 3 → ℕ}
    (c : Fin r → F) (indiv : ∀ i, Fin (h i) → F)
    (selected : ∀ i, BinaryIncidence.Local x y z l i → F)
    (hs : ∀ i j, selected i j ∈ BinaryIncidence.allowed U i
      (BinaryIncidence.inclusion x y z l i j))
    (hind : ∀ i, LinearIndependent (ZMod 2) (Sum.elim
      (Sum.elim (Sum.elim (fun j => (Module.finBasis (ZMod 2) (A i) j : F)) c) (indiv i))
      (selected i))) :
    ∃ a : (g : BinaryIncidence.Remaining x y z l) → BinaryIncidence.Space U g,
      ∀ i, LinearIndependent (ZMod 2) (Sum.elim
        (Sum.elim (Sum.elim (fun j => (Module.finBasis (ZMod 2) (A i) j : F)) c) (indiv i))
        (fun j => BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
          (a (BinaryIncidence.inclusion x y z l i j)))) := by
  classical
  let H i := (Fin (Module.finrank (ZMod 2) (A i)) ⊕ Fin r) ⊕ Fin (h i)
  let fixed : ∀ i, H i → F := fun i =>
    Sum.elim (Sum.elim (fun j => (Module.finBasis (ZMod 2) (A i) j : F)) c) (indiv i)
  let N i := H i ⊕ BinaryIncidence.Local x y z l i
  let w : ∀ i, ((g : BinaryIncidence.Remaining x y z l) → BinaryIncidence.Space U g) →
      N i → F := fun i a => Sum.elim (fixed i) (fun j =>
    BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
      (a (BinaryIncidence.inclusion x y z l i j)))
  apply independent_coordination_of_update_rule (BinaryIncidence.Space U) N w
  · intro i
    choose v hv using fun j => BinaryIncidence.projection_lift U i _ _ (hs i j)
    obtain ⟨a,ha⟩ := exists_parameter_extension (BinaryIncidence.Space U)
      (BinaryIncidence.inclusion x y z l i) (BinaryIncidence.inclusion_injective x y z l i) v
    refine ⟨a,?_⟩
    have he : (fun j => BinaryIncidence.projection U i (BinaryIncidence.inclusion x y z l i j)
        (a (BinaryIncidence.inclusion x y z l i j))) = selected i := by
      funext j
      rw [ha j,hv j]
    change LinearIndependent (ZMod 2) (Sum.elim (fixed i) _)
    rw [he]
    exact hind i
  · intro g a hi
    cases g with
    | inl g => exact pair_incidence_update U H fixed a hi g
    | inr j =>
      exact aligned_incidence_update A U hAU hspan H fixed
        (fun _ k => Sum.inl (Sum.inl k)) (fun _ _ => rfl) a hi j

end UploadBroadcast
