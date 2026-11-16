import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Simultaneous indecomposable decomposition of subspace configurations

A decomposition is a finite binary tree of internal direct sums. Every split
simultaneously splits every designated subspace; its nonzero leaves admit no
further such split. The existence theorem uses ambient dimension induction,
not a decomposition-existence hypothesis. This applies to any finite family,
and indeed any family, of subspaces. It does not assert Krull–Schmidt uniqueness
or a root classification.
-/
namespace UploadBroadcast.TaskDecomposition

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The paper's three nested pairs of subspaces. -/
structure Task (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  A : Fin 3 → Submodule K V
  U : Fin 3 → Submodule K V
  nested : ∀ i, A i ≤ U i

/-- All six designated spaces, retaining their arm labels. -/
def Task.spaces (T : Task K V) : Fin 3 × Bool → Submodule K V :=
  fun (i, b) => if b then T.U i else T.A i

/-- A simultaneous internal direct-sum split of a component `W`. -/
structure Split (S : ι → Submodule K V) (W P Q : Submodule K V) : Prop where
  disjoint : Disjoint P Q
  sup_eq : P ⊔ Q = W
  compatible : ∀ i, S i ⊓ W = (S i ⊓ P) ⊔ (S i ⊓ Q)

/-- A nonzero component with no nontrivial simultaneous splitting. -/
def Indecomposable (S : ι → Submodule K V) (W : Submodule K V) : Prop :=
  W ≠ ⊥ ∧ ∀ P Q, Split S W P Q → P = ⊥ ∨ Q = ⊥

/-- Finite certificate of a simultaneous decomposition into nonzero
indecomposable components. The empty decomposition represents the zero space. -/
inductive Decomposition (S : ι → Submodule K V) : Submodule K V → Prop
  | zero : Decomposition S ⊥
  | atom {W} : Indecomposable S W → Decomposition S W
  | split {W P Q} : Split S W P Q → Decomposition S P →
      Decomposition S Q → Decomposition S W

lemma Split.left_lt {S : ι → Submodule K V} {W P Q : Submodule K V}
    (h : Split S W P Q) (hQ : Q ≠ ⊥) : P < W := by
  have hP : P ≤ W := h.sup_eq ▸ le_sup_left
  have hQW : Q ≤ W := h.sup_eq ▸ le_sup_right
  refine lt_of_le_of_ne hP ?_
  intro he
  have : Q ≤ P := he ▸ hQW
  exact hQ (eq_bot_iff.mpr (fun x hx => h.disjoint.le_bot ⟨this hx, hx⟩))

lemma Split.right_lt {S : ι → Submodule K V} {W P Q : Submodule K V}
    (h : Split S W P Q) (hP : P ≠ ⊥) : Q < W := by
  apply Split.left_lt (S := S) (P := Q) (Q := P) _ hP
  exact ⟨h.disjoint.symm, sup_comm Q P ▸ h.sup_eq,
    fun i => (h.compatible i).trans (sup_comm _ _)⟩

/-- Every finite-dimensional subspace configuration has a finite simultaneous
internal direct-sum decomposition into indecomposable nonzero components. -/
theorem exists_decomposition [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) : Decomposition S W := by
  classical
  generalize hn : Module.finrank K W = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    by_cases hW : W = ⊥
    · exact hW ▸ Decomposition.zero
    by_cases hi : Indecomposable S W
    · exact Decomposition.atom hi
    have hs : ∃ P Q, Split S W P Q ∧ P ≠ ⊥ ∧ Q ≠ ⊥ := by
      simpa only [Indecomposable, hW, ne_eq, not_false_eq_true, true_and,
        not_forall, not_or, exists_prop] using hi
    obtain ⟨P, Q, hs, hP, hQ⟩ := hs
    apply Decomposition.split hs
    · exact ih (Module.finrank K P)
        (hn ▸ Submodule.finrank_lt_finrank_of_lt (hs.left_lt hQ)) P rfl
    · exact ih (Module.finrank K Q)
        (hn ▸ Submodule.finrank_lt_finrank_of_lt (hs.right_lt hP)) Q rfl

/-- Specialization to the six-subspace task used in the manuscript. -/
theorem Task.exists_decomposition [FiniteDimensional K V] (T : Task K V) :
    Decomposition T.spaces ⊤ := TaskDecomposition.exists_decomposition T.spaces ⊤

/-- Supremum of a finite list of components. -/
def componentSup (L : List (Submodule K V)) : Submodule K V := L.foldr (· ⊔ ·) ⊥

lemma componentSup_append (L M : List (Submodule K V)) :
    componentSup (L ++ M) = componentSup L ⊔ componentSup M := by
  induction L with
  | nil => simp [componentSup]
  | cons P L ih => simpa [componentSup, sup_assoc] using congrArg (P ⊔ ·) ih

/-- A flat finite family extracted from the decomposition certificate. It spans
`W`, splits every designated space, and has exactly the dimension of `W`, so no
redundant ambient dimensions are present. -/
theorem Decomposition.finite_components [FiniteDimensional K V]
    {S : ι → Submodule K V} {W : Submodule K V} (h : Decomposition S W) :
    ∃ L : List (Submodule K V),
      (∀ P ∈ L, Indecomposable S P) ∧ componentSup L = W ∧
      (∀ i, componentSup (L.map (fun P => S i ⊓ P)) = S i ⊓ W) ∧
      (L.map (fun (P : Submodule K V) => Module.finrank K P)).sum = Module.finrank K W := by
  induction h with
  | zero => exact ⟨[], by simp [componentSup]⟩
  | @atom W h => exact ⟨[W], by simp [componentSup, h]⟩
  | @split W P Q hs hp hq ihp ihq =>
    obtain ⟨L, hL, hLW, hLS, hLd⟩ := ihp
    obtain ⟨M, hM, hMW, hMS, hMd⟩ := ihq
    refine ⟨L ++ M, ?_, ?_, ?_, ?_⟩
    · intro R hR
      rcases List.mem_append.mp hR with hR | hR
      · exact hL R hR
      · exact hM R hR
    · rw [componentSup_append, hLW, hMW, hs.sup_eq]
    · intro i
      rw [List.map_append, componentSup_append, hLS, hMS, ← hs.compatible]
    · rw [List.map_append, List.sum_append, hLd, hMd, ← hs.sup_eq]
      have hd := Submodule.finrank_sup_add_finrank_inf_eq P Q
      rw [hs.disjoint.eq_bot, finrank_bot, add_zero] at hd
      exact hd.symm

/-- Unconditional finite-list formulation for every finite-dimensional task. -/
theorem Task.exists_finite_components [FiniteDimensional K V] (T : Task K V) :
    ∃ L : List (Submodule K V),
      (∀ P ∈ L, Indecomposable T.spaces P) ∧ componentSup L = ⊤ ∧
      (∀ i, componentSup (L.map (fun P => T.spaces i ⊓ P)) = T.spaces i) ∧
      (L.map (fun (P : Submodule K V) => Module.finrank K P)).sum = Module.finrank K V := by
  obtain ⟨L, hL, hW, hS, hd⟩ := T.exists_decomposition.finite_components
  exact ⟨L, hL, hW, by simpa using hS, by simpa using hd⟩

/-- An endomorphism preserving every designated subspace. -/
def Stable (S : ι → Submodule K V) (f : V →ₗ[K] V) : Prop :=
  ∀ i x, x ∈ S i → f x ∈ S i

/-- Every stable projection splits the whole configuration, not merely its
ambient vector space. This is the bridge needed by a Fitting/local-ring proof. -/
theorem stable_projection_split (S : ι → Submodule K V) (f : V →ₗ[K] V)
    (hf : Stable S f) (hid : ∀ x, f (f x) = f x) :
    Split S ⊤ (LinearMap.ker f) (LinearMap.range f) := by
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, rfl⟩ := hx.2
    have hy : f (f y) = 0 := hx.1
    simpa [hid y] using hy
  · apply eq_top_iff.mpr
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨x - f x, ?_, f x, ?_, sub_add_cancel x (f x)⟩
    · change f (x - f x) = 0
      simp [hid]
    · exact ⟨x, rfl⟩
  · intro i
    apply le_antisymm
    · intro x hx
      apply Submodule.mem_sup.mpr
      refine ⟨x - f x, ⟨(S i).sub_mem hx.1 (hf i x hx.1), ?_⟩,
        f x, ⟨hf i x hx.1, ⟨x, rfl⟩⟩, sub_add_cancel x (f x)⟩
      change f (x - f x) = 0
      simp [hid]
    · exact sup_le (inf_le_left.trans (le_inf le_rfl le_top))
        (inf_le_left.trans (le_inf le_rfl le_top))

/-- Indecomposable configurations have no nontrivial stable projections. -/
theorem Indecomposable.projection_eq_zero_or_id
    {S : ι → Submodule K V} (h : Indecomposable S ⊤)
    (f : V →ₗ[K] V) (hf : Stable S f) (hid : ∀ x, f (f x) = f x) :
    f = 0 ∨ f = LinearMap.id := by
  obtain hk | hr := h.2 _ _ (stable_projection_split S f hf hid)
  · right
    have hinj := LinearMap.ker_eq_bot.mp hk
    ext x
    exact hinj (hid x)
  · left
    ext x
    have hx : f x ∈ LinearMap.range f := ⟨x, rfl⟩
    rw [hr] at hx
    exact hx

/-- Ambient dimension is additive at every internal split. -/
theorem Split.finrank_eq [FiniteDimensional K V]
    {S : ι → Submodule K V} {W P Q : Submodule K V} (h : Split S W P Q) :
    Module.finrank K W = Module.finrank K P + Module.finrank K Q := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [h.disjoint.eq_bot, finrank_bot, add_zero, h.sup_eq] at hd
  exact hd

/-- Every designated subspace dimension is additive at every internal split. -/
theorem Split.finrank_inter_eq [FiniteDimensional K V]
    {S : ι → Submodule K V} {W P Q : Submodule K V} (h : Split S W P Q) (i : ι) :
    Module.finrank K (↥(S i ⊓ W)) =
      Module.finrank K (↥(S i ⊓ P)) + Module.finrank K (↥(S i ⊓ Q)) := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (S i ⊓ P) (S i ⊓ Q)
  have hj : Disjoint (S i ⊓ P) (S i ⊓ Q) := h.disjoint.mono inf_le_right inf_le_right
  rw [hj.eq_bot, finrank_bot, add_zero, ← h.compatible i] at hd
  exact hd

/-- The manuscript's excess, evaluated on a component of a task. -/
noncomputable def Task.componentExcess [FiniteDimensional K V] (T : Task K V)
    (W : Submodule K V) : ℤ :=
  (∑ i : Fin 3, (Module.finrank K (↥(T.A i ⊓ W)) : ℤ)) - Module.finrank K W

/-- Excess is genuinely additive for simultaneous task splittings. -/
theorem Task.componentExcess_split [FiniteDimensional K V] (T : Task K V)
    {W P Q : Submodule K V} (h : Split T.spaces W P Q) :
    T.componentExcess W = T.componentExcess P + T.componentExcess Q := by
  have ha (i : Fin 3) : Module.finrank K (↥(T.A i ⊓ W)) =
      Module.finrank K (↥(T.A i ⊓ P)) + Module.finrank K (↥(T.A i ⊓ Q)) := by
    simpa [Task.spaces] using h.finrank_inter_eq (i, false)
  simp only [Task.componentExcess, ha, h.finrank_eq, Nat.cast_add, Finset.sum_add_distrib]
  omega

/-- A positive-excess task contains a positive-excess indecomposable summand
in its finite simultaneous decomposition. -/
theorem Task.exists_positive_excess_component [FiniteDimensional K V]
    (T : Task K V) {W : Submodule K V} (hpos : 0 < T.componentExcess W) :
    ∃ P : Submodule K V, P ≤ W ∧ Indecomposable T.spaces P ∧
      0 < T.componentExcess P := by
  have hd := TaskDecomposition.exists_decomposition T.spaces W
  induction hd with
  | zero =>
    have hz : (∑ i : Fin 3, (Module.finrank K (↥(T.A i ⊓ (⊥ : Submodule K V)))) : ℤ) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : Module.finrank K (↥(T.A i ⊓ (⊥ : Submodule K V))) = 0 := by
        have hh := Submodule.finrank_mono (show T.A i ⊓ (⊥ : Submodule K V) ≤ ⊥ from inf_le_right)
        rw [finrank_bot] at hh
        omega
      exact_mod_cast hi
    unfold Task.componentExcess at hpos
    rw [hz, finrank_bot] at hpos
    norm_num at hpos
  | @atom W h => exact ⟨W, le_rfl, h, hpos⟩
  | @split W P Q hs hp hq ihp ihq =>
    have hadd := T.componentExcess_split hs
    have hpq : 0 < T.componentExcess P ∨ 0 < T.componentExcess Q := by omega
    rcases hpq with hP | hQ
    · obtain ⟨R, hRP, hR, hpos⟩ := ihp hP
      exact ⟨R, hRP.trans (hs.sup_eq ▸ le_sup_left), hR, hpos⟩
    · obtain ⟨R, hRQ, hR, hpos⟩ := ihq hQ
      exact ⟨R, hRQ.trans (hs.sup_eq ▸ le_sup_right), hR, hpos⟩

end UploadBroadcast.TaskDecomposition
