import UploadBroadcast.TaskDecomposition
import UploadBroadcast.Profile
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Maximal simultaneous extraction of directed demand edges

The actual six-subspace task is split by stable projections. The multiplicity
is the quotient dimension in Appendix `app:edge-extraction`; no decomposition
or extraction theorem is assumed.
-/
namespace UploadBroadcast.EdgeExtraction
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The six nested spaces of an operational task, forgetting feasibility. -/
def configuration (T : UploadBroadcast.Task K V) : TaskDecomposition.Task K V :=
  ⟨T.A, T.U, T.side_le_signal⟩

/-- A complement of `N ∩ C` inside `N`, with an ambient complement containing `C`. -/
theorem exists_relative_complement (N C : Submodule K V) :
    ∃ W Q : Submodule K V, W ≤ N ∧ Disjoint W C ∧ IsCompl W Q ∧
      C ≤ Q ∧ (N ⊓ C) ⊔ W = N := by
  classical
  obtain ⟨⟨W, hWN⟩, hW⟩ := exists_isCompl (⟨N ⊓ C, (show N ⊓ C ≤ N from inf_le_left)⟩ : Set.Iic N)
  obtain ⟨hd, hs⟩ := Set.Iic.isCompl_iff.mp hW
  have hdC : Disjoint W C := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    exact hd.le_bot ⟨⟨hWN hx.1, hx.2⟩, hx.1⟩
  obtain ⟨R, hR⟩ := (W ⊔ C).exists_isCompl
  exact ⟨W, C ⊔ R, hWN, hdC,
    hdC.isCompl_sup_right_of_isCompl_sup_left hR, le_sup_left, hs⟩

/-- Quotient dimension is attained by a genuine ambient direct summand. -/
theorem relative_complement_finrank [FiniteDimensional K V]
    {N C W : Submodule K V} (hd : Disjoint W C)
    (hs : (N ⊓ C) ⊔ W = N) :
    finrank K W = finrank K N - finrank K ↥(N ⊓ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (N ⊓ C) W
  have hj : Disjoint (N ⊓ C) W := hd.symm.mono inf_le_right le_rfl
  rw [hs, hj.eq_bot, finrank_bot, add_zero] at h
  omega

/-- Dimension upper bound for every demand-only subspace, hence also every
extractable demand-only direct summand. -/
theorem disjoint_finrank_le_quotient [FiniteDimensional K V]
    {N C W : Submodule K V} (hW : W ≤ N) (hd : Disjoint W C) :
    finrank K W ≤ finrank K N - finrank K ↥(N ⊓ C) := by
  have hj : Disjoint (N ⊓ C) W := hd.symm.mono inf_le_right le_rfl
  have h := Submodule.finrank_sup_add_finrank_inf_eq (N ⊓ C) W
  rw [hj.eq_bot, finrank_bot, add_zero] at h
  have hm := Submodule.finrank_mono (show (N ⊓ C) ⊔ W ≤ N from sup_le inf_le_left hW)
  omega

/-- Denominator used in the manuscript's edge quotient. -/
def blocked (T : UploadBroadcast.Task K V) (i j : Three) : Submodule K V :=
  T.A j ⊔ (T.U i ⊓ T.U j)

/-- Exact dimension available for a `k → j` edge, with third user `i`. -/
noncomputable def multiplicity [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (i j k : Three) : ℕ :=
  finrank K ↥(T.A k ⊓ T.U j) -
    finrank K ↥((T.A k ⊓ T.U j) ⊓ blocked T i j)

/-- The modular-law step in the extraction proof. -/
theorem signal_inf_killed (T : UploadBroadcast.Task K V) (i j : Three) :
    T.U j ⊓ (T.U i ⊔ T.A j) = blocked T i j := by
  rw [sup_comm, inf_comm, sup_inf_assoc_of_le _ (T.side_le_signal j)]
  rfl

theorem numerator_inf_killed (T : UploadBroadcast.Task K V) (i j k : Three) :
    (T.A k ⊓ T.U j) ⊓ (T.U i ⊔ T.A j) =
      (T.A k ⊓ T.U j) ⊓ blocked T i j := by
  rw [inf_assoc, signal_inf_killed]
  have hB : blocked T i j ≤ T.U j := sup_le (T.side_le_signal j) inf_le_right
  rw [inf_assoc, inf_eq_right.mpr hB]

/-- A directed edge block is present exactly on the source side/signal and
on the target signal. The third signal and target side vanish on the block. -/
structure EdgeBlock (T : UploadBroadcast.Task K V) (i j k : Three)
    (W : Submodule K V) : Prop where
  source : W ≤ T.A k
  target : W ≤ T.U j
  third_zero : Disjoint W (T.U i)
  target_side_zero : Disjoint W (T.A j)

/-- The full six-space signature of a physical edge summand. -/
theorem EdgeBlock.signature {T : UploadBroadcast.Task K V} {i j k : Three}
    {W : Submodule K V} (h : EdgeBlock T i j k W) :
    T.A k ⊓ W = W ∧ T.U k ⊓ W = W ∧ T.U j ⊓ W = W ∧
      T.A i ⊓ W = ⊥ ∧ T.U i ⊓ W = ⊥ ∧ T.A j ⊓ W = ⊥ := by
  exact ⟨inf_eq_right.mpr h.source,
    inf_eq_right.mpr (h.source.trans (T.side_le_signal k)),
    inf_eq_right.mpr h.target,
    (h.third_zero.mono_right (T.side_le_signal i)).symm.eq_bot,
    h.third_zero.symm.eq_bot, h.target_side_zero.symm.eq_bot⟩

/-- A maximal edge extraction is witnessed by an actual stable idempotent. -/
structure Extraction [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (i j k : Three) where
  W : Submodule K V
  Q : Submodule K V
  projection : V →ₗ[K] V
  block : EdgeBlock T i j k W
  complementary : IsCompl W Q
  killed : T.U i ⊔ T.A j ≤ Q
  range_eq : LinearMap.range projection = W
  ker_eq : LinearMap.ker projection = Q
  fixes : ∀ x ∈ W, projection x = x
  stable : TaskDecomposition.Stable (configuration T).spaces projection
  idempotent : ∀ x, projection (projection x) = projection x
  dimension : finrank K W = multiplicity T i j k

/-- Every field admits maximal extraction of any selected directed edge. -/
theorem exists_extraction [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Nonempty (Extraction T i j k) := by
  classical
  obtain ⟨W, Q, hWN, hd, hc, hCQ, hs⟩ :=
    exists_relative_complement (T.A k ⊓ T.U j) (T.U i ⊔ T.A j)
  let g : V →ₗ[K] W := W.linearProjOfIsCompl Q hc
  let f : V →ₗ[K] V := W.subtype.comp g
  have hfix (x : V) (hx : x ∈ W) : f x = x :=
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc (⟨x,hx⟩ : W))
  have hzero (x : V) (hx : x ∈ Q) : f x = 0 :=
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right' hc x hx)
  have him (x : V) : f x ∈ W := (g x).property
  have hstable : TaskDecomposition.Stable (configuration T).spaces f := by
    rintro ⟨l, b⟩ x hx
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hl : l = i ∨ l = j ∨ l = k := by
      have : l.val = i.val ∨ l.val = j.val ∨ l.val = k.val := by omega
      exact this.imp Fin.ext (fun h => h.imp Fin.ext Fin.ext)
    rcases hl with hl | hl | hl <;> subst l
    · have hxU : x ∈ T.U i := by
        cases b <;> simp only [configuration, TaskDecomposition.Task.spaces] at hx
        · exact T.side_le_signal i hx
        · exact hx
      rw [hzero x (hCQ ((show T.U i ≤ T.U i ⊔ T.A j from le_sup_left) hxU))]
      exact Submodule.zero_mem _
    · cases b
      · change x ∈ T.A j at hx
        rw [hzero x (hCQ ((show T.A j ≤ T.U i ⊔ T.A j from le_sup_right) hx))]
        exact Submodule.zero_mem _
      · exact (hWN (him x)).2
    · cases b
      · exact (hWN (him x)).1
      · exact T.side_le_signal k (hWN (him x)).1
  refine ⟨⟨W, Q, f,
    ⟨hWN.trans inf_le_left, hWN.trans inf_le_right,
      hd.mono_right le_sup_left, hd.mono_right le_sup_right⟩,
    hc, hCQ, ?_, ?_, hfix, hstable, fun x => hfix _ (him x), ?_⟩⟩
  · apply le_antisymm
    · rintro x ⟨y,rfl⟩; exact him y
    · intro x hx; exact ⟨x, hfix x hx⟩
  · ext x
    change f x = 0 ↔ x ∈ Q
    constructor
    · intro hx
      apply (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).mp
      exact Subtype.ext hx
    · exact hzero x
  · rw [relative_complement_finrank hd hs, numerator_inf_killed]
    rfl

/-- Chosen maximal extraction. -/
noncomputable def extract [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Extraction T i j k :=
  Classical.choice (exists_extraction T i j k hij hik hjk)

/-- The extraction splits all six spaces, as well as the ambient source. -/
theorem Extraction.split [FiniteDimensional K V]
    {T : UploadBroadcast.Task K V} {i j k : Three} (E : Extraction T i j k) :
    TaskDecomposition.Split (configuration T).spaces ⊤ E.Q E.W := by
  have h := TaskDecomposition.stable_projection_split
    (configuration T).spaces E.projection E.stable E.idempotent
  rwa [E.ker_eq, E.range_eq] at h

/-- Maximality among all simultaneous task splittings, rather than only the
particular complements used in the construction. -/
theorem EdgeBlock.finrank_le_of_split [FiniteDimensional K V]
    {T : UploadBroadcast.Task K V} {i j k : Three} {W Q : Submodule K V}
    (h : EdgeBlock T i j k W)
    (hs : TaskDecomposition.Split (configuration T).spaces ⊤ Q W) :
    finrank K W ≤ multiplicity T i j k := by
  have hi := hs.compatible (i, true)
  have hj := hs.compatible (j, false)
  change T.U i ⊓ ⊤ = (T.U i ⊓ Q) ⊔ (T.U i ⊓ W) at hi
  change T.A j ⊓ ⊤ = (T.A j ⊓ Q) ⊔ (T.A j ⊓ W) at hj
  rw [inf_top_eq, h.third_zero.symm.eq_bot, sup_bot_eq] at hi
  rw [inf_top_eq, h.target_side_zero.symm.eq_bot, sup_bot_eq] at hj
  have hCQ : T.U i ⊔ T.A j ≤ Q :=
    sup_le (hi ▸ inf_le_right) (hj ▸ inf_le_right)
  have hd : Disjoint W (T.U i ⊔ T.A j) := hs.disjoint.symm.mono_right hCQ
  have hh := disjoint_finrank_le_quotient (le_inf h.source h.target) hd
  rw [numerator_inf_killed] at hh
  exact hh

/-- The exact quotient formula is the maximum number of independent copies
of the selected physical edge task. -/
theorem maximal_edge_extraction [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (i j k : Three)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ W Q : Submodule K V,
      TaskDecomposition.Split (configuration T).spaces ⊤ Q W ∧
      EdgeBlock T i j k W ∧ finrank K W = multiplicity T i j k ∧
      ∀ W' Q', EdgeBlock T i j k W' →
        TaskDecomposition.Split (configuration T).spaces ⊤ Q' W' →
          finrank K W' ≤ finrank K W := by
  let E := extract T i j k hij hik hjk
  refine ⟨E.W, E.Q, E.split, E.block, E.dimension, ?_⟩
  intro W' Q' hW' hS'
  rw [E.dimension]
  exact hW'.finrank_le_of_split hS'

/-- Directed edges are labeled by the third user, target, and source. -/
abbrev Edge := {t : Three × Three × Three //
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}

/-- Exactly the six directed edges of the three-user graph. -/
theorem edge_card : Fintype.card Edge = 6 := by decide

noncomputable def edgeExtraction [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (e : Edge) : Extraction T e.val.1 e.val.2.1 e.val.2.2 :=
  extract T _ _ _ e.property.1 e.property.2.1 e.property.2.2

/-- For different edges, one edge image lies in a space killed by the other. -/
theorem other_edge_indices (e f : Edge) (hef : e ≠ f) :
    f.val.2.2 = e.val.1 ∨ f.val.2.2 = e.val.2.1 ∨ f.val.2.1 = e.val.1 := by
  rcases e with ⟨⟨i,j,k⟩, hij,hik,hjk⟩
  rcases f with ⟨⟨a,b,c⟩, hab,hac,hbc⟩
  change c = i ∨ c = j ∨ b = i
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  by_contra hn
  push_neg at hn
  have hci : c.val ≠ i.val := fun h => hn.1 (Fin.ext h)
  have hcj : c.val ≠ j.val := fun h => hn.2.1 (Fin.ext h)
  have hbi : b.val ≠ i.val := fun h => hn.2.2 (Fin.ext h)
  have ha : a = i := Fin.ext (by omega)
  have hb : b = j := Fin.ext (by omega)
  have hc : c = k := Fin.ext (by omega)
  subst a; subst b; subst c
  exact hef rfl

/-- Independent choices of maximal edge projections are automatically
orthogonal. This gives simultaneous extraction without a sequential choice. -/
theorem edge_projection_kills_other [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (e f : Edge) (hef : e ≠ f)
    (x : V) (hx : x ∈ (edgeExtraction T f).W) :
    (edgeExtraction T e).projection x = 0 := by
  apply LinearMap.mem_ker.mp
  rw [(edgeExtraction T e).ker_eq]
  apply (edgeExtraction T e).killed
  rcases other_edge_indices e f hef with h | h | h
  · apply (show T.U e.val.1 ≤ T.U e.val.1 ⊔ T.A e.val.2.1 from le_sup_left)
    rw [← h]
    exact T.side_le_signal _ ((edgeExtraction T f).block.source hx)
  · apply (show T.A e.val.2.1 ≤ T.U e.val.1 ⊔ T.A e.val.2.1 from le_sup_right)
    rw [← h]
    exact (edgeExtraction T f).block.source hx
  · apply (show T.U e.val.1 ≤ T.U e.val.1 ⊔ T.A e.val.2.1 from le_sup_left)
    rw [← h]
    exact (edgeExtraction T f).block.target hx

/-- The six maximal blocks are jointly independent, a stronger property
than pairwise disjointness. -/
theorem edge_blocks_independent [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) :
    iSupIndep (fun e : Edge => (edgeExtraction T e).W) := by
  intro e
  apply (edgeExtraction T e).complementary.disjoint.mono_right
  apply iSup_le
  intro f
  apply iSup_le
  intro hfe x hx
  rw [← (edgeExtraction T e).ker_eq]
  exact edge_projection_kills_other T e f (Ne.symm hfe) x hx

/-- Projection onto all six directed-edge blocks together. -/
noncomputable def allProjection [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) : V →ₗ[K] V :=
  ∑ e : Edge, (edgeExtraction T e).projection

theorem allProjection_on_edge [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (e : Edge) (x : V)
    (hx : x ∈ (edgeExtraction T e).W) : allProjection T x = x := by
  classical
  change (∑ f : Edge, (edgeExtraction T f).projection) x = x
  rw [LinearMap.sum_apply, Finset.sum_eq_single e]
  · exact (edgeExtraction T e).fixes x hx
  · intro f _ hfe
    exact edge_projection_kills_other T f e hfe x hx
  · simp

theorem edge_projection_mem [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (e : Edge) (x : V) :
    (edgeExtraction T e).projection x ∈ (edgeExtraction T e).W := by
  rw [← (edgeExtraction T e).range_eq]
  exact ⟨x, rfl⟩

theorem allProjection_stable [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) :
    TaskDecomposition.Stable (configuration T).spaces (allProjection T) := by
  intro l x hx
  change (∑ e : Edge, (edgeExtraction T e).projection) x ∈ _
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun e _ => (edgeExtraction T e).stable l x hx)

theorem allProjection_idempotent [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (x : V) :
    allProjection T (allProjection T x) = allProjection T x := by
  change allProjection T ((∑ e : Edge, (edgeExtraction T e).projection) x) =
    (∑ e : Edge, (edgeExtraction T e).projection) x
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact allProjection_on_edge T e _ (edge_projection_mem T e x)

theorem allProjection_range [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) :
    LinearMap.range (allProjection T) = ⨆ e : Edge, (edgeExtraction T e).W := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    change (∑ e : Edge, (edgeExtraction T e).projection) y ∈ _
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun e _ =>
      (le_iSup (fun e : Edge => (edgeExtraction T e).W) e) (edge_projection_mem T e y))
  · apply iSup_le
    intro e x hx
    exact ⟨x, allProjection_on_edge T e x hx⟩

/-- Simultaneous extraction on disjoint source coordinates: the remaining
source and all six maximal edge blocks split every designated task space. -/
theorem simultaneous_maximal_extraction [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) :
    ∃ (Q : Submodule K V) (W : Edge → Submodule K V),
      iSupIndep W ∧
      TaskDecomposition.Split (configuration T).spaces ⊤ Q (⨆ e, W e) ∧
      (∀ e, EdgeBlock T e.val.1 e.val.2.1 e.val.2.2 (W e) ∧
        finrank K (W e) = multiplicity T e.val.1 e.val.2.1 e.val.2.2) ∧
      ∀ l, (configuration T).spaces l =
        ((configuration T).spaces l ⊓ Q) ⊔
          ⨆ e, (configuration T).spaces l ⊓ W e := by
  refine ⟨LinearMap.ker (allProjection T), fun e => (edgeExtraction T e).W,
    edge_blocks_independent T, ?_, ?_, ?_⟩
  · have h := TaskDecomposition.stable_projection_split (configuration T).spaces
      (allProjection T) (allProjection_stable T) (allProjection_idempotent T)
    rwa [allProjection_range] at h
  · intro e
    exact ⟨(edgeExtraction T e).block, (edgeExtraction T e).dimension⟩
  · intro l
    apply le_antisymm
    · intro x hx
      apply Submodule.mem_sup.mpr
      refine ⟨x - allProjection T x, ⟨?_, ?_⟩, allProjection T x, ?_, sub_add_cancel _ _⟩
      · exact ((configuration T).spaces l).sub_mem hx (allProjection_stable T l x hx)
      · change allProjection T (x - allProjection T x) = 0
        rw [map_sub, allProjection_idempotent, sub_self]
      · change (∑ e : Edge, (edgeExtraction T e).projection) x ∈ _
        rw [LinearMap.sum_apply]
        apply Submodule.sum_mem
        intro e _
        exact (le_iSup (fun e : Edge => (configuration T).spaces l ⊓
          (edgeExtraction T e).W) e)
          ⟨(edgeExtraction T e).stable l x hx, edge_projection_mem T e x⟩
    · exact sup_le inf_le_left (iSup_le fun _ => inf_le_left)

/-- Within a pure edge block, every further subspace is again a genuine
simultaneous task summand. This allows any number of copies up to its maximum. -/
theorem Extraction.subblock_split [FiniteDimensional K V]
    {T : UploadBroadcast.Task K V} {i j k : Three} (E : Extraction T i j k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (P : Submodule K V) (hP : P ≤ E.W) :
    ∃ Q : Submodule K V, TaskDecomposition.Split (configuration T).spaces ⊤ Q P := by
  classical
  obtain ⟨X, hX⟩ := P.exists_isCompl
  let R := X ⊓ E.W
  have hsum : P ⊔ R = E.W := by
    dsimp [R]
    rw [← sup_inf_assoc_of_le X hP, hX.sup_eq_top, top_inf_eq]
  have hd : Disjoint P R := hX.disjoint.mono_right inf_le_left
  have hc : IsCompl P (R ⊔ E.Q) :=
    hd.isCompl_sup_right_of_isCompl_sup_left (hsum ▸ E.complementary)
  let g := P.linearProjOfIsCompl (R ⊔ E.Q) hc
  let f : V →ₗ[K] V := P.subtype.comp g
  have hfix (x : V) (hx : x ∈ P) : f x = x :=
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc (⟨x,hx⟩ : P))
  have hzero (x : V) (hx : x ∈ E.Q) : f x = 0 :=
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right' hc x
      ((show E.Q ≤ R ⊔ E.Q from le_sup_right) hx))
  have him (x : V) : f x ∈ E.W := hP (g x).property
  have hstable : TaskDecomposition.Stable (configuration T).spaces f := by
    rintro ⟨l,b⟩ x hx
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hl : l = i ∨ l = j ∨ l = k := by
      have : l.val = i.val ∨ l.val = j.val ∨ l.val = k.val := by omega
      exact this.imp Fin.ext (fun h => h.imp Fin.ext Fin.ext)
    rcases hl with hl | hl | hl <;> subst l
    · have hxU : x ∈ T.U i := by
        cases b <;> simp only [configuration, TaskDecomposition.Task.spaces] at hx
        · exact T.side_le_signal i hx
        · exact hx
      rw [hzero x (E.killed ((show T.U i ≤ T.U i ⊔ T.A j from le_sup_left) hxU))]
      exact Submodule.zero_mem _
    · cases b
      · change x ∈ T.A j at hx
        rw [hzero x (E.killed ((show T.A j ≤ T.U i ⊔ T.A j from le_sup_right) hx))]
        exact Submodule.zero_mem _
      · exact E.block.target (him x)
    · cases b
      · exact E.block.source (him x)
      · exact T.side_le_signal k (E.block.source (him x))
  have hr : LinearMap.range f = P := by
    apply le_antisymm
    · rintro x ⟨y,rfl⟩; exact (g y).property
    · intro x hx; exact ⟨x,hfix x hx⟩
  refine ⟨LinearMap.ker f, ?_⟩
  have hh := TaskDecomposition.stable_projection_split (configuration T).spaces f
    hstable (fun x => hfix _ (g x).property)
  rwa [hr] at hh

/-- A physical edge block is either wholly present or wholly absent in
each of the six flags. -/
theorem EdgeBlock.pure {T : UploadBroadcast.Task K V} {i j k : Three}
    {W : Submodule K V} (h : EdgeBlock T i j k W)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ l, W ≤ (configuration T).spaces l ∨ Disjoint W ((configuration T).spaces l) := by
  rintro ⟨l,b⟩
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hl : l = i ∨ l = j ∨ l = k := by
    have : l.val = i.val ∨ l.val = j.val ∨ l.val = k.val := by omega
    exact this.imp Fin.ext (fun h => h.imp Fin.ext Fin.ext)
  rcases hl with hl | hl | hl <;> subst l
  · cases b
    · exact Or.inr (h.third_zero.mono_right (T.side_le_signal i))
    · exact Or.inr h.third_zero
  · cases b
    · exact Or.inr h.target_side_zero
    · exact Or.inl h.target
  · cases b
    · exact Or.inl h.source
    · exact Or.inl (h.source.trans (T.side_le_signal k))

/-- Any selected coordinate subspace of an edge has a stable projection
which still kills every other edge block. -/
theorem exists_subblock_projection [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (e : Edge) (P : Submodule K V)
    (hP : P ≤ (edgeExtraction T e).W) :
    ∃ f : V →ₗ[K] V,
      TaskDecomposition.Stable (configuration T).spaces f ∧
      (∀ x, f x ∈ P) ∧ (∀ x ∈ P, f x = x) ∧
      ∀ d : Edge, e ≠ d → ∀ x ∈ (edgeExtraction T d).W, f x = 0 := by
  classical
  obtain ⟨C, hC⟩ := P.exists_isCompl
  let g := P.linearProjOfIsCompl C hC
  let f : V →ₗ[K] V := (P.subtype.comp g).comp (edgeExtraction T e).projection
  have him (x : V) : f x ∈ P := (g ((edgeExtraction T e).projection x)).property
  refine ⟨f, ?_, him, ?_, ?_⟩
  · intro l x hx
    rcases (edgeExtraction T e).block.pure e.property.1 e.property.2.1 e.property.2.2 l with h | h
    · exact h (hP (him x))
    · have hz : (edgeExtraction T e).projection x = 0 :=
        h.le_bot ⟨edge_projection_mem T e x, (edgeExtraction T e).stable l x hx⟩
      change ((g ((edgeExtraction T e).projection x) : P) : V) ∈ _
      rw [hz, map_zero]
      exact Submodule.zero_mem _
  · intro x hx
    change ((g ((edgeExtraction T e).projection x) : P) : V) = x
    rw [(edgeExtraction T e).fixes x (hP hx)]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC (⟨x,hx⟩ : P))
  · intro d hed x hx
    change ((g ((edgeExtraction T e).projection x) : P) : V) = 0
    rw [edge_projection_kills_other T e d hed x hx, map_zero]
    rfl

/-- Any selected number of coordinates from any of the six edge blocks
can be split simultaneously. This is the physical cycle-grouping step. -/
theorem simultaneous_subblocks [FiniteDimensional K V]
    (T : UploadBroadcast.Task K V) (P : Edge → Submodule K V)
    (hP : ∀ e, P e ≤ (edgeExtraction T e).W) :
    iSupIndep P ∧ ∃ Q : Submodule K V,
      TaskDecomposition.Split (configuration T).spaces ⊤ Q (⨆ e, P e) := by
  classical
  choose f hf him hfix hkill using fun e => exists_subblock_projection T e (P e) (hP e)
  let g : V →ₗ[K] V := ∑ e : Edge, f e
  have hgf (e : Edge) (x : V) (hx : x ∈ P e) : g x = x := by
    change (∑ d : Edge, f d) x = x
    rw [LinearMap.sum_apply, Finset.sum_eq_single e]
    · exact hfix e x hx
    · intro d _ hde; exact hkill d e hde x (hP e hx)
    · simp
  have hstable : TaskDecomposition.Stable (configuration T).spaces g := by
    intro l x hx
    change (∑ e : Edge, f e) x ∈ _
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun e _ => hf e l x hx)
  have hid (x : V) : g (g x) = g x := by
    change g ((∑ e : Edge, f e) x) = (∑ e : Edge, f e) x
    simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun e _ => hgf e _ (him e x))
  have hr : LinearMap.range g = ⨆ e, P e := by
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      change (∑ e : Edge, f e) y ∈ _
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ (fun e _ => (le_iSup P e) (him e y))
    · exact iSup_le fun e x hx => ⟨x, hgf e x hx⟩
  refine ⟨(edge_blocks_independent T).mono hP, LinearMap.ker g, ?_⟩
  have hs := TaskDecomposition.stable_projection_split (configuration T).spaces g hstable hid
  rwa [hr] at hs

end UploadBroadcast.EdgeExtraction
