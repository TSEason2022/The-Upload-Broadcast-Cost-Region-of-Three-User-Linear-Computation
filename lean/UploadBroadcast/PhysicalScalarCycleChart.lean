import UploadBroadcast.PhysicalCycleCoordinates
import UploadBroadcast.CycleDirectSumCoordinates

namespace UploadBroadcast.PhysicalScalarCycleChart
open Module CycleDirectSumCoordinates EdgeExtraction PhysicalCycleCoordinates
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev line (v : Three → V) (i : Three) := Submodule.span K {v i}
abbrev coefficients (v : Three → V) := Fintype.linearCombination K v

theorem map_side₀ (v : Three → V) : (side₀ K).map (coefficients v)=line v 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x 0=0 ∧ x 2=0 at hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨x 1,by simp [coefficients,Fintype.linearCombination_apply,Fin.sum_univ_succ,hx.1,hx.2]⟩
  · intro hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨![0,a,0],by change _=0 ∧ _=0; simp,?_⟩
    simp [coefficients,Fintype.linearCombination_apply,Fin.sum_univ_succ]

theorem map_side₁ (v : Three → V) : (side₁ K).map (coefficients v)=line v 2 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x 0=0 ∧ x 1=0 at hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨x 2,by simp [coefficients,Fintype.linearCombination_apply,Fin.sum_univ_succ,hx.1,hx.2]⟩
  · intro hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨![0,0,a],by change _=0 ∧ _=0; simp,?_⟩
    simp [coefficients,Fintype.linearCombination_apply,Fin.sum_univ_succ]

theorem map_side₂ (v : Three → V) : (side₂ K).map (coefficients v)=line v 0 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x 1=0 ∧ x 2=0 at hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨x 0,by simp [coefficients,Fintype.linearCombination_apply,Fin.sum_univ_succ,hx.1,hx.2]⟩
  · intro hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨![a,0,0],by change _=0 ∧ _=0; simp,?_⟩
    simp [coefficients,Fintype.linearCombination_apply,Fin.sum_univ_succ]

theorem signal₀_eq : signals K 0=side₀ K ⊔ side₁ K := by
  ext x
  constructor
  · intro hx
    change x 0=0 at hx
    refine Submodule.mem_sup.mpr ⟨![0,x 1,0],by change _=0 ∧ _=0; simp,
      ![0,0,x 2],by change _=0 ∧ _=0; simp,?_⟩
    funext i; fin_cases i <;> simp [hx]
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    change a 0+b 0=0
    simp only [show a 0=0 from ha.1,show b 0=0 from hb.1,add_zero]

theorem signal₁_eq : signals K 1=side₁ K ⊔ side₂ K := by
  ext x
  constructor
  · intro hx
    change x 1=0 at hx
    refine Submodule.mem_sup.mpr ⟨![0,0,x 2],by change _=0 ∧ _=0; simp,
      ![x 0,0,0],by change _=0 ∧ _=0; simp,?_⟩
    funext i; fin_cases i <;> simp [hx]
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    change a 1+b 1=0
    simp only [show a 1=0 from ha.2,show b 1=0 from hb.1,add_zero]

theorem signal₂_eq : signals K 2=side₂ K ⊔ side₀ K := by
  ext x
  constructor
  · intro hx
    change x 2=0 at hx
    refine Submodule.mem_sup.mpr ⟨![x 0,0,0],by change _=0 ∧ _=0; simp,
      ![0,x 1,0],by change _=0 ∧ _=0; simp,?_⟩
    funext i; fin_cases i <;> simp [hx]
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    change a 2+b 2=0
    simp only [show a 2=0 from ha.2,show b 2=0 from hb.2,add_zero]

theorem locally_generated (T : Task K V) (v : Three → V)
    (h₀ : EdgeBlock T 0 1 2 (line v 0)) (h₁ : EdgeBlock T 1 2 0 (line v 1))
    (h₂ : EdgeBlock T 2 0 1 (line v 2)) :
    T.LocallyGenerated (Submodule.span K (Set.range v)) := by
  rw [Submodule.span_range_eq_iSup,Profile.three_iSup]
  exact bundle_locally_generated T _ _ _ h₀ h₁ h₂

/-- A scalar physical cycle, extracted from actual edge subspaces, has
exactly the canonical cycle coordinates. No requested flag identity is assumed. -/
theorem image_task_eq (T : Task K V) (v : Three → V)
    (h₀ : EdgeBlock T 0 1 2 (line v 0)) (h₁ : EdgeBlock T 1 2 0 (line v 1))
    (h₂ : EdgeBlock T 2 0 1 (line v 2)) :
    (cycleTask K).imageTask (coefficients v) =
      NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (locally_generated T v h₀ h₁ h₂) := by
  obtain ⟨ha₀,ha₁,ha₂,hu₀,hu₁,hu₂⟩ := bundle_signature T _ _ _ h₀ h₁ h₂
  have hW : Submodule.span K (Set.range v)=line v 0 ⊔ line v 1 ⊔ line v 2 := by
    rw [Submodule.span_range_eq_iSup,Profile.three_iSup]
  have hA : ((cycleTask K).imageTask (coefficients v)).A =
      (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (locally_generated T v h₀ h₁ h₂)).A := by
    funext i
    change (sides K i).map (coefficients v)=T.A i ⊓ Submodule.span K (Set.range v)
    rw [hW]
    fin_cases i
    · exact (map_side₀ v).trans ha₀.symm
    · exact (map_side₁ v).trans ha₁.symm
    · exact (map_side₂ v).trans ha₂.symm
  have hU : ((cycleTask K).imageTask (coefficients v)).U =
      (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (locally_generated T v h₀ h₁ h₂)).U := by
    funext i
    change (signals K i).map (coefficients v)=T.U i ⊓ Submodule.span K (Set.range v)
    rw [hW]
    fin_cases i
    · change (signals K 0).map _ = _
      rw [signal₀_eq,Submodule.map_sup,map_side₀,map_side₁]
      exact hu₀.symm
    · change (signals K 1).map _ = _
      rw [signal₁_eq,Submodule.map_sup,map_side₁,map_side₂,sup_comm]
      exact hu₁.symm
    · change (signals K 2).map _ = _
      rw [signal₂_eq,Submodule.map_sup,map_side₂,map_side₀]
      exact hu₂.symm
  cases h : (cycleTask K).imageTask (coefficients v)
  cases h' : NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (locally_generated T v h₀ h₁ h₂)
  simp_all only [Task.mk.injEq]

/-- The coordinate chart is injective and its range is precisely the actual
three-edge span. This is the physical-to-canonical cycle identification. -/
theorem actual_cycle_chart (T : Task K V) (v : Three → V) (hv : LinearIndependent K v)
    (h₀ : EdgeBlock T 0 1 2 (line v 0)) (h₁ : EdgeBlock T 1 2 0 (line v 1))
    (h₂ : EdgeBlock T 2 0 1 (line v 2)) :
    Function.Injective (coefficients (K := K) v) ∧
      LinearMap.range (coefficients (K := K) v)=Submodule.span K (Set.range v) ∧
      (cycleTask K).imageTask (coefficients v) =
        NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
          (locally_generated T v h₀ h₁ h₂) :=
  ⟨hv.fintypeLinearCombination_injective,Fintype.range_linearCombination K v,
    image_task_eq T v h₀ h₁ h₂⟩

/-- Every selected copy in an extracted bundle has three independent physical
edges in the chosen user orientation. -/
theorem bundle_copy_edges (T : Task K V) (p : Equiv.Perm Three) {r : ℕ}
    (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (hb : ∀ a, EdgeBlock T (EdgeDeficits.cyclicPerm p a 0)
      (EdgeDeficits.cyclicPerm p a 1) (EdgeDeficits.cyclicPerm p a 2)
      (Submodule.span K (Set.range (v a)))) (t : Fin r) :
    LinearIndependent K (fun a => v a t) ∧
      EdgeBlock (Profile.reindexTask p T) 0 1 2 (line (fun a => v a t) 0) ∧
      EdgeBlock (Profile.reindexTask p T) 1 2 0 (line (fun a => v a t) 1) ∧
      EdgeBlock (Profile.reindexTask p T) 2 0 1 (line (fun a => v a t) 2) := by
  have hsub (a : Three) : line (fun a => v a t) a ≤ Submodule.span K (Set.range (v a)) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨t,rfl⟩)
  have h (a : Three) : EdgeBlock T (EdgeDeficits.cyclicPerm p a 0)
      (EdgeDeficits.cyclicPerm p a 1) (EdgeDeficits.cyclicPerm p a 2)
      (line (fun a => v a t) a) :=
    ⟨(hsub a).trans (hb a).source,(hsub a).trans (hb a).target,
      (hb a).third_zero.mono_left (hsub a),(hb a).target_side_zero.mono_left (hsub a)⟩
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have hh₀ : EdgeBlock T (p 0) (p 1) (p 2) (line (fun a => v a t) 0) := by
    simpa [EdgeDeficits.cyclicPerm] using h₀
  have hh₁ : EdgeBlock T (p 1) (p 2) (p 0) (line (fun a => v a t) 1) := by
    simpa [EdgeDeficits.cyclicPerm] using h₁
  have hh₂ : EdgeBlock T (p 2) (p 0) (p 1) (line (fun a => v a t) 2) := by
    simpa [EdgeDeficits.cyclicPerm] using h₂
  exact ⟨hv.comp (fun a => Sigma.mk a t) (by intro a b he; exact congrArg Sigma.fst he),
    ⟨hh₀.source,hh₀.target,hh₀.third_zero,hh₀.target_side_zero⟩,
    ⟨hh₁.source,hh₁.target,hh₁.third_zero,hh₁.target_side_zero⟩,
    ⟨hh₂.source,hh₂.target,hh₂.third_zero,hh₂.target_side_zero⟩⟩

/-- A physically extracted bundle supplies an injective canonical cycle chart
for each scalar copy, in either orientation after the indicated user labels. -/
theorem bundle_copy_chart (T : Task K V) (p : Equiv.Perm Three) {r : ℕ}
    (v : Three → Fin r → V)
    (hv : LinearIndependent K (fun x : (_a : Three) × Fin r => v x.1 x.2))
    (hb : ∀ a, EdgeBlock T (EdgeDeficits.cyclicPerm p a 0)
      (EdgeDeficits.cyclicPerm p a 1) (EdgeDeficits.cyclicPerm p a 2)
      (Submodule.span K (Set.range (v a)))) (t : Fin r) :
    ∃ hg : (Profile.reindexTask p T).LocallyGenerated (Submodule.span K (Set.range (fun a => v a t))),
      Function.Injective (coefficients (K := K) (fun a => v a t)) ∧
      LinearMap.range (coefficients (K := K) (fun a => v a t))=
        Submodule.span K (Set.range (fun a => v a t)) ∧
      (cycleTask K).imageTask (coefficients (fun a => v a t)) =
        NonzeroDefectRelays.inducedTask (Profile.reindexTask p T)
          (Submodule.span K (Set.range (fun a => v a t))) hg := by
  obtain ⟨hi,h₀,h₁,h₂⟩ := bundle_copy_edges T p v hv hb t
  exact ⟨locally_generated _ _ h₀ h₁ h₂,actual_cycle_chart _ _ hi h₀ h₁ h₂⟩

theorem reverse_locally_generated (T : Task K V) (v : Three → V)
    (h₀ : EdgeBlock T 1 0 2 (line v 0)) (h₁ : EdgeBlock T 2 1 0 (line v 1))
    (h₂ : EdgeBlock T 0 2 1 (line v 2)) :
    T.LocallyGenerated (Submodule.span K (Set.range v)) := by
  rw [Submodule.span_range_eq_iSup,Profile.three_iSup]
  exact reverse_bundle_locally_generated T _ _ _ h₀ h₁ h₂

/-- A scalar physical cycle, extracted from actual edge subspaces, has
exactly the canonical cycle coordinates. No requested flag identity is assumed. -/
theorem image_reverse_task_eq (T : Task K V) (v : Three → V)
    (h₀ : EdgeBlock T 1 0 2 (line v 0)) (h₁ : EdgeBlock T 2 1 0 (line v 1))
    (h₂ : EdgeBlock T 0 2 1 (line v 2)) :
    (reverseCycleTask K).imageTask (coefficients v) =
      NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (reverse_locally_generated T v h₀ h₁ h₂) := by
  obtain ⟨ha₀,ha₁,ha₂,hu₀,hu₁,hu₂⟩ := reverse_bundle_signature T _ _ _ h₀ h₁ h₂
  have hW : Submodule.span K (Set.range v)=line v 0 ⊔ line v 1 ⊔ line v 2 := by
    rw [Submodule.span_range_eq_iSup,Profile.three_iSup]
  have hA : ((reverseCycleTask K).imageTask (coefficients v)).A =
      (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (reverse_locally_generated T v h₀ h₁ h₂)).A := by
    funext i
    change (sides K i).map (coefficients v)=T.A i ⊓ Submodule.span K (Set.range v)
    rw [hW]
    fin_cases i
    · exact (map_side₀ v).trans ha₀.symm
    · exact (map_side₁ v).trans ha₁.symm
    · exact (map_side₂ v).trans ha₂.symm
  have hU : ((reverseCycleTask K).imageTask (coefficients v)).U =
      (NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (reverse_locally_generated T v h₀ h₁ h₂)).U := by
    funext i
    change (![signals K 2,signals K 0,signals K 1] i).map (coefficients v)=T.U i ⊓ Submodule.span K (Set.range v)
    rw [hW]
    fin_cases i
    · change (signals K 2).map _ = _
      rw [signal₂_eq,Submodule.map_sup,map_side₂,map_side₀]
      exact hu₀.symm
    · change (signals K 0).map _ = _
      rw [signal₀_eq,Submodule.map_sup,map_side₀,map_side₁]
      exact hu₁.symm
    · change (signals K 1).map _ = _
      rw [signal₁_eq,Submodule.map_sup,map_side₁,map_side₂,sup_comm]
      exact hu₂.symm
  cases h : (reverseCycleTask K).imageTask (coefficients v)
  cases h' : NonzeroDefectRelays.inducedTask T (Submodule.span K (Set.range v))
        (reverse_locally_generated T v h₀ h₁ h₂)
  simp_all only [Task.mk.injEq]

end UploadBroadcast.PhysicalScalarCycleChart
