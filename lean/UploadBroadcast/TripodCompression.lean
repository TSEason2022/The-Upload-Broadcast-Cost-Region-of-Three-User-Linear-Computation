import UploadBroadcast.ThreeSubspaceNormalForm
import UploadBroadcast.Profile
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Explicit original-field two-copy compression of a nonzero tripod. -/
namespace UploadBroadcast.TripodCompression
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

private theorem normalized_separator (S : Submodule K F) (a : F) (ha : a ∉ S) :
    ∃ f : F →ₗ[K] K, f a = 1 ∧ ∀ b ∈ S, f b = 0 := by
  obtain ⟨f,hfa,hfS⟩ := S.exists_dual_map_eq_bot_of_nmem ha inferInstance
  refine ⟨(f a)⁻¹ • f, by simp [hfa], ?_⟩
  intro b hb
  have h : f b ∈ S.map f := ⟨b,hb,rfl⟩
  rw [hfS] at h
  have hz : f b = 0 := h
  simp [hz]

private theorem sup_kernel_eq_top (S : Submodule K F) (f : F →ₗ[K] K)
    (z : F) (hz : z ∈ S) (hfz : f z = 1) : S ⊔ LinearMap.ker f = ⊤ := by
  apply top_unique
  intro x _
  refine Submodule.mem_sup.mpr ⟨f x • z, S.smul_mem _ hz,
    x - f x • z, ?_, by abel⟩
  change f (x - f x • z) = 0
  simp [hfz]

/-- A nonzero dependency between three pairwise-disjoint spanning sides
produces a proper, locally generated relay on two copies. Every user can
recover the entire doubled ambient space from that relay and its own side.
The construction is the kernel of an explicit scalar linear functional. -/
theorem exists_compressed_double (A B C : Submodule K F)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hspan : (A ⊔ B) ⊔ C = ⊤) (hdep : C ⊓ (A ⊔ B) ≠ ⊥) :
    ∃ Q : Submodule K (F × F),
      Q ≠ ⊤ ∧
      Q = ((Q ⊓ A.prod A) ⊔ (Q ⊓ B.prod B)) ⊔ (Q ⊓ C.prod C) ∧
      A.prod A ⊔ Q = ⊤ ∧ B.prod B ⊔ Q = ⊤ ∧ C.prod C ⊔ Q = ⊤ := by
  obtain ⟨c,hc,hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdep
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hc.2
  have haB : a ∉ B := by
    intro haB
    have ha0 : a = 0 := (Submodule.disjoint_def.mp hAB) a ha haB
    have hbc : c ∈ B := by rw [← hab,ha0,zero_add]; exact hb
    exact hc0 ((Submodule.disjoint_def.mp hBC) c hbc hc.1)
  have hbA : b ∉ A := by
    intro hbA
    have hb0 : b = 0 := (Submodule.disjoint_def.mp hAB) b hbA hb
    have hac : c ∈ A := by rw [← hab,hb0,add_zero]; exact ha
    exact hc0 ((Submodule.disjoint_def.mp hAC) c hac hc.1)
  obtain ⟨f,hfa,hfB⟩ := normalized_separator B a haB
  obtain ⟨g,hgb,hgA⟩ := normalized_separator A b hbA
  have hfb : f b = 0 := hfB b hb
  have hga : g a = 0 := hgA a ha
  have hfc : f c = 1 := by rw [← hab,map_add,hfa,hfb,add_zero]
  have hgc : g c = 1 := by rw [← hab,map_add,hga,hgb,zero_add]
  let l : (F × F) →ₗ[K] K := f.comp (LinearMap.fst K F F) + g.comp (LinearMap.snd K F F)
  have hl (x : F × F) : l x = f x.1 + g x.2 := rfl
  let Q := LinearMap.ker l
  have hla : l (a,0) = 1 := by simp [hl,hfa]
  have hlb : l (0,b) = 1 := by simp [hl,hgb]
  have hlc : l (c,0) = 1 := by simp [hl,hfc]
  have hn : Q ≠ ⊤ := by
    intro h
    have hh : (a,0) ∈ Q := h.symm ▸ Submodule.mem_top
    exact one_ne_zero (hla.symm.trans hh)
  have hdouble : ((A.prod A) ⊔ (B.prod B)) ⊔ (C.prod C) = ⊤ := by
    rw [Submodule.prod_sup_prod,Submodule.prod_sup_prod,hspan]
    simp
  refine ⟨Q,hn,le_antisymm ?_ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left),
    sup_kernel_eq_top (A.prod A) l (a,0) ⟨ha,A.zero_mem⟩ hla,
    sup_kernel_eq_top (B.prod B) l (0,b) ⟨B.zero_mem,hb⟩ hlb,
    sup_kernel_eq_top (C.prod C) l (c,0) ⟨hc.1,C.zero_mem⟩ hlc⟩
  intro x hx
  have hxm : x ∈ ((A.prod A) ⊔ (B.prod B)) ⊔ (C.prod C) := hdouble.symm ▸ Submodule.mem_top
  obtain ⟨ab,hab',cc,hcc,habc⟩ := Submodule.mem_sup.mp hxm
  obtain ⟨aa,haa,bb,hbb,he⟩ := Submodule.mem_sup.mp hab'
  have hsum : aa + bb + cc = x := by rw [he,habc]
  let α := l aa
  let β := l bb
  let wa : F × F := (α • a,β • a)
  let wb : F × F := (α • b,β • b)
  let wc : F × F := (α • c,β • c)
  have hwa : wa ∈ A.prod A := ⟨A.smul_mem _ ha,A.smul_mem _ ha⟩
  have hwb : wb ∈ B.prod B := ⟨B.smul_mem _ hb,B.smul_mem _ hb⟩
  have hwc : wc ∈ C.prod C := ⟨C.smul_mem _ hc.1,C.smul_mem _ hc.1⟩
  have hwa' : l wa = α := by simp [wa,hl,hfa,hga]
  have hwb' : l wb = β := by simp [wb,hl,hfb,hgb]
  have hwc' : l wc = α + β := by simp [wc,hl,hfc,hgc]
  have habw : wa + wb = wc := by ext <;> simp [wa,wb,wc,← smul_add,hab]
  have hzero : α + β + l cc = 0 := by
    have := congrArg l hsum
    simpa only [map_add,show l x = 0 from hx] using this
  have hqaa : aa - wa ∈ Q := by change l (aa-wa) = 0; simp [hwa',α]
  have hqbb : bb - wb ∈ Q := by change l (bb-wb) = 0; simp [hwb',β]
  have hqcc : cc + wc ∈ Q := by change l (cc+wc) = 0; rw [map_add,hwc']; linear_combination hzero
  apply Submodule.mem_sup.mpr
  refine ⟨(aa-wa)+(bb-wb),Submodule.add_mem_sup ⟨hqaa,(A.prod A).sub_mem haa hwa⟩
    ⟨hqbb,(B.prod B).sub_mem hbb hwb⟩,cc+wc,⟨hqcc,(C.prod C).add_mem hcc hwc⟩,?_⟩
  rw [← habw,← hsum]
  abel

/-- The strict saving is in actual coefficient dimension. -/
theorem exists_compressed_double_finrank [FiniteDimensional K F]
    (A B C : Submodule K F)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hspan : (A ⊔ B) ⊔ C = ⊤) (hdep : C ⊓ (A ⊔ B) ≠ ⊥) :
    ∃ Q : Submodule K (F × F),
      finrank K Q < 2 * finrank K F ∧
      Q = ((Q ⊓ A.prod A) ⊔ (Q ⊓ B.prod B)) ⊔ (Q ⊓ C.prod C) ∧
      A.prod A ⊔ Q = ⊤ ∧ B.prod B ⊔ Q = ⊤ ∧ C.prod C ⊔ Q = ⊤ := by
  obtain ⟨Q,hn,hl,h₁,h₂,h₃⟩ := exists_compressed_double A B C hAB hAC hBC hspan hdep
  refine ⟨Q,?_,hl,h₁,h₂,h₃⟩
  have h := Submodule.finrank_lt hn
  simpa only [finrank_top,Module.finrank_prod,two_mul] using h

end UploadBroadcast.TripodCompression
