import UploadBroadcast.ResidualPureTransport

/-! Intrinsic geometric consequences of the canonical private/tripod chart. -/
namespace UploadBroadcast.ResidualIntrinsicGeometry
open ResidualUpload ResidualTaskAssembly
set_option maxHeartbeats 2000000
variable {K F V P₁ P₂ P₃ D : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup P₁] [Module K P₁] [AddCommGroup P₂] [Module K P₂]
  [AddCommGroup P₃] [Module K P₃] [AddCommGroup D] [Module K D]

/-- Surjectivity of a coordinate projection plus its kernel spans the ambient. -/
theorem sup_eq_top_of_projection (U W : Submodule K F) (p : F →ₗ[K] V)
    (hker : LinearMap.ker p ≤ U ⊔ W)
    (hused : U.map p ⊔ W.map p = ⊤) : U ⊔ W = ⊤ := by
  apply top_unique
  intro x _
  have hx : p x ∈ (U ⊔ W).map p := by rw [Submodule.map_sup,hused]; trivial
  obtain ⟨y,hy,he⟩ := hx
  have hz : x-y ∈ LinearMap.ker p := by
    change p (x-y) = 0
    rw [map_sub,he,sub_self]
  simpa only [sub_add_cancel] using (U ⊔ W).add_mem (hker hz) hy

variable (task : Task K (Ambient P₁ P₂ P₃ D))
  (h₀ : task.A 0 = A₁ K P₁ P₂ P₃ D)
  (h₁ : task.A 1 = A₂ K P₁ P₂ P₃ D)
  (h₂ : task.A 2 = A₃ K P₁ P₂ P₃ D)

include h₀ h₁ h₂

/-- Once every private direction is used remotely, each pair of signals spans. -/
theorem signal_pair_spanning
    (hu₁ : used₁ task = ⊤) (hu₂ : used₂ task = ⊤) (hu₃ : used₃ task = ⊤) :
    task.U 0 ⊔ task.U 1 = ⊤ ∧ task.U 0 ⊔ task.U 2 = ⊤ ∧ task.U 1 ⊔ task.U 2 = ⊤ := by
  refine ⟨sup_eq_top_of_projection _ _ private₃ ?_ hu₃,
    sup_eq_top_of_projection _ _ private₂ ?_ hu₂,
    sup_eq_top_of_projection _ _ private₁ ?_ hu₁⟩
  · intro x hx
    have hz : x.1.2 = 0 := hx
    have ha : side₁ (K := K) (x.1.1.1,x.2.1) ∈ task.A 0 := by rw [h₀]; exact ⟨_,rfl⟩
    have hb : side₂ (K := K) (x.1.1.2,x.2.2) ∈ task.A 1 := by rw [h₁]; exact ⟨_,rfl⟩
    have hh := Submodule.add_mem_sup (task.side_le_signal 0 ha) (task.side_le_signal 1 hb)
    convert hh using 1; ext <;> simp [side₁,side₂,hz]
  · intro x hx
    have hz : x.1.1.2 = 0 := hx
    have ha : side₁ (K := K) (x.1.1.1,x.2.1+x.2.2) ∈ task.A 0 := by rw [h₀]; exact ⟨_,rfl⟩
    have hb : side₃ (K := K) (x.1.2,x.2.2) ∈ task.A 2 := by rw [h₂]; exact ⟨_,rfl⟩
    have hh := Submodule.add_mem_sup (task.side_le_signal 0 ha) (task.side_le_signal 2 hb)
    convert hh using 1; ext <;> simp [side₁,side₃,hz]
  · intro x hx
    have hz : x.1.1.1 = 0 := hx
    have ha : side₂ (K := K) (x.1.1.2,x.2.2+x.2.1) ∈ task.A 1 := by rw [h₁]; exact ⟨_,rfl⟩
    have hb : side₃ (K := K) (x.1.2,-x.2.1) ∈ task.A 2 := by rw [h₂]; exact ⟨_,rfl⟩
    have hh := Submodule.add_mem_sup (task.side_le_signal 1 ha) (task.side_le_signal 2 hb)
    convert hh using 1; ext <;> simp [side₂,side₃,hz]

/-- The first intrinsic side-overlap core is exactly the v copy of tripod rows. -/
theorem tripod_side_core :
    task.A 0 ⊓ (task.A 1 ⊔ task.A 2) = LinearMap.range
      (embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (D := D)) := by
  rw [h₀,h₁,h₂]
  apply le_antisymm
  · rintro x ⟨⟨⟨p,d⟩,rfl⟩,hx⟩
    obtain ⟨b,⟨⟨q,e⟩,rfl⟩,c,⟨⟨r,f⟩,rfl⟩,he⟩ := Submodule.mem_sup.mp hx
    have hp : p = 0 := by
      have hh := congrArg (fun z : Ambient P₁ P₂ P₃ D => z.1.1.1) he
      simpa [side₁,side₂,side₃] using hh.symm
    exact ⟨d,by simp [embedV,side₁,hp]⟩
  · rintro x ⟨d,rfl⟩
    refine ⟨⟨(0,d),rfl⟩,?_⟩
    have h := Submodule.add_mem_sup
      (show side₂ (K := K) (0,d) ∈ A₂ K P₁ P₂ P₃ D from ⟨_,rfl⟩)
      (show side₃ (K := K) (0,-d) ∈ A₃ K P₁ P₂ P₃ D from ⟨_,rfl⟩)
    convert h using 1; ext <;> simp [embedV,side₁,side₂,side₃]

omit h₀ h₁ h₂ in
/-- Intrinsic common tripod seed inside the common signal space. -/
def commonSeed :=
  (task.A 0 ⊓ (task.U 0 ⊓ task.U 1 ⊓ task.U 2)) ⊓
    ((task.A 1 ⊓ (task.U 0 ⊓ task.U 1 ⊓ task.U 2)) ⊔
      (task.A 2 ⊓ (task.U 0 ⊓ task.U 1 ⊓ task.U 2)))

/-- Pure rows are the exact intrinsic common-tripod seed, in the v chart. -/
theorem commonSeed_eq_pure_image :
    commonSeed task = (pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task).map
      (embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)) := by
  let g := selectedDemandData task h₀ h₁ h₂
  obtain ⟨hd₀,hd₁,hd₂⟩ := g.pureRows_iff
  have hv₀ (d : D) : embedV (K := K) d ∈ task.U 0 :=
    task.side_le_signal 0 (by rw [h₀]; exact ⟨(0,d),rfl⟩)
  have hr₁ (d : D) : embedR (K := K) d ∈ task.U 1 :=
    task.side_le_signal 1 (by rw [h₁]; exact ⟨(0,d),rfl⟩)
  have hz₂ (d : D) : embedR (K := K) d - embedV (K := K) d ∈ task.U 2 :=
    task.side_le_signal 2 (by rw [h₂]; exact ⟨(0,d),by ext <;> simp [embedR,embedV,side₁,side₂,side₃]⟩)
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨ha,hxw⟩,hxsum⟩ := hx
    rw [h₀] at ha
    obtain ⟨⟨p,d⟩,rfl⟩ := ha
    obtain ⟨b,⟨hbA,hbW⟩,c,⟨hcA,hcW⟩,he⟩ := Submodule.mem_sup.mp hxsum
    rw [h₁] at hbA
    rw [h₂] at hcA
    obtain ⟨⟨q,e⟩,rfl⟩ := hbA
    obtain ⟨⟨r,f⟩,rfl⟩ := hcA
    have hp : p = 0 := by
      simpa [side₁,side₂,side₃] using
        (congrArg (fun z : Ambient P₁ P₂ P₃ D => z.1.1.1) he).symm
    have hq : q = 0 := by
      simpa [side₁,side₂,side₃] using
        congrArg (fun z : Ambient P₁ P₂ P₃ D => z.1.1.2) he
    have hef : e+f = 0 := by
      simpa [side₁,side₂,side₃] using
        congrArg (fun z : Ambient P₁ P₂ P₃ D => z.2.2) he
    have hfd : -f = d := by
      simpa [side₁,side₂,side₃] using
        congrArg (fun z : Ambient P₁ P₂ P₃ D => z.2.1) he
    have hed : e = d := by
      have hn : e = -f := eq_neg_of_add_eq_zero_left hef
      exact hn.trans hfd
    have hv : (side₁ (K := K) (p,d) : Ambient P₁ P₂ P₃ D) = embedV (K := K) d := by simp [hp,embedV,side₁]
    have hr : (side₂ (K := K) (q,e) : Ambient P₁ P₂ P₃ D) = embedR (K := K) d := by simp [hq,hed,embedR,side₂]
    refine ⟨d,⟨⟨(hd₀ d).mpr ?_,(hd₁ d).mpr ?_⟩,(hd₂ d).mpr ?_⟩,hv.symm⟩
    · simpa only [hr] using hbW.1.1
    · simpa only [hv] using hxw.1.2
    · simpa only [hv] using hxw.2
  · rintro x ⟨d,⟨⟨hd0,hd1⟩,hd2⟩,rfl⟩
    have hvW : embedV (K := K) d ∈ task.U 0 ⊓ task.U 1 ⊓ task.U 2 :=
      ⟨⟨hv₀ d,(hd₁ d).mp hd1⟩,(hd₂ d).mp hd2⟩
    have hr₂ : embedR (K := K) d ∈ task.U 2 := by
      have h := (task.U 2).add_mem (hz₂ d) ((hd₂ d).mp hd2)
      simpa only [sub_add_cancel] using h
    have hrW : embedR (K := K) d ∈ task.U 0 ⊓ task.U 1 ⊓ task.U 2 :=
      ⟨⟨(hd₀ d).mp hd0,hr₁ d⟩,hr₂⟩
    refine ⟨⟨by rw [h₀]; exact ⟨(0,d),rfl⟩,hvW⟩,?_⟩
    apply Submodule.mem_sup.mpr
    refine ⟨embedR (K := K) d,⟨by rw [h₁]; exact ⟨(0,d),rfl⟩,hrW⟩,
      embedV (K := K) d - embedR (K := K) d,⟨?_,(task.U 0 ⊓ task.U 1 ⊓ task.U 2).sub_mem hvW hrW⟩,?_⟩
    · rw [h₂]
      exact ⟨(0,-d),by ext <;> simp [embedV,embedR,side₁,side₂,side₃]⟩
    · abel

/-- In particular, zero common pure rows imply zero intrinsic common seed. -/
theorem commonSeed_eq_bot
    (hzero : pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥) :
    commonSeed task = ⊥ := by
  rw [commonSeed_eq_pure_image task h₀ h₁ h₂,hzero,Submodule.map_bot]

/-- The common pure-row and intrinsic common-seed vanishing criteria agree. -/
theorem commonSeed_eq_bot_iff :
    commonSeed task = ⊥ ↔ pureRows₁ task ⊓ pureRows₂ task ⊓ pureRows₃ task = ⊥ := by
  constructor
  · intro hz
    apply le_antisymm _ bot_le
    intro d hd
    have hv : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d ∈ commonSeed task := by
      rw [commonSeed_eq_pure_image task h₀ h₁ h₂]
      exact ⟨d,hd,rfl⟩
    rw [hz] at hv
    have he : embedV (K := K) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) d = 0 := hv
    change d = 0
    exact congrArg (fun x : Ambient P₁ P₂ P₃ D => x.2.1) he
  · exact commonSeed_eq_bot task h₀ h₁ h₂

/-- Label-independent pairwise spanning for every distinct pair of users. -/
theorem all_signal_pairs_spanning
    (hu₁ : used₁ task = ⊤) (hu₂ : used₂ task = ⊤) (hu₃ : used₃ task = ⊤) :
    ∀ i j : Three, i ≠ j → task.U i ⊔ task.U j = ⊤ := by
  obtain ⟨ha,hb,hc⟩ := signal_pair_spanning task h₀ h₁ h₂ hu₁ hu₂ hu₃
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ha
  · exact hb
  · exact (sup_comm (task.U 1) (task.U 0)).trans ha
  · exact (hij rfl).elim
  · exact hc
  · exact (sup_comm (task.U 2) (task.U 0)).trans hb
  · exact (sup_comm (task.U 2) (task.U 1)).trans hc
  · exact (hij rfl).elim

end UploadBroadcast.ResidualIntrinsicGeometry
