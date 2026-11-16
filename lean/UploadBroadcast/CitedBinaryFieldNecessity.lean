import UploadBroadcast.GeneralBroadcastOptimum
import UploadBroadcast.OmniscienceProfile
import UploadBroadcast.Examples

/-! The binary-plane LCBC example: D*=1 but every scalar nonlinear broadcast
has at least four attainable symbols. This witnesses failure at ceil(D*),
unlike the separate five-bit half-integral example. -/
namespace UploadBroadcast.CitedBinaryFieldNecessity
open Module
abbrev K := ZMod 2
abbrev F := K × K

def sideMap : Three → K →ₗ[K] F :=
  ![LinearMap.inl K K K,LinearMap.inr K K K,(LinearMap.id : K→ₗ[K]K).prod LinearMap.id]

def side (i : Three) : Submodule K F := LinearMap.range (sideMap i)

theorem sideMap_injective (i : Three) : Function.Injective (sideMap i) := by
  intro a b h
  fin_cases i <;> simpa [sideMap] using h

theorem side_rank (i : Three) : finrank K (side i)=1 := by
  rw [side,LinearMap.finrank_range_of_inj (sideMap_injective i)]
  simp

theorem side_span : (⨆ i, side i)=⊤ := by
  apply top_unique
  intro x _
  have ha : (x.1,0) ∈ ⨆ i, side i :=
    (le_iSup side 0) ⟨x.1,rfl⟩
  have hb : (0,x.2) ∈ ⨆ i, side i :=
    (le_iSup side 1) ⟨x.2,rfl⟩
  simpa using Submodule.add_mem (⨆ i, side i) ha hb

def task : Task K F where
  A := side
  U _ := ⊤
  side_le_signal _ := le_top
  feasible _ := by rw [side_span]

@[simp] theorem signal_top (i : Three) : task.U i=⊤ := rfl
@[simp] theorem task_side_rank (i : Three) : finrank K (task.A i)=1 := side_rank i

theorem deficit (i : Three) : condRank (⊤ : Submodule K F) (task.A i)=1 := by
  rw [condRank,sup_top_eq,finrank_top,task_side_rank]
  norm_num [F,Module.finrank_prod]

theorem totalDemand : Profile.totalDemand task=3 := by
  unfold Profile.totalDemand
  simp only [signal_top,finrank_top,task_side_rank]
  norm_num [F,Module.finrank_prod,Fin.sum_univ_succ]

theorem all_entries (r : Profile.Index) : Profile.entry task r=1 := by
  cases r with
  | inl r =>
    simp only [Profile.entry,Profile.firstEntry,totalDemand,signal_top,
      top_inf_eq,inf_top_eq,top_sup_eq,sup_top_eq,deficit]
    norm_num
  | inr r =>
    simp only [Profile.entry,Profile.secondEntry,totalDemand,signal_top,
      top_inf_eq,inf_top_eq,top_sup_eq,sup_top_eq,deficit]
    norm_num

theorem broadcastOptimum_eq_one : broadcastOptimum task.A task.U=1 := by
  rw [task_general_broadcastOptimum_eq_rankBound]
  apply le_antisymm
  · apply Finset.sup'_le
    intro r _
    exact (all_entries r).le
  · rw [←all_entries (.inl 0)]
    exact Profile.entry_le_rankBound task _

def valueSource (a : F) : Source K F 1 where
  toFun x _ := a.1*x.1+a.2*x.2
  map_add' := by intro x y; ext i; simp; ring
  map_smul' := by intro c x; ext i; simp; ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Kernel reduction checks the three binary lines cover all annihilator
directions. No native evaluation or rank identity is assumed. -/
theorem side_equal_exists (a b : F) :
    ∃ i : Three, ∀ t : K,
      a.1*(sideMap i t).1+a.2*(sideMap i t).2=
        b.1*(sideMap i t).1+b.2*(sideMap i t).2 := by
  revert a b
  decide

/-- Every two distinct binary sources are confusable for at least one user. -/
theorem broadcast_source_injective {S : Type*} (c : BlockBroadcastCode task.A task.U 1 S) :
    Function.Injective (fun a : F => c.encode (valueSource a)) := by
  intro a b hab
  change c.encode (valueSource a)=c.encode (valueSource b) at hab
  obtain ⟨i,hi⟩ := side_equal_exists a b
  have hs : observe K F (task.A i) (valueSource a)=observe K F (task.A i) (valueSource b) := by
    ext x j
    obtain ⟨t,ht⟩ := x.property
    fin_cases j
    change a.1*x.val.1+a.2*x.val.2=b.1*x.val.1+b.2*x.val.2
    rw [←ht]
    exact hi t
  have hu : observe K F (task.U i) (valueSource a)=observe K F (task.U i) (valueSource b) := by
    rw [←c.zero_error (valueSource a) i,←c.zero_error (valueSource b) i,hab,hs]
  let e₀ : task.U i := ⟨(1,0),trivial⟩
  let e₁ : task.U i := ⟨(0,1),trivial⟩
  have h₀ := congrArg (fun f : task.U i →ₗ[K] (Fin 1→K) => f e₀ 0) hu
  have h₁ := congrArg (fun f : task.U i →ₗ[K] (Fin 1→K) => f e₁ 0) hu
  apply Prod.ext
  · simpa [observe,valueSource,e₀] using h₀
  · simpa [observe,valueSource,e₁] using h₁

theorem scalar_broadcast_card {S : Type*} [Finite S]
    (c : BlockBroadcastCode task.A task.U 1 S) : 4≤Nat.card (Set.range c.encode) := by
  let f : F → Set.range c.encode := fun a => ⟨c.encode (valueSource a),⟨valueSource a,rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    exact broadcast_source_injective c (congrArg Subtype.val h)
  have hh := Nat.card_le_card_of_injective f hf
  simpa [F,K,Nat.card_eq_fintype_card] using hh

/-- The original binary field needs two scalar symbols even though D*=1. -/
theorem scalar_cost_ge_two {S : Type*} [Finite S]
    (c : BlockBroadcastCode task.A task.U 1 S) : 2≤c.cost := by
  have hc : (4:ℝ)≤Nat.card (Set.range c.encode) := by exact_mod_cast scalar_broadcast_card c
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by norm_num : (0:ℝ)<4) hc
  rw [Examples.logb_two_four] at hh
  simpa [BlockBroadcastCode.cost,K,Nat.card_eq_fintype_card] using hh

/-- Source field-size necessity is witnessed at the rounded benchmark itself. -/
theorem scalar_cost_gt_ceiling {S : Type*} [Finite S]
    (c : BlockBroadcastCode task.A task.U 1 S) :
    ((⌈broadcastOptimum task.A task.U⌉:ℤ):ℝ)<c.cost := by
  rw [broadcastOptimum_eq_one]
  norm_num
  linarith [scalar_cost_ge_two c]

/-- Literal demand columns of the cited binary example, paired with side
columns (1,0), (0,1), and (1,1), respectively. -/
def demand : Three→F := ![(0,1),(1,1),(1,0)]

/-- Including these literal demands gives exactly the operational signal
spaces used above, so the counterexample is not a different omniscience task. -/
theorem signal_from_demands (i : Three) :
    task.A i ⊔ Submodule.span K {demand i}=task.U i := by
  have hn : ∀ (j : Three) (t : K), sideMap j t≠demand j := by decide
  have hd : demand i ∉ task.A i := by
    rintro ⟨t,ht⟩
    exact hn i t ht
  have hlt : task.A i < task.A i ⊔ Submodule.span K {demand i} := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    apply hd
    have hx : demand i ∈ task.A i ⊔ Submodule.span K {demand i} :=
      Submodule.mem_sup_right (Submodule.subset_span (by simp))
    rwa [←he] at hx
  have hr := Submodule.finrank_lt_finrank_of_lt hlt
  rw [task_side_rank] at hr
  have hf : finrank K F=2 := by simp [F,Module.finrank_prod]
  have hu := (task.A i ⊔ Submodule.span K {demand i}).finrank_le
  rw [hf] at hu
  rw [signal_top]
  apply Submodule.eq_of_le_of_finrank_eq le_top
  rw [finrank_top,hf]
  omega

end UploadBroadcast.CitedBinaryFieldNecessity
