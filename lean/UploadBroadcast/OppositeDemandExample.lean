import UploadBroadcast.ScalarPaperEndpoints

/-! The strict broadcast-subadditivity example at manuscript lines 1182–1189,
with the actual tasks, a scalar encoder x+y, and nonlinear operational costs. -/
namespace UploadBroadcast.OppositeDemandExample
open Module
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

/-- User 1 knows x; User 2 demands x; User 3 is empty. -/
def first : Task K K where
  A := ![⊤,⊥,⊥]
  U := ![⊤,⊤,⊥]
  side_le_signal i := by fin_cases i <;> simp
  feasible i := by rw [Profile.three_iSup]; fin_cases i <;> simp

/-- User 2 knows y; User 1 demands y; User 3 is empty. -/
def second : Task K K where
  A := ![⊥,⊤,⊥]
  U := ![⊤,⊤,⊥]
  side_le_signal i := by fin_cases i <;> simp
  feasible i := by rw [Profile.three_iSup]; fin_cases i <;> simp

/-- The actual independent direct sum, with source covectors on K × K. -/
def combined : Task K (K × K) := Profile.directSum (first K) (second K)

@[simp] theorem first_A : (first K).A = ![⊤,⊥,⊥] := rfl
@[simp] theorem first_U : (first K).U = ![⊤,⊤,⊥] := rfl
@[simp] theorem second_A : (second K).A = ![⊥,⊤,⊥] := rfl
@[simp] theorem second_U : (second K).U = ![⊤,⊤,⊥] := rfl

theorem first_totalDemand : Profile.totalDemand (first K) = 1 := by
  unfold Profile.totalDemand
  rw [Fin.sum_univ_three]
  change (finrank K (⊤ : Submodule K K) - finrank K (⊤ : Submodule K K)) +
    (finrank K (⊤ : Submodule K K) - finrank K (⊥ : Submodule K K)) +
    (finrank K (⊥ : Submodule K K) - finrank K (⊥ : Submodule K K)) = 1
  simp

theorem second_totalDemand : Profile.totalDemand (second K) = 1 := by
  unfold Profile.totalDemand
  rw [Fin.sum_univ_three]
  change (finrank K (⊤ : Submodule K K) - finrank K (⊥ : Submodule K K)) +
    (finrank K (⊤ : Submodule K K) - finrank K (⊤ : Submodule K K)) +
    (finrank K (⊥ : Submodule K K) - finrank K (⊥ : Submodule K K)) = 1
  simp

theorem condRank_self (P : Submodule K K) : condRank P P = 0 := by
  unfold condRank
  rw [sup_idem]
  exact Nat.sub_self _

theorem condRank_top_bot : condRank (⊤ : Submodule K K) ⊥ = 1 := by
  unfold condRank
  rw [bot_sup_eq]
  simp

theorem first_entry_two : Profile.entry (first K) (.inl 2) = 1 := by
  change (Profile.totalDemand (first K) : ℝ) -
    condRank ((⊤ : Submodule K K) ⊓ ⊤) ⊤ -
    condRank ((⊥ : Submodule K K) ⊓ (⊤ ⊔ ⊤)) ⊥ = 1
  rw [first_totalDemand]
  simp only [top_inf_eq,bot_inf_eq]
  rw [condRank_self, condRank_self]
  norm_num

theorem first_entry_zero : Profile.entry (first K) (.inl 0) = 0 := by
  change (Profile.totalDemand (first K) : ℝ) -
    condRank ((⊤ : Submodule K K) ⊓ ⊤) ⊥ -
    condRank ((⊥ : Submodule K K) ⊓ (⊤ ⊔ ⊤)) ⊥ = 0
  rw [first_totalDemand]
  simp only [top_inf_eq,bot_inf_eq]
  rw [condRank_top_bot, condRank_self]
  norm_num

theorem second_entry_zero : Profile.entry (second K) (.inl 0) = 1 := by
  change (Profile.totalDemand (second K) : ℝ) -
    condRank ((⊤ : Submodule K K) ⊓ ⊤) ⊤ -
    condRank ((⊥ : Submodule K K) ⊓ (⊤ ⊔ ⊤)) ⊥ = 1
  rw [second_totalDemand]
  simp only [top_inf_eq,bot_inf_eq]
  rw [condRank_self, condRank_self]
  norm_num

section Encoders
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A source coefficient list with a verified spanning condition gives an
actual code whose encoder is exactly the stated list evaluation. -/
theorem coefficient_code {n : ℕ} (A U : Three → Submodule K V)
    (v : Fin n → V) (hspan : ∀ i, U i ≤ A i ⊔ Submodule.span K (Set.range v)) :
    ∃ c : ScalarBroadcastCode A U n, c.encode = coefficientBroadcast v := by
  have hk (i : Three) :
      LinearMap.ker ((coefficientBroadcast v).prod (dualObserve (A i))) ≤
        LinearMap.ker (dualObserve (U i)) := by
    intro x hx
    have he : coefficientBroadcast v x = 0 ∧ dualObserve (A i) x = 0 := by
      change (coefficientBroadcast v x,dualObserve (A i) x) = (0,0) at hx
      exact ⟨congrArg Prod.fst hx,congrArg Prod.snd hx⟩
    have hv : Submodule.span K (Set.range v) ≤ LinearMap.ker x := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact congrFun he.1 j
    apply LinearMap.mem_ker.mpr
    ext u
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (hspan i u.property)
    have ha0 := LinearMap.congr_fun he.2 ⟨a,ha⟩
    have hb0 := hv hb
    change x (u : V) = 0
    rw [←hab,map_add]
    exact (congrArg₂ (· + ·) ha0 hb0).trans (zero_add 0)
  choose d hd using fun i => factors_through_of_ker_le
    ((coefficientBroadcast v).prod (dualObserve (A i))) (dualObserve (U i)) (hk i)
  exact ⟨⟨coefficientBroadcast v,d,fun x i => LinearMap.congr_fun (hd i) x⟩,rfl⟩
end Encoders

theorem single_span (i : Three) (A U : Three → Submodule K K) :
    U i ≤ A i ⊔ Submodule.span K (Set.range (fun _ : Fin 1 => (1 : K))) := by
  intro x _
  apply (show Submodule.span K (Set.range (fun _ : Fin 1 => (1 : K))) ≤
    A i ⊔ Submodule.span K (Set.range (fun _ : Fin 1 => (1 : K))) from le_sup_right)
  have h := (Submodule.span K (Set.range (fun _ : Fin 1 => (1 : K)))).smul_mem x
    (Submodule.subset_span (show (1 : K) ∈ Set.range (fun _ : Fin 1 => (1 : K)) from ⟨0,rfl⟩))
  simpa only [smul_eq_mul, mul_one] using h

/-- Both singleton tasks have an actual scalar code that transmits the
one source symbol. -/
theorem singleton_encoders :
    (∃ c : ScalarBroadcastCode (first K).A (first K).U 1,
      ∀ x, c.encode x 0 = x 1) ∧
    (∃ c : ScalarBroadcastCode (second K).A (second K).U 1,
      ∀ x, c.encode x 0 = x 1) := by
  constructor
  · obtain ⟨c,hc⟩ := coefficient_code K (first K).A (first K).U
      (fun _ : Fin 1 => (1 : K)) (fun i => single_span K i _ _)
    exact ⟨c,fun x => by rw [hc]; rfl⟩
  · obtain ⟨c,hc⟩ := coefficient_code K (second K).A (second K).U
      (fun _ : Fin 1 => (1 : K)) (fun i => single_span K i _ _)
    exact ⟨c,fun x => by rw [hc]; rfl⟩

theorem combined_span (i : Three) :
    (combined K).U i ≤ (combined K).A i ⊔
      Submodule.span K (Set.range (fun _ : Fin 1 => ((1 : K),(1 : K)))) := by
  have hd (z : K) : (z,z) ∈ Submodule.span K
      (Set.range (fun _ : Fin 1 => ((1 : K),(1 : K)))) := by
    have hh := (Submodule.span K (Set.range (fun _ : Fin 1 => ((1 : K),(1 : K))))).smul_mem z
      (Submodule.subset_span (show ((1 : K),(1 : K)) ∈ Set.range
        (fun _ : Fin 1 => ((1 : K),(1 : K))) from ⟨0,rfl⟩))
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one] using hh
  fin_cases i
  · intro x _
    refine Submodule.mem_sup.mpr ⟨(x.1-x.2,0),?_,(x.2,x.2),hd x.2,?_⟩
    · change (x.1-x.2 : K) ∈ (⊤ : Submodule K K) ∧ (0 : K) ∈ (⊥ : Submodule K K)
      simp
    · ext <;> simp
  · intro x _
    refine Submodule.mem_sup.mpr ⟨(0,x.2-x.1),?_,(x.1,x.1),hd x.1,?_⟩
    · change (0 : K) ∈ (⊥ : Submodule K K) ∧ (x.2-x.1 : K) ∈ (⊤ : Submodule K K)
      simp
    · ext <;> simp
  · intro x hx
    have hh : x.1 = 0 ∧ x.2 = 0 := hx
    have hz : x = 0 := Prod.ext hh.1 hh.2
    rw [hz]
    exact Submodule.zero_mem _

/-- The encoder is literally x+y, with constructed linear zero-error decoders
for the actual independent direct sum over the original field. -/
theorem sum_encoder : ∃ c : ScalarBroadcastCode (combined K).A (combined K).U 1,
    ∀ x, c.encode x 0 = x (1,0) + x (0,1) := by
  obtain ⟨c,hc⟩ := coefficient_code K (combined K).A (combined K).U
    (fun _ : Fin 1 => ((1 : K),(1 : K))) (combined_span K)
  refine ⟨c,fun x => ?_⟩
  rw [hc]
  change x (1,1) = x (1,0) + x (0,1)
  rw [←map_add]
  congr 1
  ext <;> simp

section Operational
variable [Finite K]

theorem rankBound_le_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) (c : ScalarBroadcastCode T.A T.U 1) :
    Profile.rankBound T ≤ 1 := by
  have hl := c.toBlockOne.rankBound_le_cost T.side_le_signal (by decide : 0 < 1)
  rw [Allocation.rawRankBound_eq_rankBound,c.toBlockOne_cost] at hl
  exact hl.trans (by simpa using scalarBroadcastCode_cost_le c)

theorem first_rankBound : Profile.rankBound (first K) = 1 := by
  obtain ⟨c,_⟩ := (singleton_encoders K).1
  refine le_antisymm (rankBound_le_one K (first K) c) ?_
  rw [←first_entry_two K]
  exact Profile.entry_le_rankBound (first K) _

theorem second_rankBound : Profile.rankBound (second K) = 1 := by
  obtain ⟨c,_⟩ := (singleton_encoders K).2
  refine le_antisymm (rankBound_le_one K (second K) c) ?_
  rw [←second_entry_zero K]
  exact Profile.entry_le_rankBound (second K) _

theorem combined_rankBound : Profile.rankBound (combined K) = 1 := by
  obtain ⟨c,_⟩ := sum_encoder K
  refine le_antisymm (rankBound_le_one K (combined K) c) ?_
  have hh := Profile.entry_le_rankBound (combined K) (.inl 0)
  change Profile.entry (Profile.directSum (first K) (second K)) (.inl 0) ≤ _ at hh
  rw [Profile.entry_directSum,first_entry_zero,second_entry_zero,zero_add] at hh
  exact hh

theorem optima :
    broadcastOptimum (first K).A (first K).U = 1 ∧
    broadcastOptimum (second K).A (second K).U = 1 ∧
    broadcastOptimum (combined K).A (combined K).U = 1 := by
  simp only [task_general_broadcastOptimum_eq_rankBound,
    first_rankBound,second_rankBound,combined_rankBound,and_self]

/-- The same exact cost is attained by every one-symbol scalar code for
these tasks. This is attained-alphabet cost, rather than nominal length. -/
theorem scalar_cost {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) (hT : Profile.rankBound T = 1)
    (c : ScalarBroadcastCode T.A T.U 1) :
    c.toBlockOne.cost = 1 := by
  rw [c.toBlockOne_cost]
  have hn : (1 : ℤ) = ⌈Allocation.rawRankBound T.A T.U⌉ := by
    rw [Allocation.rawRankBound_eq_rankBound,hT]
    norm_num
  simpa using c.cost_eq_ceiling T.side_le_signal hn

/-- Universal nonlinear positive-blocklength lower bound for the example. -/
theorem all_block_lower {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Task K V) (hT : Profile.rankBound T = 1)
    {L : ℕ} {S : Type*} [Finite S] (c : BlockBroadcastCode T.A T.U L S)
    (hL : 0 < L) : 1 ≤ c.cost := by
  have hh := c.rankBound_le_cost T.side_le_signal hL
  rwa [Allocation.rawRankBound_eq_rankBound,hT] at hh

/-- Source-facing certificate: individual and joint operational optima, strict
subadditivity, and the actually attained scalar x+y broadcast. -/
theorem strict_subadditivity_example :
    broadcastOptimum (first K).A (first K).U = 1 ∧
    broadcastOptimum (second K).A (second K).U = 1 ∧
    broadcastOptimum (combined K).A (combined K).U = 1 ∧
    broadcastOptimum (combined K).A (combined K).U <
      broadcastOptimum (first K).A (first K).U + broadcastOptimum (second K).A (second K).U ∧
    ∃ c : ScalarBroadcastCode (combined K).A (combined K).U 1,
      (∀ x, c.encode x 0 = x (1,0) + x (0,1)) ∧ c.toBlockOne.cost = 1 := by
  obtain ⟨h₁,h₂,h₃⟩ := optima K
  obtain ⟨c,hc⟩ := sum_encoder K
  refine ⟨h₁,h₂,h₃,?_,c,hc,scalar_cost K (combined K) (combined_rankBound K) c⟩
  rw [h₁,h₂,h₃]
  norm_num
end Operational

end UploadBroadcast.OppositeDemandExample
