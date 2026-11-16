import UploadBroadcast.Allocation

/-! The exact change of variables between the numerical LCBC allocation
LP and its waterfilling problem. Rank monotonicity is stated explicitly;
no equality of the two optima is assumed. -/
namespace UploadBroadcast.Allocation

/-- The five-variable allocation constraints (λ123,λ23,λ13,λ12,λal). -/
def LCBCFeasible (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ t x y z a : ℝ) : Prop :=
  0 ≤ t ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ a ∧ t ≤ r ∧
  t+x ≤ u₁ ∧ t+y ≤ u₂ ∧ t+z ≤ u₃ ∧
  t+y+z ≤ p₁ ∧ t+x+z ≤ p₂ ∧ t+x+y ≤ p₃ ∧
  t+y+z+a ≤ b₁ ∧ t+x+z+a ≤ b₂ ∧ t+x+y+a ≤ b₃

/-- Elementary monotonicity inequalities obeyed by the conditional ranks:
common ≤ pair ≤ incident pair-sum ≤ enlarged intersection. -/
def RankBounds (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ u₁ ∧ r ≤ u₂ ∧ r ≤ u₃ ∧
  u₂ ≤ p₁ ∧ u₃ ≤ p₁ ∧ u₁ ≤ p₂ ∧ u₃ ≤ p₂ ∧
  u₁ ≤ p₃ ∧ u₂ ≤ p₃ ∧ p₁ ≤ b₁ ∧ p₂ ≤ b₂ ∧ p₃ ≤ b₃

/-- Every feasible five-variable allocation is dominated by a point in
the fixed-common-allocation waterfilling polyhedron. -/
theorem lcbc_to_waterfill
    {r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ t x y z a : ℝ}
    (hrank : RankBounds r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃)
    (hf : LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ t x y z a) :
    ∃ X Y Z, WaterFeasible (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) X Y Z ∧
      2*t+x+y+z+a ≤ r+waterLevel b₁ b₂ b₃ X Y Z := by
  rcases hrank with ⟨hr,hr₁,hr₂,hr₃,h₂₁,h₃₁,h₁₂,h₃₂,h₁₃,h₂₃,hb₁,hb₂,hb₃⟩
  rcases hf with ⟨ht,hx,hy,hz,ha,htr,hu₁,hu₂,hu₃,hp₁,hp₂,hp₃,ha₁,ha₂,ha₃⟩
  let X := max 0 (x-(r-t))
  let Y := max 0 (y-(r-t))
  let Z := max 0 (z-(r-t))
  have hX : 0 ≤ X := le_max_left _ _
  have hY : 0 ≤ Y := le_max_left _ _
  have hZ : 0 ≤ Z := le_max_left _ _
  have hXu : X ≤ u₁-r := by dsimp [X]; rw [max_le_iff]; constructor <;> linarith
  have hYu : Y ≤ u₂-r := by dsimp [Y]; rw [max_le_iff]; constructor <;> linarith
  have hZu : Z ≤ u₃-r := by dsimp [Z]; rw [max_le_iff]; constructor <;> linarith
  have hYZ : Y+Z ≤ p₁-r := by
    dsimp [Y,Z]; simp only [max_def]; split_ifs <;> linarith
  have hXZ : X+Z ≤ p₂-r := by
    dsimp [X,Z]; simp only [max_def]; split_ifs <;> linarith
  have hXY : X+Y ≤ p₃-r := by
    dsimp [X,Y]; simp only [max_def]; split_ifs <;> linarith
  refine ⟨X,Y,Z,⟨hX,hY,hZ,hXu,hYu,hZu,hYZ,hXZ,hXY⟩,?_⟩
  have hlX : x-(r-t) ≤ X := le_max_right _ _
  have hlY : y-(r-t) ≤ Y := le_max_right _ _
  have hlZ : z-(r-t) ≤ Z := le_max_right _ _
  have hlevel : 2*t+x+y+z+a-r ≤ waterLevel b₁ b₂ b₃ X Y Z := by
    unfold waterLevel
    apply le_min
    · linarith
    · apply le_min <;> linarith
  linarith

/-- Every waterfilling point gives a feasible allocation with λ123=r,
whose objective is exactly r plus the water level. -/
theorem waterfill_to_lcbc
    {r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ X Y Z : ℝ}
    (hrank : RankBounds r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃)
    (hf : WaterFeasible (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) X Y Z) :
    ∃ a, LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ r X Y Z a ∧
      2*r+X+Y+Z+a = r+waterLevel b₁ b₂ b₃ X Y Z := by
  rcases hrank with ⟨hr,hr₁,hr₂,hr₃,h₂₁,h₃₁,h₁₂,h₃₂,h₁₃,h₂₃,hb₁,hb₂,hb₃⟩
  rcases hf with ⟨hX,hY,hZ,hu₁,hu₂,hu₃,hp₁,hp₂,hp₃⟩
  let a := min (b₁-Y-Z) (min (b₂-X-Z) (b₃-X-Y))-r
  have ha : 0 ≤ a := by
    dsimp [a]
    have h : r ≤ min (b₁-Y-Z) (min (b₂-X-Z) (b₃-X-Y)) := by
      apply le_min
      · linarith
      · apply le_min <;> linarith
    linarith
  have ha₁ : r+Y+Z+a ≤ b₁ := by
    have := min_le_left (b₁-Y-Z) (min (b₂-X-Z) (b₃-X-Y)); dsimp [a]; linarith
  have ha₂ : r+X+Z+a ≤ b₂ := by
    have := le_trans (min_le_right (b₁-Y-Z) (min (b₂-X-Z) (b₃-X-Y))) (min_le_left _ _)
    dsimp [a]; linarith
  have ha₃ : r+X+Y+a ≤ b₃ := by
    have := le_trans (min_le_right (b₁-Y-Z) (min (b₂-X-Z) (b₃-X-Y))) (min_le_right _ _)
    dsimp [a]; linarith
  refine ⟨a,⟨hr,hX,hY,hZ,ha,le_refl r,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,ha₁,ha₂,ha₃⟩,?_⟩
  dsimp [a,waterLevel]
  simp only [min_def]
  split_ifs <;> linarith

/-- Numerical equivalence of the allocation and waterfilling optima,
including attainment with the common allocation saturated. -/
theorem lcbc_waterfill_optimum
    {r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ X Y Z : ℝ}
    (hrank : RankBounds r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃)
    (hf : WaterFeasible (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) X Y Z)
    (hopt : ∀ x y z,
      WaterFeasible (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) x y z →
      waterLevel b₁ b₂ b₃ x y z ≤ waterLevel b₁ b₂ b₃ X Y Z) :
    ∃ a, LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ r X Y Z a ∧
      2*r+X+Y+Z+a = r+waterLevel b₁ b₂ b₃ X Y Z ∧
      ∀ t x y z a', LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ t x y z a' →
        2*t+x+y+z+a' ≤ 2*r+X+Y+Z+a := by
  obtain ⟨a,ha,he⟩ := waterfill_to_lcbc hrank hf
  refine ⟨a,ha,he,?_⟩
  intro t x y z a' hF
  obtain ⟨x',y',z',hW,hbound⟩ := lcbc_to_waterfill hrank hF
  have := hopt x' y' z' hW
  linarith

/-- The upper bound on a common water level imposed by one pair. -/
noncomputable def pairLevel (b c p : ℝ) : ℝ :=
  min (b+p) (min (c+p) ((b+c+p)/2))

noncomputable def waterfillValue (u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ : ℝ) : ℝ :=
  min (b₁+u₁) (min (b₂+u₂) (min (b₃+u₃)
    (min (pairLevel b₂ b₃ p₁) (min (pairLevel b₁ b₃ p₂) (pairLevel b₁ b₂ p₃)))))

theorem pairLevel_upper {h b c p y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hp : y+z ≤ p)
    (hb : h ≤ b+y) (hc : h ≤ c+z) : h ≤ pairLevel b c p := by
  unfold pairLevel
  apply le_min
  · linarith
  · apply le_min <;> linarith

theorem pairLevel_fill {h b c p : ℝ} (hp : 0 ≤ p)
    (hh : h ≤ pairLevel b c p) :
    max 0 (h-b) + max 0 (h-c) ≤ p := by
  unfold pairLevel at hh
  rw [le_min_iff,le_min_iff] at hh
  rcases hh with ⟨h₁,h₂,h₃⟩
  simp only [max_def]
  split_ifs <;> linarith

theorem waterfillValue_upper {u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ x y z : ℝ}
    (hf : WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x y z) :
    waterLevel b₁ b₂ b₃ x y z ≤ waterfillValue u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ := by
  rcases hf with ⟨hx,hy,hz,hu₁,hu₂,hu₃,hp₁,hp₂,hp₃⟩
  have h₁ : waterLevel b₁ b₂ b₃ x y z ≤ b₁+x := min_le_left _ _
  have h₂ : waterLevel b₁ b₂ b₃ x y z ≤ b₂+y :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have h₃ : waterLevel b₁ b₂ b₃ x y z ≤ b₃+z :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  unfold waterfillValue
  simp only [le_min_iff]
  exact ⟨by linarith,by linarith,by linarith,
    pairLevel_upper hy hz hp₁ h₂ h₃,
    pairLevel_upper hx hz hp₂ h₁ h₃,
    pairLevel_upper hx hy hp₃ h₁ h₂⟩

/-- Explicit attainment, avoiding a compactness or pre-existing-optimizer
assumption. All six upper bounds must be nonnegative, exactly when zero
belongs to this downward-closed polyhedron. -/
theorem waterfillValue_attained (u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ : ℝ)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hu₃ : 0 ≤ u₃)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) :
    ∃ x y z, WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x y z ∧
      waterLevel b₁ b₂ b₃ x y z = waterfillValue u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ := by
  let h := waterfillValue u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃
  have hh : h ≤ waterfillValue u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ := le_refl _
  unfold waterfillValue at hh
  simp only [le_min_iff] at hh
  rcases hh with ⟨h₁,h₂,h₃,hp₁',hp₂',hp₃'⟩
  let x := max 0 (h-b₁)
  let y := max 0 (h-b₂)
  let z := max 0 (h-b₃)
  have hf : WaterFeasible u₁ u₂ u₃ p₁ p₂ p₃ x y z := by
    refine ⟨le_max_left _ _,le_max_left _ _,le_max_left _ _,?_,?_,?_,
      pairLevel_fill hp₁ hp₁',pairLevel_fill hp₂ hp₂',pairLevel_fill hp₃ hp₃'⟩
    · dsimp [x]; rw [max_le_iff]; exact ⟨hu₁,by linarith⟩
    · dsimp [y]; rw [max_le_iff]; exact ⟨hu₂,by linarith⟩
    · dsimp [z]; rw [max_le_iff]; exact ⟨hu₃,by linarith⟩
  refine ⟨x,y,z,hf,le_antisymm (waterfillValue_upper hf) ?_⟩
  have hx : h-b₁ ≤ x := le_max_right _ _
  have hy : h-b₂ ≤ y := le_max_right _ _
  have hz : h-b₃ ≤ z := le_max_right _ _
  change h ≤ waterLevel b₁ b₂ b₃ x y z
  unfold waterLevel
  apply le_min
  · linarith
  · apply le_min <;> linarith

/-- Exact minimum of the numerical broadcast-length LP. -/
noncomputable def lcbcCostValue
    (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m : ℝ) : ℝ :=
  m-r-waterfillValue (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) b₁ b₂ b₃

/-- Full optimizer existence and optimality for the real allocation LP.
Only the elementary rank-order inequalities are assumed. -/
theorem lcbc_cost_optimum
    (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m : ℝ)
    (hrank : RankBounds r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃) :
    (∃ x y z a, LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ r x y z a ∧
      m-2*r-x-y-z-a = lcbcCostValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m) ∧
    (∀ t x y z a, LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ t x y z a →
      lcbcCostValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m ≤ m-2*t-x-y-z-a) := by
  have hrank' := hrank
  rcases hrank' with ⟨hr,hr₁,hr₂,hr₃,h₂₁,h₃₁,h₁₂,h₃₂,h₁₃,h₂₃,hb₁,hb₂,hb₃⟩
  obtain ⟨x,y,z,hf,he⟩ := waterfillValue_attained
    (u₁-r) (u₂-r) (u₃-r) (p₁-r) (p₂-r) (p₃-r) b₁ b₂ b₃
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨a,ha,he',hopt⟩ := lcbc_waterfill_optimum hrank hf
    (fun x' y' z' h' => le_trans (waterfillValue_upper h') (le_of_eq he.symm))
  constructor
  · refine ⟨x,y,z,a,ha,?_⟩
    unfold lcbcCostValue
    linarith
  · intro t x' y' z' a' h'
    have := hopt t x' y' z' a' h'
    unfold lcbcCostValue
    linarith

/-- Integer LCBC allocation at the ceiling of the real LP optimum.
Unlike the intermediate rounding lemma, this result assumes no optimizer
and no waterfilling identity. Those are proved above. -/
theorem integer_lcbc_cost_ceiling
    (r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m₁ m₂ m₃ : ℤ)
    (hrank : RankBounds r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃)
    (hm₁ : b₁ ≤ m₁) (hm₂ : b₂ ≤ m₂) (hm₃ : b₃ ≤ m₃) :
    ∃ X Y Z a : ℤ,
      LCBCFeasible r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ r X Y Z a ∧
      0 ≤ m₁-r-Y-Z-a ∧ 0 ≤ m₂-r-X-Z-a ∧ 0 ≤ m₃-r-X-Y-a ∧
      m₁+m₂+m₃-2*r-X-Y-Z-a =
        ⌈lcbcCostValue r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ (m₁+m₂+m₃)⌉ := by
  have hrank' := hrank
  rcases hrank' with ⟨hr,hr₁,hr₂,hr₃,h₂₁,h₃₁,h₁₂,h₃₂,h₁₃,h₂₃,hb₁,hb₂,hb₃⟩
  obtain ⟨x,y,z,hf,he⟩ := waterfillValue_attained
    ((u₁:ℝ)-r) ((u₂:ℝ)-r) ((u₃:ℝ)-r) ((p₁:ℝ)-r) ((p₂:ℝ)-r) ((p₃:ℝ)-r) b₁ b₂ b₃
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hopt : ∀ x' y' z', WaterFeasible ((u₁:ℝ)-r) ((u₂:ℝ)-r) ((u₃:ℝ)-r)
      ((p₁:ℝ)-r) ((p₂:ℝ)-r) ((p₃:ℝ)-r) x' y' z' →
      waterLevel b₁ b₂ b₃ x' y' z' ≤ waterLevel b₁ b₂ b₃ x y z := by
    intro x' y' z' h'
    exact le_trans (waterfillValue_upper h') (le_of_eq he.symm)
  obtain ⟨X,Y,Z,a,hR,hX,hY,hZ,hA,hU₁,hU₂,hU₃,hP₁,hP₂,hP₃,hA₁,hA₂,hA₃,hM₁,hM₂,hM₃,hcost⟩ :=
    integer_lcbc_allocation r u₁ u₂ u₃ p₁ p₂ p₃ b₁ b₂ b₃ m₁ m₂ m₃
      (by exact_mod_cast hr) (by exact_mod_cast hb₁) (by exact_mod_cast hb₂)
      (by exact_mod_cast hb₃) hm₁ hm₂ hm₃ x y z hf hopt
  refine ⟨X,Y,Z,a,?_,hM₁,hM₂,hM₃,?_⟩
  · unfold LCBCFeasible
    exact_mod_cast (show (0 ≤ r ∧ 0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ Z ∧ 0 ≤ a ∧ r ≤ r ∧
      r+X ≤ u₁ ∧ r+Y ≤ u₂ ∧ r+Z ≤ u₃ ∧ r+Y+Z ≤ p₁ ∧ r+X+Z ≤ p₂ ∧
      r+X+Y ≤ p₃ ∧ r+Y+Z+a ≤ b₁ ∧ r+X+Z+a ≤ b₂ ∧ r+X+Y+a ≤ b₃) from
      ⟨hR,hX,hY,hZ,hA,le_refl r,hU₁,hU₂,hU₃,hP₁,hP₂,hP₃,hA₁,hA₂,hA₃⟩)
  · rw [he] at hcost
    unfold lcbcCostValue
    convert hcost using 1; push_cast; ring

end UploadBroadcast.Allocation
