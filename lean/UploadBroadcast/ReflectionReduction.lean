import UploadBroadcast.Structural

/-!
# The dimension-level Coxeter reduction for the inward affine E6 quiver

These are unconditional integral calculations for the sink/source reflection
sequences. They are NOT reflection functors: identifying these transformations
with dimensions of reflected indecomposable representations requires the
kernel/cokernel equivalences and their simple-object exceptions.
-/
namespace UploadBroadcast.ReflectionReduction

@[ext] structure Dimension where
  f : ℤ
  u₁ : ℤ
  u₂ : ℤ
  u₃ : ℤ
  a₁ : ℤ
  a₂ : ℤ
  a₃ : ℤ
  deriving DecidableEq

def defect (x : Dimension) : ℤ :=
  -3*x.f + x.u₁+x.u₂+x.u₃+x.a₁+x.a₂+x.a₃

def tits (x : Dimension) : ℤ :=
  Structural.tits x.f x.u₁ x.u₂ x.u₃ x.a₁ x.a₂ x.a₃

/-- Reflect first the central sink, then the three middle sinks, then the
three outer sinks. The original orientation is restored. -/
def sinkCycle (x : Dimension) : Dimension :=
  let f := x.u₁+x.u₂+x.u₃-x.f
  ⟨f, f+x.a₁-x.u₁, f+x.a₂-x.u₂, f+x.a₃-x.u₃,
    f-x.u₁, f-x.u₂, f-x.u₃⟩

/-- Reverse sequence: the three outer sources, three middle sources, center. -/
def sourceCycle (x : Dimension) : Dimension :=
  ⟨2*x.f-x.a₁-x.a₂-x.a₃, x.f-x.a₁, x.f-x.a₂, x.f-x.a₃,
    x.u₁-x.a₁, x.u₂-x.a₂, x.u₃-x.a₃⟩

def translate (x : Dimension) (n : ℤ) : Dimension :=
  ⟨x.f+3*n, x.u₁+2*n, x.u₂+2*n, x.u₃+2*n,
    x.a₁+n, x.a₂+n, x.a₃+n⟩

theorem source_sink_inverse (x : Dimension) : sourceCycle (sinkCycle x) = x := by
  ext <;> simp [sourceCycle, sinkCycle]
  ring

theorem sink_source_inverse (x : Dimension) : sinkCycle (sourceCycle x) = x := by
  ext <;> simp [sourceCycle, sinkCycle] <;> ring

theorem defect_sinkCycle (x : Dimension) : defect (sinkCycle x) = defect x := by
  simp [defect, sinkCycle]; ring

theorem defect_sourceCycle (x : Dimension) : defect (sourceCycle x) = defect x := by
  simp [defect, sourceCycle]; ring

theorem tits_sinkCycle (x : Dimension) : tits (sinkCycle x) = tits x := by
  simp [tits, Structural.tits, sinkCycle]; ring

theorem tits_sourceCycle (x : Dimension) : tits (sourceCycle x) = tits x := by
  simp [tits, Structural.tits, sourceCycle]; ring

def sixSinks (x : Dimension) : Dimension :=
  sinkCycle (sinkCycle (sinkCycle (sinkCycle (sinkCycle (sinkCycle x)))))

def sixSources (x : Dimension) : Dimension :=
  sourceCycle (sourceCycle (sourceCycle (sourceCycle (sourceCycle (sourceCycle x)))))

set_option maxHeartbeats 2000000 in
/-- Six full sink cycles translate by `defect * delta`. -/
theorem sixSinks_eq (x : Dimension) : sixSinks x = translate x (defect x) := by
  ext <;> simp [sixSinks, sinkCycle, translate, defect] <;> ring

set_option maxHeartbeats 2000000 in
/-- Six full source cycles translate by `-defect * delta`. -/
theorem sixSources_eq (x : Dimension) : sixSources x = translate x (-defect x) := by
  ext <;> simp [sixSources, sourceCycle, translate, defect] <;> ring

lemma defect_translate (x : Dimension) (n : ℤ) : defect (translate x n) = defect x := by
  simp [defect, translate]; ring

def sourceBlocks : ℕ → Dimension → Dimension
  | 0, x => x
  | n+1, x => sixSources (sourceBlocks n x)

def sinkBlocks : ℕ → Dimension → Dimension
  | 0, x => x
  | n+1, x => sixSinks (sinkBlocks n x)

theorem sourceBlocks_eq (n : ℕ) (x : Dimension) :
    sourceBlocks n x = translate x (-(n : ℤ)*defect x) := by
  induction n with
  | zero => ext <;> simp [sourceBlocks, translate]
  | succ n ih =>
    rw [sourceBlocks, sixSources_eq, ih, defect_translate]
    ext <;> simp [translate, Nat.cast_add, Nat.cast_one] <;> ring

theorem sinkBlocks_eq (n : ℕ) (x : Dimension) :
    sinkBlocks n x = translate x ((n : ℤ)*defect x) := by
  induction n with
  | zero => ext <;> simp [sinkBlocks, translate]
  | succ n ih =>
    rw [sinkBlocks, sixSinks_eq, ih, defect_translate]
    ext <;> simp [translate, Nat.cast_add, Nat.cast_one] <;> ring

/-- Positive defect prevents an infinite sequence of genuine source-reflected
representations with these dimensions: eventually the central dimension is
negative. A reflection-functor proof must therefore reach a simple exception. -/
theorem positive_defect_terminates (x : Dimension) (h : 0 < defect x) :
    ∃ n : ℕ, (sourceBlocks n x).f < 0 := by
  refine ⟨x.f.natAbs + 1, ?_⟩
  rw [sourceBlocks_eq]
  simp only [translate, Nat.cast_add, Nat.cast_one]
  have ha : x.f ≤ (x.f.natAbs : ℤ) := Int.le_natAbs
  have hn : 0 ≤ (x.f.natAbs : ℤ) := Int.natCast_nonneg _
  have hp : 1 ≤ defect x := h
  nlinarith

/-- The dual termination statement for negative defect. -/
theorem negative_defect_terminates (x : Dimension) (h : defect x < 0) :
    ∃ n : ℕ, (sinkBlocks n x).f < 0 := by
  refine ⟨x.f.natAbs + 1, ?_⟩
  rw [sinkBlocks_eq]
  simp only [translate, Nat.cast_add, Nat.cast_one]
  have ha : x.f ≤ (x.f.natAbs : ℤ) := Int.le_natAbs
  have hn : 0 ≤ (x.f.natAbs : ℤ) := Int.natCast_nonneg _
  have hp : defect x ≤ -1 := by omega
  nlinarith

/-- Zero defect is a real obstruction to using this termination argument. -/
theorem zero_defect_periodic (x : Dimension) (h : defect x = 0) :
    sixSinks x = x ∧ sixSources x = x := by
  rw [sixSinks_eq, sixSources_eq, h]
  constructor <;> ext <;> simp [translate]

/-- The manuscript's resonant family has positive excess but zero defect. -/
theorem resonant_family (n : ℤ) :
    let x : Dimension := ⟨3*n+2, 2*n+1, 2*n+1, 2*n+1, n+1, n+1, n+1⟩
    defect x = 0 ∧ tits x = 1 ∧
      Structural.excess x.f x.a₁ x.a₂ x.a₃ = 1 := by
  dsimp [defect, tits, Structural.tits, Structural.excess]
  constructor
  · ring
  constructor <;> ring

end UploadBroadcast.ReflectionReduction
