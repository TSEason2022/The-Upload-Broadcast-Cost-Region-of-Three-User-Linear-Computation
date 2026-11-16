import UploadBroadcast.SourceHomVanishing
import UploadBroadcast.QuiverTits

/-!
# Reflection certificates for excluding an enlarged tripod

The fixed T1 representation has dimension (2;2,1,1;1,1,1). Four source
cycles take this dimension to the simple at outer arm zero, while the resonant
regular dimension returns to itself. The actual Hom-vanishing consequence is
proved using the no-simple-prefix reflection transport, separately from these
integer calculations.
-/
namespace UploadBroadcast.ResonantTripodTransversality
open QuiverRepresentation E6Reflection

def tripodEnlargement : ReflectionReduction.Dimension := ⟨2,2,1,1,1,1,1⟩

def regular (n : ℕ) : E6Vertex → ℤ :=
  encode ⟨3*n+2,2*n+1,2*n+1,2*n+1,n+1,n+1,n+1⟩

def regularPartner (n : ℕ) : E6Vertex → ℤ :=
  encode ⟨3*n+1,2*n+1,2*n+1,2*n+1,n,n,n⟩

theorem source_regular (n : ℕ) : sourceWord.action (regular n) = regularPartner n := by
  rw [sourceWord_action]
  funext v
  cases v with
  | center => simp [regular,regularPartner,encode,vector,ReflectionReduction.sourceCycle]; ring
  | middle i => fin_cases i <;> simp [regular,regularPartner,encode,vector,ReflectionReduction.sourceCycle] <;> ring
  | outer i => fin_cases i <;> simp [regular,regularPartner,encode,vector,ReflectionReduction.sourceCycle] <;> ring

theorem source_regularPartner (n : ℕ) : sourceWord.action (regularPartner n) = regular n := by
  rw [sourceWord_action]
  funext v
  cases v with
  | center => simp [regular,regularPartner,encode,vector,ReflectionReduction.sourceCycle]; ring
  | middle i => fin_cases i <;> simp [regular,regularPartner,encode,vector,ReflectionReduction.sourceCycle] <;> ring
  | outer i => fin_cases i <;> simp [regular,regularPartner,encode,vector,ReflectionReduction.sourceCycle] <;> ring

theorem four_source_regular (n : ℕ) : (sourceWord.power 4).action (regular n) = regular n := by
  simp only [SourceWord.power,SourceWord.action_append,SourceWord.action,
    source_regular,source_regularPartner]

theorem four_source_tripodEnlargement :
    (sourceWord.power 4).action (encode tripodEnlargement) =
      fun v => if v = E6Vertex.outer 0 then 1 else 0 := by
  simp only [SourceWord.power,SourceWord.action_append,SourceWord.action,sourceWord_action,
    vector_encode]
  funext v
  cases v with
  | center => norm_num [tripodEnlargement,ReflectionReduction.sourceCycle,encode]; decide
  | middle i => fin_cases i <;> norm_num [tripodEnlargement,ReflectionReduction.sourceCycle,encode] <;> decide
  | outer i => fin_cases i <;> norm_num [tripodEnlargement,ReflectionReduction.sourceCycle,encode]

theorem sourceWord_nonsimple_numeric (d : E6Vertex → ℤ) :
    sourceWord.NonSimpleDims d ↔
      (∃ v : E6Vertex, v ≠ (.outer 0) ∧ (d) v ≠ 0) ∧
      (∃ v : E6Vertex, v ≠ (.outer 1) ∧ (sourceDimension P0 (.outer 0) (d)) v ≠ 0) ∧
      (∃ v : E6Vertex, v ≠ (.outer 2) ∧ (sourceDimension P1 (.outer 1) (sourceDimension P0 (.outer 0) (d))) v ≠ 0) ∧
      (∃ v : E6Vertex, v ≠ (.middle 0) ∧ (sourceDimension P2 (.outer 2) (sourceDimension P1 (.outer 1) (sourceDimension P0 (.outer 0) (d)))) v ≠ 0) ∧
      (∃ v : E6Vertex, v ≠ (.middle 1) ∧ (sourceDimension P3 (.middle 0) (sourceDimension P2 (.outer 2) (sourceDimension P1 (.outer 1) (sourceDimension P0 (.outer 0) (d))))) v ≠ 0) ∧
      (∃ v : E6Vertex, v ≠ (.middle 2) ∧ (sourceDimension P4 (.middle 1) (sourceDimension P3 (.middle 0) (sourceDimension P2 (.outer 2) (sourceDimension P1 (.outer 1) (sourceDimension P0 (.outer 0) (d)))))) v ≠ 0) ∧
      (∃ v : E6Vertex, v ≠ (.center) ∧ (sourceDimension P5 (.middle 2) (sourceDimension P4 (.middle 1) (sourceDimension P3 (.middle 0) (sourceDimension P2 (.outer 2) (sourceDimension P1 (.outer 1) (sourceDimension P0 (.outer 0) (d))))))) v ≠ 0) ∧
      True := by
  simp only [sourceWord,SourceWord.nonSimpleDims_castTarget,sourceWordRaw,SourceWord.NonSimpleDims]
  rfl

theorem source_regular_nonsimple (n : ℕ) : sourceWord.NonSimpleDims (regular n) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,
    ⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 1,(by intro he; cases he),?_⟩,
    ⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,
    ⟨.middle 0,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    simp [regular,encode,reflectDimension,neighbourSum] <;> omega

theorem source_regularPartner_nonsimple (n : ℕ) : sourceWord.NonSimpleDims (regularPartner n) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,
    ⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 1,(by intro he; cases he),?_⟩,
    ⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,
    ⟨.middle 0,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    simp [regularPartner,encode,reflectDimension,neighbourSum] <;> omega

theorem four_source_regular_nonsimple (n : ℕ) :
    (sourceWord.power 4).NonSimpleDims (regular n) := by
  simp only [SourceWord.power,SourceWord.nonSimpleDims_append,SourceWord.NonSimpleDims,
    SourceWord.action_append,SourceWord.action,source_regular,source_regularPartner]
  exact ⟨⟨⟨⟨True.intro,source_regular_nonsimple n⟩,source_regularPartner_nonsimple n⟩,
    source_regular_nonsimple n⟩,source_regularPartner_nonsimple n⟩

private theorem tripod_cycle_0_nonsimple :
    sourceWord.NonSimpleDims (encode (⟨2,2,1,1,1,1,1⟩ : ReflectionReduction.Dimension)) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    decide

private theorem tripod_cycle_1_nonsimple :
    sourceWord.NonSimpleDims (encode (⟨1,1,1,1,1,0,0⟩ : ReflectionReduction.Dimension)) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.middle 1,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    decide

private theorem tripod_cycle_2_nonsimple :
    sourceWord.NonSimpleDims (encode (⟨1,0,1,1,0,1,1⟩ : ReflectionReduction.Dimension)) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    decide

private theorem tripod_cycle_3_nonsimple :
    sourceWord.NonSimpleDims (encode (⟨0,1,0,0,0,0,0⟩ : ReflectionReduction.Dimension)) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,⟨.outer 0,(by intro he; cases he),?_⟩,⟨.outer 0,(by intro he; cases he),?_⟩,⟨.outer 0,(by intro he; cases he),?_⟩,⟨.outer 0,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    decide

theorem four_source_tripodEnlargement_nonsimple :
    (sourceWord.power 4).NonSimpleDims (encode tripodEnlargement) := by
  simp only [SourceWord.power,SourceWord.nonSimpleDims_append,SourceWord.NonSimpleDims,
    SourceWord.action_append,SourceWord.action,sourceWord_action,vector_encode]
  refine ⟨⟨⟨⟨True.intro,tripod_cycle_0_nonsimple⟩,?_⟩,?_⟩,?_⟩
  · exact tripod_cycle_1_nonsimple
  · exact tripod_cycle_2_nonsimple
  · exact tripod_cycle_3_nonsimple

/-- Actual Hom vanishing, obtained by transporting through all 28 admissible
source reflections. No regular-tube classification is assumed. -/
theorem tripodEnlargement_hom_zero {K : Type} [Field K]
    (R S : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S)
    (hRD : dimension R = encode tripodEnlargement)
    (n : ℕ) (hSD : dimension S = regular n) (f : Hom R S) : f = Hom.zero R S := by
  let w := sourceWord.power 4
  have hr := w.valid_of_dims R hR (by rw [hRD]; exact four_source_tripodEnlargement_nonsimple)
  have hs := w.valid_of_dims S hS (by rw [hSD]; exact four_source_regular_nonsimple n)
  have hdR : dimension (w.run R) = fun v => if v = E6Vertex.outer 0 then 1 else 0 := by
    rw [hr.2.2,hRD]
    exact four_source_tripodEnlargement
  have hdS : dimension (w.run S) = regular n := by
    rw [hs.2.2,hSD]
    exact four_source_regular n
  have hp : SupportedAt (w.run R) (.outer 0) := by
    intro v hv x
    have he := congrFun hdR v
    rw [if_neg hv] at he
    have hdim : Module.finrank K ((w.run R).space v) = 0 := by
      change (Module.finrank K ((w.run R).space v) : ℤ) = 0 at he
      exact_mod_cast he
    haveI : Subsingleton ((w.run R).space v) := Module.finrank_zero_iff.mp hdim
    exact Subsingleton.elim x 0
  have hc : Nontrivial ((w.run S).space .center) := by
    rcases subsingleton_or_nontrivial ((w.run S).space .center) with h | h
    · letI := h
      have he := congrFun hdS .center
      simp [dimension,regular,encode,Module.finrank_zero_of_subsingleton] at he
      omega
    · exact h
  letI := hc
  have hout := sourceOutgoing_injective (w.run S) source0 hs.2.1 E6Vertex.center (by intro he; cases he)
  exact w.hom_zero_of_terminal R S hr.1 hs.1 source0 hp hout f

/-- Tripod enlargement on an arbitrary arm. -/
def tripodEnlargementAt (i : Fin 3) : ReflectionReduction.Dimension :=
  ⟨2,1+(if i=0 then 1 else 0),1+(if i=1 then 1 else 0),1+(if i=2 then 1 else 0),1,1,1⟩

theorem four_source_tripodEnlargementAt (i : Fin 3) :
    (sourceWord.power 4).action (encode (tripodEnlargementAt i)) =
      fun v => if v = E6Vertex.outer i then 1 else 0 := by
  simp only [SourceWord.power,SourceWord.action_append,SourceWord.action,sourceWord_action,
    vector_encode]
  fin_cases i <;> funext v
  all_goals cases v with
    | center => decide
    | middle j => fin_cases j <;> decide
    | outer j => fin_cases j <;> decide

private theorem tripodAt_cycle_0_nonsimple (i : Fin 3) :
    sourceWord.NonSimpleDims (encode ((ReflectionReduction.sourceCycle^[0]) (tripodEnlargementAt i))) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.middle 0,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    fin_cases i <;> decide

private theorem tripodAt_cycle_1_nonsimple (i : Fin 3) :
    sourceWord.NonSimpleDims (encode ((ReflectionReduction.sourceCycle^[1]) (tripodEnlargementAt i))) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.middle (i+1),(by intro he; cases he),?_⟩,True.intro⟩ <;>
    fin_cases i <;> decide

private theorem tripodAt_cycle_2_nonsimple (i : Fin 3) :
    sourceWord.NonSimpleDims (encode ((ReflectionReduction.sourceCycle^[2]) (tripodEnlargementAt i))) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.center,(by intro he; cases he),?_⟩,⟨.middle i,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    fin_cases i <;> decide

private theorem tripodAt_cycle_3_nonsimple (i : Fin 3) :
    sourceWord.NonSimpleDims (encode ((ReflectionReduction.sourceCycle^[3]) (tripodEnlargementAt i))) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  refine ⟨⟨.middle i,(by intro he; cases he),?_⟩,⟨.middle i,(by intro he; cases he),?_⟩,⟨.middle i,(by intro he; cases he),?_⟩,⟨.outer i,(by intro he; cases he),?_⟩,⟨.outer i,(by intro he; cases he),?_⟩,⟨.outer i,(by intro he; cases he),?_⟩,⟨.outer i,(by intro he; cases he),?_⟩,True.intro⟩ <;>
    fin_cases i <;> decide

theorem four_source_tripodEnlargementAt_nonsimple (i : Fin 3) :
    (sourceWord.power 4).NonSimpleDims (encode (tripodEnlargementAt i)) := by
  simp only [SourceWord.power,SourceWord.nonSimpleDims_append,SourceWord.NonSimpleDims,
    SourceWord.action_append,SourceWord.action,sourceWord_action,vector_encode]
  exact ⟨⟨⟨⟨True.intro,tripodAt_cycle_0_nonsimple i⟩,tripodAt_cycle_1_nonsimple i⟩,
    tripodAt_cycle_2_nonsimple i⟩,tripodAt_cycle_3_nonsimple i⟩

theorem tripodEnlargementAt_hom_zero {K : Type} [Field K]
    (i : Fin 3) (R S : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S)
    (hRD : dimension R = encode (tripodEnlargementAt i))
    (n : ℕ) (hSD : dimension S = regular n) (f : Hom R S) : f = Hom.zero R S := by
  let w := sourceWord.power 4
  have hr := w.valid_of_dims R hR (by rw [hRD]; exact four_source_tripodEnlargementAt_nonsimple i)
  have hs := w.valid_of_dims S hS (by rw [hSD]; exact four_source_regular_nonsimple n)
  have hdR : dimension (w.run R) = fun v => if v = E6Vertex.outer i then 1 else 0 := by
    rw [hr.2.2,hRD]
    exact four_source_tripodEnlargementAt i
  have hdS : dimension (w.run S) = regular n := by
    rw [hs.2.2,hSD]
    exact four_source_regular n
  have hp : SupportedAt (w.run R) (.outer i) := by
    intro v hv x
    have he := congrFun hdR v
    rw [if_neg hv] at he
    have hdim : Module.finrank K ((w.run R).space v) = 0 := by
      change (Module.finrank K ((w.run R).space v) : ℤ) = 0 at he
      exact_mod_cast he
    haveI : Subsingleton ((w.run R).space v) := Module.finrank_zero_iff.mp hdim
    exact Subsingleton.elim x 0
  have hc : Nontrivial ((w.run S).space .center) := by
    rcases subsingleton_or_nontrivial ((w.run S).space .center) with h | h
    · letI := h
      have he := congrFun hdS .center
      simp [dimension,regular,encode,Module.finrank_zero_of_subsingleton] at he
      omega
    · exact h
  letI := hc
  have hsource : inwardE6.IsSource (.outer i) := by intro e; cases e <;> intro he <;> cases he
  have hout := sourceOutgoing_injective (w.run S) hsource hs.2.1 E6Vertex.center (by intro he; cases he)
  exact w.hom_zero_of_terminal R S hr.1 hs.1 hsource hp hout f

@[simp] private theorem center_ne_middle (j : Fin 3) : (E6Vertex.center) ≠ (E6Vertex.middle j) := by intro h; cases h
@[simp] private theorem center_ne_outer (j : Fin 3) : (E6Vertex.center) ≠ (E6Vertex.outer j) := by intro h; cases h
@[simp] private theorem middle_ne_center (i : Fin 3) : (E6Vertex.middle i) ≠ (E6Vertex.center) := by intro h; cases h
@[simp] private theorem middle_ne_outer (i : Fin 3) (j : Fin 3) : (E6Vertex.middle i) ≠ (E6Vertex.outer j) := by intro h; cases h
@[simp] private theorem outer_ne_center (i : Fin 3) : (E6Vertex.outer i) ≠ (E6Vertex.center) := by intro h; cases h
@[simp] private theorem outer_ne_middle (i : Fin 3) (j : Fin 3) : (E6Vertex.outer i) ≠ (E6Vertex.middle j) := by intro h; cases h

@[simp] private theorem fin_0_ne_1 : (0 : Fin 3) ≠ 1 := by decide
@[simp] private theorem fin_0_ne_2 : (0 : Fin 3) ≠ 2 := by decide
@[simp] private theorem fin_1_ne_0 : (1 : Fin 3) ≠ 0 := by decide
@[simp] private theorem fin_1_ne_2 : (1 : Fin 3) ≠ 2 := by decide
@[simp] private theorem fin_2_ne_0 : (2 : Fin 3) ≠ 0 := by decide
@[simp] private theorem fin_2_ne_1 : (2 : Fin 3) ≠ 1 := by decide
@[simp] private theorem triple_two (a b c : ℤ) : (![a,b,c] : Fin 3 → ℤ) 2 = c := rfl

/-- Pure dimension certificate for an arbitrary nonzero zero-defect vector.
No real-root or resonant-family dimension is assumed. -/
theorem source_zero_defect_nonsimple (x : ReflectionReduction.Dimension)
    (hdef : ReflectionReduction.defect x = 0) (hne : encode x ≠ fun _ => 0) :
    sourceWord.NonSimpleDims (encode x) := by
  rw [sourceWord_nonsimple_numeric]
  rw [sourceDimension0,sourceDimension1,sourceDimension2,sourceDimension3,sourceDimension4,sourceDimension5]
  dsimp only [ReflectionReduction.defect] at hdef
  refine ⟨?_,?_,?_,?_,?_,?_,?_,True.intro⟩
  · by_contra hn
    push_neg at hn
    have h0 := hn (.center) (by decide)
    have h1 := hn (.middle 0) (by decide)
    have h2 := hn (.middle 1) (by decide)
    have h3 := hn (.middle 2) (by decide)
    have h5 := hn (.outer 1) (by decide)
    have h6 := hn (.outer 2) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h0 h1 h2 h3 h5 h6
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith
  · by_contra hn
    push_neg at hn
    have h0 := hn (.center) (by decide)
    have h1 := hn (.middle 0) (by decide)
    have h2 := hn (.middle 1) (by decide)
    have h3 := hn (.middle 2) (by decide)
    have h4 := hn (.outer 0) (by decide)
    have h6 := hn (.outer 2) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h0 h1 h2 h3 h4 h6
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith
  · by_contra hn
    push_neg at hn
    have h0 := hn (.center) (by decide)
    have h1 := hn (.middle 0) (by decide)
    have h2 := hn (.middle 1) (by decide)
    have h3 := hn (.middle 2) (by decide)
    have h4 := hn (.outer 0) (by decide)
    have h5 := hn (.outer 1) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h0 h1 h2 h3 h4 h5
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith
  · by_contra hn
    push_neg at hn
    have h0 := hn (.center) (by decide)
    have h2 := hn (.middle 1) (by decide)
    have h3 := hn (.middle 2) (by decide)
    have h4 := hn (.outer 0) (by decide)
    have h5 := hn (.outer 1) (by decide)
    have h6 := hn (.outer 2) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h0 h2 h3 h4 h5 h6
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith
  · by_contra hn
    push_neg at hn
    have h0 := hn (.center) (by decide)
    have h1 := hn (.middle 0) (by decide)
    have h3 := hn (.middle 2) (by decide)
    have h4 := hn (.outer 0) (by decide)
    have h5 := hn (.outer 1) (by decide)
    have h6 := hn (.outer 2) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h0 h1 h3 h4 h5 h6
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith
  · by_contra hn
    push_neg at hn
    have h0 := hn (.center) (by decide)
    have h1 := hn (.middle 0) (by decide)
    have h2 := hn (.middle 1) (by decide)
    have h4 := hn (.outer 0) (by decide)
    have h5 := hn (.outer 1) (by decide)
    have h6 := hn (.outer 2) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h0 h1 h2 h4 h5 h6
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith
  · by_contra hn
    push_neg at hn
    have h1 := hn (.middle 0) (by decide)
    have h2 := hn (.middle 1) (by decide)
    have h3 := hn (.middle 2) (by decide)
    have h4 := hn (.outer 0) (by decide)
    have h5 := hn (.outer 1) (by decide)
    have h6 := hn (.outer 2) (by decide)
    norm_num [reflectDimension,neighbourSum,encode] at h1 h2 h3 h4 h5 h6
    apply hne
    funext v
    cases v with
    | center => simp only [encode]; linarith
    | middle i => fin_cases i <;> simp [encode] <;> linarith
    | outer i => fin_cases i <;> simp [encode] <;> linarith

theorem sourceCycle_encode_nonzero (x : ReflectionReduction.Dimension)
    (hx : encode x ≠ fun _ => 0) :
    encode (ReflectionReduction.sourceCycle x) ≠ fun _ => 0 := by
  intro hz
  have he := congrArg (fun d => ReflectionReduction.sinkCycle (vector d)) hz
  dsimp only at he
  rw [vector_encode,ReflectionReduction.sink_source_inverse] at he
  have hx0 : x = ⟨0,0,0,0,0,0,0⟩ := by simpa [vector,ReflectionReduction.sinkCycle] using he
  apply hx
  rw [hx0]
  funext v
  cases v with
  | center => rfl
  | middle i => fin_cases i <;> rfl
  | outer i => fin_cases i <;> rfl

theorem sourceCycle_iterate_defect (k : ℕ) (x : ReflectionReduction.Dimension) :
    ReflectionReduction.defect ((ReflectionReduction.sourceCycle^[k]) x) = ReflectionReduction.defect x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ReflectionReduction.defect_sourceCycle,ih]

theorem sourceCycle_iterate_nonzero (k : ℕ) (x : ReflectionReduction.Dimension)
    (hx : encode x ≠ fun _ => 0) :
    encode ((ReflectionReduction.sourceCycle^[k]) x) ≠ fun _ => 0 := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact sourceCycle_encode_nonzero _ ih

theorem source_power_action_encode (k : ℕ) (x : ReflectionReduction.Dimension) :
    (sourceWord.power k).action (encode x) = encode ((ReflectionReduction.sourceCycle^[k]) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [SourceWord.power,SourceWord.action_append,ih,sourceWord_action,vector_encode,
      Function.iterate_succ_apply']

theorem source_power_zero_defect_nonsimple (k : ℕ) (x : ReflectionReduction.Dimension)
    (hdef : ReflectionReduction.defect x = 0) (hne : encode x ≠ fun _ => 0) :
    (sourceWord.power k).NonSimpleDims (encode x) := by
  induction k with
  | zero => exact True.intro
  | succ k ih =>
    rw [SourceWord.nonSimpleDims_power_succ,source_power_action_encode]
    exact ⟨ih,source_zero_defect_nonsimple _ ((sourceCycle_iterate_defect k x).trans hdef)
      (sourceCycle_iterate_nonzero k x hne)⟩

theorem indecomposable_dimension_nonzero {K : Type} [Field K] (R : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] (hi : Indecomposable R) :
    dimension R ≠ fun _ => 0 := by
  intro he
  apply hi.1
  intro v x
  have hh := congrFun he v
  change (Module.finrank K (R.space v) : ℤ)=0 at hh
  have hd : Module.finrank K (R.space v)=0 := by exact_mod_cast hh
  haveI : Subsingleton (R.space v) := Module.finrank_zero_iff.mp hd
  exact Subsingleton.elim x 0

/-- The T1 obstruction is excluded from every zero-defect indecomposable,
without fixing its dimension vector or assuming its Tits value is one. -/
theorem tripodEnlargementAt_hom_zero_of_zero_defect {K : Type} [Field K]
    (i : Fin 3) (R S : Rep K inwardE6)
    [∀ v, FiniteDimensional K (R.space v)] [∀ v, FiniteDimensional K (S.space v)]
    (hR : Indecomposable R) (hS : Indecomposable S)
    (hRD : dimension R = encode (tripodEnlargementAt i))
    (hSD : ReflectionReduction.defect (vector (dimension S))=0)
    (f : Hom R S) : f = Hom.zero R S := by
  let w := sourceWord.power 4
  have hr := w.valid_of_dims R hR (by rw [hRD]; exact four_source_tripodEnlargementAt_nonsimple i)
  have hx : encode (vector (dimension S)) ≠ fun _ => 0 := by
    rw [encode_vector]
    exact indecomposable_dimension_nonzero S hS
  have hcert : w.NonSimpleDims (dimension S) := by
    simpa only [encode_vector] using source_power_zero_defect_nonsimple 4 (vector (dimension S)) hSD hx
  have hs := w.valid_of_dims S hS hcert
  have hdR : dimension (w.run R) = fun v => if v = E6Vertex.outer i then 1 else 0 := by
    rw [hr.2.2,hRD]
    exact four_source_tripodEnlargementAt i
  have hdS : ReflectionReduction.defect (vector (dimension (w.run S)))=0 := by
    have he := source_power_action_encode 4 (vector (dimension S))
    rw [encode_vector] at he
    rw [hs.2.2,he,vector_encode,sourceCycle_iterate_defect,hSD]
  have hp : SupportedAt (w.run R) (.outer i) := by
    intro v hv x
    have he := congrFun hdR v
    rw [if_neg hv] at he
    change (Module.finrank K ((w.run R).space v) : ℤ)=0 at he
    have hdim : Module.finrank K ((w.run R).space v)=0 := by exact_mod_cast he
    haveI : Subsingleton ((w.run R).space v) := Module.finrank_zero_iff.mp hdim
    exact Subsingleton.elim x 0
  have hsource : inwardE6.IsSource (.outer i) := by intro e; cases e <;> intro he <;> cases he
  obtain hsimple | ⟨_,hout⟩ := source_step (w.run S) hsource hs.2.1
  · rw [hsimple.dimension] at hdS
    fin_cases i <;> norm_num [ReflectionReduction.defect,vector] at hdS
    exact False.elim (hdS rfl)
  · exact w.hom_zero_of_terminal R S hr.1 hs.1 hsource hp hout f

end UploadBroadcast.ResonantTripodTransversality
