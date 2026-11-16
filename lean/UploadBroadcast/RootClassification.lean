import UploadBroadcast.Structural

/-! Numeric classification only: no assertion about existence or classification of
quiver representations is made here. Arm order is lexicographic in `(a,u)`. -/
namespace UploadBroadcast.RootClassification
open Structural

def ArmLE (u a v b : ℤ) : Prop := a < b ∨ (a = b ∧ u ≤ v)

def Legal (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) : Prop :=
  0 ≤ a₁ ∧ 0 ≤ a₂ ∧ 0 ≤ a₃ ∧ a₁ ≤ u₁ ∧ a₂ ≤ u₂ ∧ a₃ ≤ u₃ ∧
    u₁ ≤ f ∧ u₂ ≤ f ∧ u₃ ≤ f

/-- The nine rows of Table `tab:residues`, with their exact legal translation
thresholds. The seven equalities in each row describe `gamma + n delta`. -/
def TableRow (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) : Prop := ∃ n : ℤ,
  (1 ≤ n ∧ f = 3*n ∧ u₁ = 2*n ∧ u₂ = 2*n ∧ u₃ = 2*n ∧ a₁ = n ∧ a₂ = n ∧ a₃ = n+1) ∨
  (1 ≤ n ∧ f = 3*n ∧ u₁ = 2*n ∧ u₂ = 2*n ∧ u₃ = 2*n+1 ∧ a₁ = n ∧ a₂ = n ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+1 ∧ u₁ = 2*n ∧ u₂ = 2*n+1 ∧ u₃ = 2*n+1 ∧ a₁ = n ∧ a₂ = n+1 ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+1 ∧ u₁ = 2*n+1 ∧ u₂ = 2*n+1 ∧ u₃ = 2*n+1 ∧ a₁ = n ∧ a₂ = n+1 ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+1 ∧ u₁ = 2*n+1 ∧ u₂ = 2*n+1 ∧ u₃ = 2*n+1 ∧ a₁ = n+1 ∧ a₂ = n+1 ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+2 ∧ u₁ = 2*n+1 ∧ u₂ = 2*n+1 ∧ u₃ = 2*n+1 ∧ a₁ = n+1 ∧ a₂ = n+1 ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+2 ∧ u₁ = 2*n+1 ∧ u₂ = 2*n+1 ∧ u₃ = 2*n+2 ∧ a₁ = n+1 ∧ a₂ = n+1 ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+2 ∧ u₁ = 2*n+1 ∧ u₂ = 2*n+2 ∧ u₃ = 2*n+2 ∧ a₁ = n+1 ∧ a₂ = n+1 ∧ a₃ = n+1) ∨
  (0 ≤ n ∧ f = 3*n+2 ∧ u₁ = 2*n+2 ∧ u₂ = 2*n+2 ∧ u₃ = 2*n+2 ∧ a₁ = n+1 ∧ a₂ = n+1 ∧ a₃ = n+1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem sorted_classification (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (hl : Legal f u₁ u₂ u₃ a₁ a₂ a₃)
    (h₁₂ : ArmLE u₁ a₁ u₂ a₂) (h₂₃ : ArmLE u₂ a₂ u₃ a₃)
    (hq : tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1)
    (hc : 0 < excess f a₁ a₂ a₃) : TableRow f u₁ u₂ u₃ a₁ a₂ a₃ := by
  obtain h | h := positive_excess_one_or_two f u₁ u₂ u₃ a₁ a₂ a₃ (by omega) hc
  · have hn := excess_one_near_dimensions f u₁ u₂ u₃ a₁ a₂ a₃ hq h
    unfold excess at h
    unfold Legal at hl
    unfold ArmLE at h₁₂ h₂₃
    refine ⟨f / 3, ?_⟩
    have hr : f % 3 = 0 ∨ f % 3 = 1 ∨ f % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · have ha : a₁ = f/3 ∧ a₂ = f/3 ∧ a₃ = f/3+1 := by omega
      by_cases hu : u₃ = 2*(f/3)
      · left; omega
      · right; left; omega
    · have ha : a₁ = f/3 ∧ a₂ = f/3+1 ∧ a₃ = f/3+1 := by omega
      by_cases hu : u₁ = 2*(f/3)
      · right; right; left; omega
      · right; right; right; left; omega
    · have ha : a₁ = f/3+1 ∧ a₂ = f/3+1 ∧ a₃ = f/3+1 := by omega
      by_cases hu₃ : u₃ = 2*(f/3)+1
      · right; right; right; right; right; left; omega
      · by_cases hu₂ : u₂ = 2*(f/3)+1
        · right; right; right; right; right; right; left; omega
        · by_cases hu₁ : u₁ = 2*(f/3)+1
          · right; right; right; right; right; right; right; left; omega
          · right; right; right; right; right; right; right; right; omega
  · have hn := excess_two_rigidity f u₁ u₂ u₃ a₁ a₂ a₃ hq h
    unfold excess at h
    unfold Legal at hl
    refine ⟨f / 3, ?_⟩
    right; right; right; right; left
    omega


/-- Six possibilities suffice to sort three arms without changing their pairing. -/
lemma sort_arms (u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) :
  (ArmLE u₁ a₁ u₂ a₂ ∧ ArmLE u₂ a₂ u₃ a₃) ∨
  (ArmLE u₁ a₁ u₃ a₃ ∧ ArmLE u₃ a₃ u₂ a₂) ∨
  (ArmLE u₂ a₂ u₁ a₁ ∧ ArmLE u₁ a₁ u₃ a₃) ∨
  (ArmLE u₂ a₂ u₃ a₃ ∧ ArmLE u₃ a₃ u₁ a₁) ∨
  (ArmLE u₃ a₃ u₁ a₁ ∧ ArmLE u₁ a₁ u₂ a₂) ∨
  (ArmLE u₃ a₃ u₂ a₂ ∧ ArmLE u₂ a₂ u₁ a₁) := by
  unfold ArmLE
  omega

def UpToArmPermutation (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) : Prop :=
  TableRow f u₁ u₂ u₃ a₁ a₂ a₃ ∨ TableRow f u₁ u₃ u₂ a₁ a₃ a₂ ∨
  TableRow f u₂ u₁ u₃ a₂ a₁ a₃ ∨ TableRow f u₂ u₃ u₁ a₂ a₃ a₁ ∨
  TableRow f u₃ u₁ u₂ a₃ a₁ a₂ ∨ TableRow f u₃ u₂ u₁ a₃ a₂ a₁

/-- Every legal positive-excess integer vector of Tits value one is in one of the table's nine families, up to simultaneous permutation of its arms.
This is a dimension-vector theorem, with no representation-theoretic premise. -/
theorem classification (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (hl : Legal f u₁ u₂ u₃ a₁ a₂ a₃)
    (hq : tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1)
    (hc : 0 < excess f a₁ a₂ a₃) :
    UpToArmPermutation f u₁ u₂ u₃ a₁ a₂ a₃ := by
  obtain h | h | h | h | h | h := sort_arms u₁ u₂ u₃ a₁ a₂ a₃
  · have l : Legal f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold Legal at *; omega
    have q : tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1 := by
      calc
        _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
        _ = 1 := hq
    have c : 0 < excess f a₁ a₂ a₃ := by unfold excess at *; omega
    have r := sorted_classification f u₁ u₂ u₃ a₁ a₂ a₃ l h.1 h.2 q c
    unfold UpToArmPermutation
    exact Or.inl r
  · have l : Legal f u₁ u₃ u₂ a₁ a₃ a₂ := by unfold Legal at *; omega
    have q : tits f u₁ u₃ u₂ a₁ a₃ a₂ = 1 := by
      calc
        _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
        _ = 1 := hq
    have c : 0 < excess f a₁ a₃ a₂ := by unfold excess at *; omega
    have r := sorted_classification f u₁ u₃ u₂ a₁ a₃ a₂ l h.1 h.2 q c
    unfold UpToArmPermutation
    exact Or.inr (Or.inl r)
  · have l : Legal f u₂ u₁ u₃ a₂ a₁ a₃ := by unfold Legal at *; omega
    have q : tits f u₂ u₁ u₃ a₂ a₁ a₃ = 1 := by
      calc
        _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
        _ = 1 := hq
    have c : 0 < excess f a₂ a₁ a₃ := by unfold excess at *; omega
    have r := sorted_classification f u₂ u₁ u₃ a₂ a₁ a₃ l h.1 h.2 q c
    unfold UpToArmPermutation
    exact Or.inr (Or.inr (Or.inl r))
  · have l : Legal f u₂ u₃ u₁ a₂ a₃ a₁ := by unfold Legal at *; omega
    have q : tits f u₂ u₃ u₁ a₂ a₃ a₁ = 1 := by
      calc
        _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
        _ = 1 := hq
    have c : 0 < excess f a₂ a₃ a₁ := by unfold excess at *; omega
    have r := sorted_classification f u₂ u₃ u₁ a₂ a₃ a₁ l h.1 h.2 q c
    unfold UpToArmPermutation
    exact Or.inr (Or.inr (Or.inr (Or.inl r)))
  · have l : Legal f u₃ u₁ u₂ a₃ a₁ a₂ := by unfold Legal at *; omega
    have q : tits f u₃ u₁ u₂ a₃ a₁ a₂ = 1 := by
      calc
        _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
        _ = 1 := hq
    have c : 0 < excess f a₃ a₁ a₂ := by unfold excess at *; omega
    have r := sorted_classification f u₃ u₁ u₂ a₃ a₁ a₂ l h.1 h.2 q c
    unfold UpToArmPermutation
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r))))
  · have l : Legal f u₃ u₂ u₁ a₃ a₂ a₁ := by unfold Legal at *; omega
    have q : tits f u₃ u₂ u₁ a₃ a₂ a₁ = 1 := by
      calc
        _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
        _ = 1 := hq
    have c : 0 < excess f a₃ a₂ a₁ := by unfold excess at *; omega
    have r := sorted_classification f u₃ u₂ u₁ a₃ a₂ a₁ l h.1 h.2 q c
    unfold UpToArmPermutation
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r)))))

/-- Equation `legal-translate`: for nonnegative base side dimensions and a
nonnegative translate, inclusion is equivalent to the stated maximum bound. -/
theorem legal_translate (f u₁ u₂ u₃ a₁ a₂ a₃ n : ℤ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hn : 0 ≤ n) :
    Legal (f+3*n) (u₁+2*n) (u₂+2*n) (u₃+2*n) (a₁+n) (a₂+n) (a₃+n) ↔
    max 0 (max (max (a₁-u₁) (max (a₂-u₂) (a₃-u₃)))
      (max (u₁-f) (max (u₂-f) (u₃-f)))) ≤ n := by
  simp only [Legal, max_le_iff]
  omega

/-- Conversely, every listed legal translate is a positive-excess vector of
Tits value one. This does not assert that it has a representation. -/
theorem tableRow_sound (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ)
    (h : TableRow f u₁ u₂ u₃ a₁ a₂ a₃) :
    Legal f u₁ u₂ u₃ a₁ a₂ a₃ ∧ tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1 ∧
      0 < excess f a₁ a₂ a₃ := by
  obtain ⟨n, h⟩ := h
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨hn, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold Legal; omega
    · unfold tits; ring
    · unfold excess; omega



/-- Exact least translation indices for all nine rows, even when negative
integer translates are tested. In particular O and H start at one. -/
theorem table_legal_thresholds (n : ℤ) :
    (Legal (3*n) (2*n) (2*n) (2*n) n n (n+1) ↔ 1 ≤ n) ∧
    (Legal (3*n) (2*n) (2*n) (2*n+1) n n (n+1) ↔ 1 ≤ n) ∧
    (Legal (3*n+1) (2*n) (2*n+1) (2*n+1) n (n+1) (n+1) ↔ 0 ≤ n) ∧
    (Legal (3*n+1) (2*n+1) (2*n+1) (2*n+1) n (n+1) (n+1) ↔ 0 ≤ n) ∧
    (Legal (3*n+1) (2*n+1) (2*n+1) (2*n+1) (n+1) (n+1) (n+1) ↔ 0 ≤ n) ∧
    (Legal (3*n+2) (2*n+1) (2*n+1) (2*n+1) (n+1) (n+1) (n+1) ↔ 0 ≤ n) ∧
    (Legal (3*n+2) (2*n+1) (2*n+1) (2*n+2) (n+1) (n+1) (n+1) ↔ 0 ≤ n) ∧
    (Legal (3*n+2) (2*n+1) (2*n+2) (2*n+2) (n+1) (n+1) (n+1) ↔ 0 ≤ n) ∧
    (Legal (3*n+2) (2*n+2) (2*n+2) (2*n+2) (n+1) (n+1) (n+1) ↔ 0 ≤ n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold Legal <;> omega

/-- Bidirectional, exhaustive numerical classification of the legal
positive-excess real-root dimension vectors. -/
theorem classification_iff (f u₁ u₂ u₃ a₁ a₂ a₃ : ℤ) :
    UpToArmPermutation f u₁ u₂ u₃ a₁ a₂ a₃ ↔
    Legal f u₁ u₂ u₃ a₁ a₂ a₃ ∧ tits f u₁ u₂ u₃ a₁ a₂ a₃ = 1 ∧
      0 < excess f a₁ a₂ a₃ := by
  constructor
  · intro h
    rcases h with h | h | h | h | h | h
    · obtain ⟨l, q, c⟩ := tableRow_sound f u₁ u₂ u₃ a₁ a₂ a₃ h
      refine ⟨?_, ?_, ?_⟩
      · unfold Legal at *; omega
      · calc
          _ = tits f u₁ u₂ u₃ a₁ a₂ a₃ := by unfold tits; ring
          _ = 1 := q
      · unfold excess at *; omega
    · obtain ⟨l, q, c⟩ := tableRow_sound f u₁ u₃ u₂ a₁ a₃ a₂ h
      refine ⟨?_, ?_, ?_⟩
      · unfold Legal at *; omega
      · calc
          _ = tits f u₁ u₃ u₂ a₁ a₃ a₂ := by unfold tits; ring
          _ = 1 := q
      · unfold excess at *; omega
    · obtain ⟨l, q, c⟩ := tableRow_sound f u₂ u₁ u₃ a₂ a₁ a₃ h
      refine ⟨?_, ?_, ?_⟩
      · unfold Legal at *; omega
      · calc
          _ = tits f u₂ u₁ u₃ a₂ a₁ a₃ := by unfold tits; ring
          _ = 1 := q
      · unfold excess at *; omega
    · obtain ⟨l, q, c⟩ := tableRow_sound f u₂ u₃ u₁ a₂ a₃ a₁ h
      refine ⟨?_, ?_, ?_⟩
      · unfold Legal at *; omega
      · calc
          _ = tits f u₂ u₃ u₁ a₂ a₃ a₁ := by unfold tits; ring
          _ = 1 := q
      · unfold excess at *; omega
    · obtain ⟨l, q, c⟩ := tableRow_sound f u₃ u₁ u₂ a₃ a₁ a₂ h
      refine ⟨?_, ?_, ?_⟩
      · unfold Legal at *; omega
      · calc
          _ = tits f u₃ u₁ u₂ a₃ a₁ a₂ := by unfold tits; ring
          _ = 1 := q
      · unfold excess at *; omega
    · obtain ⟨l, q, c⟩ := tableRow_sound f u₃ u₂ u₁ a₃ a₂ a₁ h
      refine ⟨?_, ?_, ?_⟩
      · unfold Legal at *; omega
      · calc
          _ = tits f u₃ u₂ u₁ a₃ a₂ a₁ := by unfold tits; ring
          _ = 1 := q
      · unfold excess at *; omega
  · rintro ⟨hl, hq, hc⟩
    exact classification f u₁ u₂ u₃ a₁ a₂ a₃ hl hq hc

end UploadBroadcast.RootClassification
