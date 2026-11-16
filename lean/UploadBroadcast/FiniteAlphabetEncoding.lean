import UploadBroadcast.GeneralEntropyConverse

/-! Lossless natural-number encoding of arbitrary heterogeneous finite alphabets.
These lemmas justify the coordinate representation used in the concrete entropy
converse; they preserve actual Shannon entropy and conditional entropy. -/
namespace UploadBroadcast.FiniteAlphabet
open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, Fintype (α i)]

/-- An injective finite alphabet code into the natural numbers. -/
noncomputable def encode {S : Type*} [Fintype S] (s : S) : ℕ :=
  (Fintype.equivFin S s).val

lemma encode_injective {S : Type*} [Fintype S] : Function.Injective (@encode S _) := by
  intro a b h
  apply (Fintype.equivFin S).injective
  exact Fin.ext h

noncomputable def encodeFamily (v : ∀ i, α i) : ι → ℕ := fun i => encode (v i)

def project (A : Finset ι) (v : ∀ i, α i) : ∀ i : A, α i := fun i => v i

noncomputable def encodeSection (A : Finset ι) (v : ∀ i : A, α i) : ι → ℕ :=
  fun i => if hi : i ∈ A then encode (v ⟨i, hi⟩) else 0

omit [Fintype ι] in
lemma encodeSection_injective (A : Finset ι) :
    Function.Injective (encodeSection (α := α) A) := by
  intro a b hab
  funext i
  apply encode_injective
  have hi := congrFun hab i
  simpa only [encodeSection, dif_pos i.property] using hi

omit [Fintype ι] in
lemma observe_encodeFamily {Ω : Type*} (X : Ω → ∀ i, α i) (A : Finset ι) :
    Shannon.observe (encodeFamily ∘ X) A = encodeSection A ∘ (project A ∘ X) := by
  funext ω i
  by_cases hi : i ∈ A <;> simp [Shannon.observe, encodeFamily, encodeSection, project, hi]

variable {Ω : Type*} [MeasurableSpace Ω]
  [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → ∀ i, α i)

omit [DecidableEq ι] in
lemma measurable_encodeFamily (hX : Measurable X) : Measurable (encodeFamily ∘ X) :=
  Measurable.of_discrete.comp hX

instance encoded_finiteRange : FiniteRange (encodeFamily ∘ X) := inferInstance

omit [IsProbabilityMeasure μ] in
/-- Shannon entropy is unchanged by the finite alphabet encoding. -/
lemma entropy_encoded (hX : Measurable X) (A : Finset ι) :
    Shannon.value μ (encodeFamily ∘ X) A = entropy (project A ∘ X) μ := by
  unfold Shannon.value
  rw [observe_encodeFamily]
  exact entropy_comp_of_injective μ (Measurable.of_discrete.comp hX) _ (encodeSection_injective A)

/-- Conditional entropy is unchanged by independently encoding both finite
observation tuples. This includes all functional recovery conditions. -/
lemma conditional_entropy_encoded (hX : Measurable X) (A C : Finset ι) :
    Shannon.cvalue μ (encodeFamily ∘ X) A C =
      condEntropy (project A ∘ X) (project C ∘ X) μ := by
  unfold Shannon.cvalue
  rw [observe_encodeFamily, observe_encodeFamily]
  rw [condEntropy_comp_of_injective μ (Measurable.of_discrete.comp hX)
      (encodeSection A) (encodeSection_injective A)]
  exact condEntropy_of_injective' μ (Measurable.of_discrete.comp hX)
    (Measurable.of_discrete.comp hX) (encodeSection C) (encodeSection_injective C)
    (Measurable.of_discrete.comp (Measurable.of_discrete.comp hX))

omit [IsProbabilityMeasure μ] in
/-- Mutual information is unchanged by the finite alphabet encoding. -/
lemma mutual_information_encoded (hX : Measurable X) (A B : Finset ι) :
    mutualInfo (Shannon.observe (encodeFamily ∘ X) A) (Shannon.observe (encodeFamily ∘ X) B) μ =
      mutualInfo (project A ∘ X) (project B ∘ X) μ := by
  have hA : Measurable (project A ∘ X) := (Measurable.of_discrete (f := project A)).comp hX
  have hB : Measurable (project B ∘ X) := (Measurable.of_discrete (f := project B)).comp hX
  rw [mutualInfo_def, mutualInfo_def]
  rw [show entropy (Shannon.observe (encodeFamily ∘ X) A) μ = _ from entropy_encoded μ X hX A,
      show entropy (Shannon.observe (encodeFamily ∘ X) B) μ = _ from entropy_encoded μ X hX B]
  congr 1
  rw [observe_encodeFamily, observe_encodeFamily]
  change entropy
    ((fun p : (∀ i : A, α i) × (∀ i : B, α i) => (encodeSection A p.1, encodeSection B p.2)) ∘
      (fun ω => (project A (X ω), project B (X ω)))) μ = _
  exact entropy_comp_of_injective μ
    (hA.prodMk hB)
    (fun p : (∀ i : A, α i) × (∀ i : B, α i) => (encodeSection A p.1, encodeSection B p.2))
    (by
      intro p q hpq
      exact Prod.ext (encodeSection_injective A (congrArg Prod.fst hpq))
        (encodeSection_injective B (congrArg Prod.snd hpq)))

/-- Conditional mutual information is unchanged by all three encodings. -/
lemma conditional_mutual_information_encoded (hX : Measurable X) (A B C : Finset ι) :
    Shannon.cinfo μ (encodeFamily ∘ X) A B C =
      condMutualInfo (project A ∘ X) (project B ∘ X) (project C ∘ X) μ := by
  have hA : Measurable (project A ∘ X) := (Measurable.of_discrete (f := project A)).comp hX
  have hB : Measurable (project B ∘ X) := (Measurable.of_discrete (f := project B)).comp hX
  have hC : Measurable (project C ∘ X) := (Measurable.of_discrete (f := project C)).comp hX
  have hm (D : Finset ι) : Measurable (Shannon.observe (encodeFamily ∘ X) D) := by
    rw [observe_encodeFamily]
    exact Measurable.of_discrete.comp (Measurable.of_discrete.comp hX)
  unfold Shannon.cinfo
  rw [condMutualInfo_eq (hm A) (hm B) (hm C),
    condMutualInfo_eq hA hB hC]
  rw [show condEntropy (Shannon.observe (encodeFamily ∘ X) A)
      (Shannon.observe (encodeFamily ∘ X) C) μ = _ from conditional_entropy_encoded μ X hX A C,
    show condEntropy (Shannon.observe (encodeFamily ∘ X) B)
      (Shannon.observe (encodeFamily ∘ X) C) μ = _ from conditional_entropy_encoded μ X hX B C]
  congr 1
  rw [observe_encodeFamily, observe_encodeFamily, observe_encodeFamily]
  change condEntropy
    ((fun p : (∀ i : A, α i) × (∀ i : B, α i) => (encodeSection A p.1, encodeSection B p.2)) ∘
      (fun ω => (project A (X ω), project B (X ω))))
    (encodeSection C ∘ (project C ∘ X)) μ = _
  trans condEntropy (fun ω => (project A (X ω), project B (X ω)))
    (encodeSection C ∘ (project C ∘ X)) μ
  · exact condEntropy_comp_of_injective μ
      (hA.prodMk hB)
      (fun p : (∀ i : A, α i) × (∀ i : B, α i) => (encodeSection A p.1, encodeSection B p.2))
      (by
        intro p q hpq
        exact Prod.ext (encodeSection_injective A (congrArg Prod.fst hpq))
          (encodeSection_injective B (congrArg Prod.snd hpq)))
  · exact condEntropy_of_injective' μ
      (hA.prodMk hB)
      hC (encodeSection C) (encodeSection_injective C)
      (Measurable.of_discrete.comp hC)

/-- Conditional independence of finite observation tuples is preserved by the
encoding, so the hypotheses of the common-function theorem transport too. -/
lemma conditional_independence_encoded (hX : Measurable X) (A B C : Finset ι) :
    CondIndepFun (Shannon.observe (encodeFamily ∘ X) A)
      (Shannon.observe (encodeFamily ∘ X) B) (Shannon.observe (encodeFamily ∘ X) C) μ ↔
    CondIndepFun (project A ∘ X) (project B ∘ X) (project C ∘ X) μ := by
  have hm (D : Finset ι) : Measurable (Shannon.observe (encodeFamily ∘ X) D) := by
    rw [observe_encodeFamily]
    exact Measurable.of_discrete.comp (Measurable.of_discrete.comp hX)
  rw [← condMutualInfo_eq_zero (hm A) (hm B),
    ← condMutualInfo_eq_zero (Measurable.of_discrete.comp hX) (Measurable.of_discrete.comp hX)]
  change Shannon.cinfo μ (encodeFamily ∘ X) A B C = 0 ↔ _
  rw [conditional_mutual_information_encoded μ X hX]

/-- Ordinary independence is preserved by the lossless alphabet encoding. -/
lemma independence_encoded (hX : Measurable X) (A B : Finset ι) :
    IndepFun (Shannon.observe (encodeFamily ∘ X) A)
      (Shannon.observe (encodeFamily ∘ X) B) μ ↔
    IndepFun (project A ∘ X) (project B ∘ X) μ := by
  have hm (D : Finset ι) : Measurable (Shannon.observe (encodeFamily ∘ X) D) := by
    rw [observe_encodeFamily]
    exact Measurable.of_discrete.comp (Measurable.of_discrete.comp hX)
  rw [← mutualInfo_eq_zero (hm A) (hm B),
    ← mutualInfo_eq_zero (Measurable.of_discrete.comp hX) (Measurable.of_discrete.comp hX),
    mutual_information_encoded μ X hX]

end UploadBroadcast.FiniteAlphabet
