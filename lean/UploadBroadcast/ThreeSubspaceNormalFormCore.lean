import UploadBroadcast.LinearAlgebra
import Mathlib.LinearAlgebra.Projection

/-!
# Simultaneous invariant splittings of three coefficient subspaces

These are actual ambient direct-sum splittings, not dimension identities.
The common and pair blocks are removed by invariant complements, and the
remaining pairwise-disjoint triple is put into private-plus-diagonal coordinates.
-/
namespace UploadBroadcast
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- A complement to a subspace can be chosen to contain any disjoint subspace. -/
theorem exists_complement_containing (P C : Submodule K F) (hPC : Disjoint P C) :
    ∃ Q : Submodule K F, IsCompl P Q ∧ C ≤ Q := by
  obtain ⟨f, hfP, hfC⟩ := exists_joint_extension P C (LinearMap.id : P →ₗ[K] P) 0 (by
    intro p c he
    have hz : (p : F) = 0 := (Submodule.disjoint_def.mp hPC) p p.property (he ▸ c.property)
    exact Subtype.ext hz)
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj (fun p => ?_), ?_⟩
  · exact LinearMap.congr_fun hfP p
  · intro c hc
    exact LinearMap.congr_fun hfC ⟨c, hc⟩

/-- Every complement splits every subspace containing its first factor. -/
theorem subspace_split_of_complement (P Q A : Submodule K F)
    (hPQ : IsCompl P Q) (hPA : P ≤ A) : A = P ⊔ (A ⊓ Q) := by
  apply relay_decomposition P A Q hPA
  rw [hPQ.sup_eq_top]
  exact le_top

/-- The fully common block has a simultaneous invariant complement. -/
theorem three_subspace_common_split (A B C : Submodule K F) :
    ∃ Q : Submodule K F,
      IsCompl (A ⊓ B ⊓ C) Q ∧
      A = (A ⊓ B ⊓ C) ⊔ (A ⊓ Q) ∧
      B = (A ⊓ B ⊓ C) ⊔ (B ⊓ Q) ∧
      C = (A ⊓ B ⊓ C) ⊔ (C ⊓ Q) ∧
      (A ⊓ Q) ⊓ (B ⊓ Q) ⊓ (C ⊓ Q) = ⊥ := by
  obtain ⟨Q, hQ⟩ := (A ⊓ B ⊓ C).exists_isCompl
  refine ⟨Q, hQ,
    subspace_split_of_complement _ _ _ hQ (inf_le_left.trans inf_le_left),
    subspace_split_of_complement _ _ _ hQ (inf_le_left.trans inf_le_right),
    subspace_split_of_complement _ _ _ hQ inf_le_right, ?_⟩
  have he : (A ⊓ Q) ⊓ (B ⊓ Q) ⊓ (C ⊓ Q) = (A ⊓ B ⊓ C) ⊓ Q := by
    ext x
    simp only [Submodule.mem_inf]
    tauto
  rw [he, hQ.inf_eq_bot]

/-- After the common intersection is removed, a whole pair intersection
splits off while the third subspace remains exactly in the residual factor. -/
theorem three_subspace_pair_split (A B C : Submodule K F)
    (hABC : A ⊓ B ⊓ C = ⊥) :
    ∃ Q : Submodule K F,
      IsCompl (A ⊓ B) Q ∧ C ≤ Q ∧
      A = (A ⊓ B) ⊔ (A ⊓ Q) ∧
      B = (A ⊓ B) ⊔ (B ⊓ Q) ∧
      Disjoint (A ⊓ Q) (B ⊓ Q) := by
  obtain ⟨Q, hQ, hCQ⟩ := exists_complement_containing (A ⊓ B) C
    (disjoint_iff.mpr hABC)
  refine ⟨Q, hQ, hCQ,
    subspace_split_of_complement _ _ _ hQ inf_le_left,
    subspace_split_of_complement _ _ _ hQ inf_le_right, ?_⟩
  rw [disjoint_iff]
  have he : (A ⊓ Q) ⊓ (B ⊓ Q) = (A ⊓ B) ⊓ Q := by
    ext x
    simp only [Submodule.mem_inf]
    tauto
  rw [he, hQ.inf_eq_bot]

/-- The non-distributive residual is an actual diagonal graph. Both coordinate
maps are injective, and their sum is the original inclusion of the residual
relation space. This holds over every field, including characteristic two. -/
theorem residual_diagonal_graph (A B D : Submodule K F)
    (hAB : Disjoint A B) (hDA : Disjoint D A) (hDB : Disjoint D B)
    (hD : D ≤ A ⊔ B) :
    ∃ (f : D →ₗ[K] A) (g : D →ₗ[K] B),
      Function.Injective f ∧ Function.Injective g ∧
      A.subtype.comp f + B.subtype.comp g = D.subtype := by
  obtain ⟨p, hpA, hpB⟩ := exists_joint_extension A B (LinearMap.id : A →ₗ[K] A) 0 (by
    intro a b he
    have hz : (a : F) = 0 := Submodule.disjoint_def.mp hAB a a.property (he ▸ b.property)
    exact Subtype.ext hz)
  let f : D →ₗ[K] A := p.comp D.subtype
  have hgB : ∀ d : D, (d : F) - (f d : F) ∈ B := by
    intro d
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hD d.property)
    have hpa : p a = ⟨a, ha⟩ := LinearMap.congr_fun hpA ⟨a, ha⟩
    have hpb : p b = 0 := LinearMap.congr_fun hpB ⟨b, hb⟩
    have hd : (f d : F) = a := by
      change (p (d : F) : F) = a
      rw [← hab, map_add, hpa, hpb, add_zero]
    rw [hd, ← hab]
    simpa using hb
  let g : D →ₗ[K] B := (D.subtype - A.subtype.comp f).codRestrict B hgB
  have hsum : A.subtype.comp f + B.subtype.comp g = D.subtype := by
    ext d
    change (f d : F) + ((d : F) - (f d : F)) = d
    abel
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro d hd
    have hfd : f d = 0 := hd
    have hdB : (d : F) ∈ B := by
      have h := hgB d
      simpa only [hfd, Submodule.coe_zero, sub_zero] using h
    exact Subtype.ext (Submodule.disjoint_def.mp hDB d d.property hdB)
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro d hd
    have hgd : g d = 0 := hd
    have he := LinearMap.congr_fun hsum d
    have hdA : (d : F) ∈ A := by
      change (f d : F) + (g d : F) = d at he
      rw [hgd, Submodule.coe_zero, add_zero] at he
      rw [← he]
      exact (f d).property
    exact Subtype.ext (Submodule.disjoint_def.mp hDA d d.property hdA)
  exact ⟨f, g, hf, hg, hsum⟩

/-- The addition map for two disjoint subspaces is a linear equivalence onto
 their sum, with no finite-dimensional assumption. -/
noncomputable def disjointSumEquiv (A B : Submodule K F) (hAB : Disjoint A B) :
    (A × B) ≃ₗ[K] ↥(A ⊔ B) := by
  let f : (A × B) →ₗ[K] ↥(A ⊔ B) :=
    (A.subtype.coprod B.subtype).codRestrict (A ⊔ B) (by
      intro x
      exact Submodule.add_mem_sup x.1.property x.2.property)
  apply LinearEquiv.ofBijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    rintro ⟨a, b⟩ hx
    have hab : (a : F) + b = 0 := congrArg Subtype.val hx
    have haB : (a : F) ∈ B := by
      rw [eq_neg_of_add_eq_zero_left hab]
      exact B.neg_mem b.property
    have ha : a = 0 := Subtype.ext (Submodule.disjoint_def.mp hAB a a.property haB)
    have hb : b = 0 := by
      apply Subtype.ext
      simpa only [ha, Submodule.coe_zero, zero_add] using hab
    simpa only [ha, hb] using (show (0, 0) ∈ (⊥ : Submodule K (A × B)) from Submodule.zero_mem _)
  · intro x
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp x.property
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext he⟩

@[simp] theorem disjointSumEquiv_apply (A B : Submodule K F) (hAB : Disjoint A B)
    (a : A) (b : B) :
    (disjointSumEquiv A B hAB (a,b) : F) = (a : F) + b := rfl

/-- Removing the relation space inside C leaves a genuine private block,
 complementary to the entire sum A+B. -/
theorem private_third_split (A B C : Submodule K F)
    (hspan : (A ⊔ B) ⊔ C = ⊤) :
    ∃ P : Submodule K F, P ≤ C ∧ IsCompl (A ⊔ B) P ∧
      C = (C ⊓ (A ⊔ B)) ⊔ P := by
  let D := C ⊓ (A ⊔ B)
  obtain ⟨Q, hQ⟩ := D.exists_isCompl
  have hC := subspace_split_of_complement D Q C hQ inf_le_left
  refine ⟨C ⊓ Q, inf_le_left, ?_, hC⟩
  constructor
  · rw [disjoint_iff]
    have he : (A ⊔ B) ⊓ (C ⊓ Q) = D ⊓ Q := by
      ext x
      simp only [D, Submodule.mem_inf]
      tauto
    rw [he, hQ.inf_eq_bot]
  · rw [codisjoint_iff]
    calc
      (A ⊔ B) ⊔ (C ⊓ Q) = (A ⊔ B) ⊔ (D ⊔ (C ⊓ Q)) := by
        rw [← sup_assoc, sup_eq_left.mpr (show D ≤ A ⊔ B from inf_le_right)]
      _ = ⊤ := by rw [← hC, hspan]

/-- Every injective parametrization of a subspace extends to product
coordinates, with the specified parametrization unchanged on the first axis. -/
theorem extend_injection_to_product {D V : Type*}
    [AddCommGroup D] [Module K D] [AddCommGroup V] [Module K V]
    (f : D →ₗ[K] V) (hf : Function.Injective f) :
    ∃ (P : Submodule K V) (e : (D × P) ≃ₗ[K] V),
      ∀ d, e (d, 0) = f d := by
  obtain ⟨P, hP⟩ := (LinearMap.range f).exists_isCompl
  let e := ((LinearEquiv.ofInjective f hf).prodCongr (LinearEquiv.refl K P)).trans
    (Submodule.prodEquivOfIsCompl (LinearMap.range f) P hP)
  refine ⟨P, e, ?_⟩
  intro d
  change f d + (0 : V) = f d
  exact add_zero _

/-- The complete private-plus-tripod normal form for a pairwise-disjoint
triple. The three displayed ranges are exactly the three original coefficient
subspaces. The same parameter appears in both axes of the third range, so
this is the diagonal three-line block, not three unrelated subspaces. -/
theorem pairwise_disjoint_three_subspace_normal_form (A B C : Submodule K F)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hspan : (A ⊔ B) ⊔ C = ⊤) :
    let D := C ⊓ (A ⊔ B)
    ∃ (PA : Submodule K A) (PB : Submodule K B) (PC : Submodule K F)
      (e : (((D × PA) × (D × PB)) × PC) ≃ₗ[K] F),
      Set.range (fun z : D × PA => e ((z, 0), 0)) = (A : Set F) ∧
      Set.range (fun z : D × PB => e ((0, z), 0)) = (B : Set F) ∧
      Set.range (fun z : D × PC => e (((z.1, 0), (z.1, 0)), z.2)) = (C : Set F) := by
  dsimp only
  let D := C ⊓ (A ⊔ B)
  obtain ⟨f, g, hf, hg, hfg⟩ := residual_diagonal_graph A B D hAB
    (hAC.symm.mono_left inf_le_left) (hBC.symm.mono_left inf_le_left) inf_le_right
  obtain ⟨PA, eA, heA⟩ := extend_injection_to_product f hf
  obtain ⟨PB, eB, heB⟩ := extend_injection_to_product g hg
  obtain ⟨PC, hPC, hcomp, hC⟩ := private_third_split A B C hspan
  let e : (((D × PA) × (D × PB)) × PC) ≃ₗ[K] F :=
    (((eA.prodCongr eB).prodCongr (LinearEquiv.refl K PC)).trans
      ((disjointSumEquiv A B hAB).prodCongr (LinearEquiv.refl K PC))).trans
        (Submodule.prodEquivOfIsCompl (A ⊔ B) PC hcomp)
  have he : ∀ a b c, e ((a,b),c) = (eA a : F) + (eB b : F) + (c : F) := by
    intro a b c
    rfl
  have hdiag : ∀ (d : D) (c : PC), e (((d,0),(d,0)),c) = (d : F) + c := by
    intro d c
    rw [he, heA, heB]
    have hh := LinearMap.congr_fun hfg d
    change (f d : F) + (g d : F) = d at hh
    rw [hh]
  refine ⟨PA, PB, PC, e, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      dsimp only
      rw [he]
      simp
    · intro hx
      refine ⟨eA.symm ⟨x, hx⟩, ?_⟩
      dsimp only
      rw [he, eA.apply_symm_apply]
      simp
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      dsimp only
      rw [he]
      simp
    · intro hx
      refine ⟨eB.symm ⟨x, hx⟩, ?_⟩
      dsimp only
      rw [he, eB.apply_symm_apply]
      simp
  · ext x
    constructor
    · rintro ⟨⟨d,c⟩, rfl⟩
      dsimp only
      rw [hdiag]
      exact C.add_mem d.property.1 (hPC c.property)
    · intro hx
      rw [hC] at hx
      obtain ⟨d, hd, c, hc, heq⟩ := Submodule.mem_sup.mp hx
      exact ⟨(⟨d, hd⟩, ⟨c, hc⟩), (hdiag _ _).trans heq⟩

/-- Exact coefficient membership in invariant direct-sum coordinates. -/
theorem invariant_split_membership (P Q X : Submodule K F) (hPQ : IsCompl P Q)
    (hX : X = (X ⊓ P) ⊔ (X ⊓ Q)) (p : P) (q : Q) :
    Submodule.prodEquivOfIsCompl P Q hPQ (p,q) ∈ X ↔
      (p : F) ∈ X ∧ (q : F) ∈ X := by
  constructor
  · intro hx
    rw [hX] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have he : Submodule.prodEquivOfIsCompl P Q hPQ (⟨a,ha.2⟩,⟨b,hb.2⟩) =
        Submodule.prodEquivOfIsCompl P Q hPQ (p,q) := hab
    have hep := congrArg Prod.fst ((Submodule.prodEquivOfIsCompl P Q hPQ).injective he)
    have heq := congrArg Prod.snd ((Submodule.prodEquivOfIsCompl P Q hPQ).injective he)
    exact ⟨(congrArg Subtype.val hep) ▸ ha.1, (congrArg Subtype.val heq) ▸ hb.1⟩
  · rintro ⟨hp,hq⟩
    exact X.add_mem hp hq

/-- An invariant ambient complement preserves the spanning hypothesis when
all three coefficient subspaces are restricted to that complement. -/
theorem invariant_complement_spans (P Q A B C : Submodule K F)
    (hPQ : IsCompl P Q) (hspan : (A ⊔ B) ⊔ C = ⊤)
    (hA : A ≤ P ⊔ (A ⊓ Q)) (hB : B ≤ P ⊔ (B ⊓ Q))
    (hC : C ≤ P ⊔ (C ⊓ Q)) :
    (A.comap Q.subtype ⊔ B.comap Q.subtype) ⊔ C.comap Q.subtype = ⊤ := by
  let p := Q.linearProjOfIsCompl P hPQ.symm
  have stable : ∀ X : Submodule K F, X ≤ P ⊔ (X ⊓ Q) →
      ∀ x ∈ X, (p x : F) ∈ X := by
    intro X hX x hx
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp (hX hx)
    have he' : p x = ⟨b, hb.2⟩ := by
      rw [← he, map_add]
      have hpa : p a = 0 := Submodule.linearProjOfIsCompl_apply_right hPQ.symm ⟨a,ha⟩
      have hpb : p b = ⟨b,hb.2⟩ := Submodule.linearProjOfIsCompl_apply_left hPQ.symm ⟨b,hb.2⟩
      rw [hpa, hpb, zero_add]
    rw [he']
    exact hb.1
  apply top_unique
  intro q _
  have hq : (q : F) ∈ (A ⊔ B) ⊔ C := by rw [hspan]; trivial
  obtain ⟨ab, hab, c, hc, he⟩ := Submodule.mem_sup.mp hq
  obtain ⟨a, ha, b, hb, heab⟩ := Submodule.mem_sup.mp hab
  have hpq : p (q : F) = q := Submodule.linearProjOfIsCompl_apply_left hPQ.symm q
  have hs : p a + p b + p c = q := by
    rw [← map_add, ← map_add, heab, he, hpq]
  rw [← hs]
  exact Submodule.add_mem_sup
    (Submodule.add_mem_sup (stable A hA a ha) (stable B hB b hb)) (stable C hC c hc)

/-- Restriction along a subspace inclusion cannot create intersections. -/
theorem disjoint_restrict (A B Q : Submodule K F) (hAB : Disjoint A B) :
    Disjoint (A.comap Q.subtype) (B.comap Q.subtype) := by
  rw [Submodule.disjoint_def]
  intro q hqA hqB
  exact Subtype.ext (Submodule.disjoint_def.mp hAB q hqA hqB)

/-- A pair intersection complementary to Q disappears inside Q. -/
theorem disjoint_restrict_of_complement (A B Q : Submodule K F)
    (hQ : Disjoint (A ⊓ B) Q) :
    Disjoint (A.comap Q.subtype) (B.comap Q.subtype) := by
  rw [Submodule.disjoint_def]
  intro q hqA hqB
  exact Subtype.ext (Submodule.disjoint_def.mp hQ q ⟨hqA,hqB⟩ q.property)

/-- A certified invariant direct-sum split of a triple. Every field is proved
by the constructors below; this is output data, never a normal-form assumption. -/
structure InvariantTripleSplit (A B C : Submodule K F) where
  block : Submodule K F
  residual : Submodule K F
  complementary : IsCompl block residual
  splitA : A = (A ⊓ block) ⊔ (A ⊓ residual)
  splitB : B = (B ⊓ block) ⊔ (B ⊓ residual)
  splitC : C = (C ⊓ block) ⊔ (C ⊓ residual)

namespace InvariantTripleSplit
variable {A B C : Submodule K F}
abbrev first (s : InvariantTripleSplit A B C) : Submodule K s.residual := A.comap s.residual.subtype
abbrev second (s : InvariantTripleSplit A B C) : Submodule K s.residual := B.comap s.residual.subtype
abbrev third (s : InvariantTripleSplit A B C) : Submodule K s.residual := C.comap s.residual.subtype
noncomputable def equivalence (s : InvariantTripleSplit A B C) :
    (s.block × s.residual) ≃ₗ[K] F := Submodule.prodEquivOfIsCompl _ _ s.complementary

theorem spans (s : InvariantTripleSplit A B C) (h : (A ⊔ B) ⊔ C = ⊤) :
    (s.first ⊔ s.second) ⊔ s.third = ⊤ := by
  apply invariant_complement_spans s.block s.residual A B C s.complementary h
  · exact s.splitA.le.trans (sup_le_sup inf_le_right le_rfl)
  · exact s.splitB.le.trans (sup_le_sup inf_le_right le_rfl)
  · exact s.splitC.le.trans (sup_le_sup inf_le_right le_rfl)
end InvariantTripleSplit

private theorem split_containing (P Q X : Submodule K F) (h : IsCompl P Q) (hP : P ≤ X) :
    X = (X ⊓ P) ⊔ (X ⊓ Q) := by
  rw [inf_eq_right.mpr hP]
  exact subspace_split_of_complement P Q X h hP

private theorem split_inside (P Q X : Submodule K F) (_h : IsCompl P Q) (hQ : X ≤ Q) :
    X = (X ⊓ P) ⊔ (X ⊓ Q) := by
  rw [inf_eq_left.mpr hQ, sup_eq_right.mpr inf_le_left]

/-- Construction of the first, fully common, invariant split. -/
theorem exists_common_invariant_split (A B C : Submodule K F) :
    ∃ s : InvariantTripleSplit A B C,
      s.block = A ⊓ B ⊓ C ∧ s.first ⊓ s.second ⊓ s.third = ⊥ := by
  obtain ⟨Q, hQ⟩ := (A ⊓ B ⊓ C).exists_isCompl
  let s : InvariantTripleSplit A B C := ⟨A ⊓ B ⊓ C, Q, hQ,
    split_containing _ _ _ hQ (inf_le_left.trans inf_le_left),
    split_containing _ _ _ hQ (inf_le_left.trans inf_le_right),
    split_containing _ _ _ hQ inf_le_right⟩
  refine ⟨s, rfl, ?_⟩
  apply le_antisymm _ bot_le
  intro q hq
  apply Subtype.ext
  exact Submodule.disjoint_def.mp hQ.disjoint q ⟨⟨hq.1.1,hq.1.2⟩,hq.2⟩ q.property

/-- Construction of a pure pair invariant split. -/
theorem exists_pair_invariant_split (A B C : Submodule K F)
    (hABC : A ⊓ B ⊓ C = ⊥) :
    ∃ s : InvariantTripleSplit A B C,
      s.block = A ⊓ B ∧ C ≤ s.residual ∧ Disjoint s.first s.second := by
  obtain ⟨Q, hQ, hCQ⟩ := exists_complement_containing (A ⊓ B) C (disjoint_iff.mpr hABC)
  let s : InvariantTripleSplit A B C := ⟨A ⊓ B, Q, hQ,
    split_containing _ _ _ hQ inf_le_left,
    split_containing _ _ _ hQ inf_le_right,
    split_inside _ _ _ hQ hCQ⟩
  exact ⟨s, rfl, hCQ, disjoint_restrict_of_complement A B Q hQ.disjoint⟩

/-- The four invariant peeling steps, retaining their exact subspace
identities. Pair steps are ordered 12, 13, 23. -/
structure ThreeSubspacePeeling (A B C : Submodule K F) where
  common : InvariantTripleSplit A B C
  common_block : common.block = A ⊓ B ⊓ C
  pair12 : InvariantTripleSplit (K := K) (F := common.residual) common.first common.second common.third
  pair12_block : pair12.block = common.first ⊓ common.second
  pair12_third : common.third ≤ pair12.residual
  pair13 : InvariantTripleSplit (K := K) (F := pair12.residual) pair12.first pair12.third pair12.second
  pair13_block : pair13.block = pair12.first ⊓ pair12.third
  pair13_third : pair12.second ≤ pair13.residual
  pair23 : InvariantTripleSplit (K := K) (F := pair13.residual) pair13.third pair13.second pair13.first
  pair23_block : pair23.block = pair13.third ⊓ pair13.second
  pair23_third : pair13.first ≤ pair23.residual
  residual12 : Disjoint pair23.third pair23.first
  residual13 : Disjoint pair23.third pair23.second
  residual23 : Disjoint pair23.first pair23.second

/-- All common and pair blocks can be split off over an arbitrary field,
leaving a pairwise-disjoint triple. No normal form is supplied as input. -/
theorem exists_three_subspace_peeling (A B C : Submodule K F) :
    Nonempty (ThreeSubspacePeeling A B C) := by
  obtain ⟨s0, hs0, hz0⟩ := exists_common_invariant_split A B C
  obtain ⟨s1, hs1, hc1, hd1⟩ := exists_pair_invariant_split (K := K) (F := s0.residual) s0.first s0.second s0.third hz0
  have hz1 : s1.first ⊓ s1.third ⊓ s1.second = ⊥ := by
    apply le_antisymm _ bot_le
    exact (inf_le_inf inf_le_left le_rfl).trans hd1.le_bot
  obtain ⟨s2, hs2, hc2, hd2⟩ := exists_pair_invariant_split (K := K) (F := s1.residual) s1.first s1.third s1.second hz1
  have hdAB : Disjoint s2.first s2.third := disjoint_restrict (K := K) (F := s1.residual) s1.first s1.second s2.residual hd1
  have hz2 : s2.third ⊓ s2.second ⊓ s2.first = ⊥ := by
    apply le_antisymm _ bot_le
    exact (inf_le_inf inf_le_left le_rfl).trans hdAB.symm.le_bot
  obtain ⟨s3, hs3, hc3, hd3⟩ := exists_pair_invariant_split (K := K) (F := s2.residual) s2.third s2.second s2.first hz2
  exact ⟨⟨s0, hs0, s1, hs1, hc1, s2, hs2, hc2, s3, hs3, hc3,
    disjoint_restrict (K := K) (F := s2.residual) s2.first s2.third s3.residual hdAB,
    disjoint_restrict (K := K) (F := s2.residual) s2.first s2.second s3.residual hd2, hd3⟩⟩

namespace ThreeSubspacePeeling
variable {A B C : Submodule K F}
/-- The iterated actual ambient linear equivalence for common/pair peeling. -/
noncomputable def equivalence (s : ThreeSubspacePeeling A B C) :
    (s.common.block × (s.pair12.block × (s.pair13.block ×
      (s.pair23.block × s.pair23.residual)))) ≃ₗ[K] F :=
  ((LinearEquiv.refl K s.common.block).prodCongr
    (((LinearEquiv.refl K s.pair12.block).prodCongr
      (((LinearEquiv.refl K s.pair13.block).prodCongr s.pair23.equivalence).trans
        s.pair13.equivalence)).trans s.pair12.equivalence)).trans s.common.equivalence

/-- The final three subspaces still span the entire residual ambient space. -/
theorem spans (s : ThreeSubspacePeeling A B C) (h : (A ⊔ B) ⊔ C = ⊤) :
    (s.pair23.third ⊔ s.pair23.first) ⊔ s.pair23.second = ⊤ := by
  have h0 := s.common.spans h
  have h1 := s.pair12.spans h0
  have h2 := s.pair13.spans (by calc
    _ = (s.pair12.first ⊔ s.pair12.second) ⊔ s.pair12.third := by ac_rfl
    _ = ⊤ := h1)
  have h3 := s.pair23.spans (by calc
    _ = (s.pair13.first ⊔ s.pair13.second) ⊔ s.pair13.third := by ac_rfl
    _ = ⊤ := h2)
  calc
    _ = (s.pair23.first ⊔ s.pair23.second) ⊔ s.pair23.third := by ac_rfl
    _ = ⊤ := h3

/-- Insert any chosen residual coordinates into the complete common/pair
ambient decomposition. -/
noncomputable def liftResidualEquivalence (s : ThreeSubspacePeeling A B C)
    {R : Type*} [AddCommGroup R] [Module K R]
    (e : R ≃ₗ[K] s.pair23.residual) :
    (s.common.block × (s.pair12.block × (s.pair13.block ×
      (s.pair23.block × R)))) ≃ₗ[K] F :=
  ((LinearEquiv.refl K s.common.block).prodCongr
    ((LinearEquiv.refl K s.pair12.block).prodCongr
      ((LinearEquiv.refl K s.pair13.block).prodCongr
        ((LinearEquiv.refl K s.pair23.block).prodCongr e)))).trans s.equivalence
end ThreeSubspacePeeling

/-- Exact private-plus-diagonal coordinates, packaged as a proposition to
avoid repeatedly elaborating the dependent coordinate types. -/
def HasPrivateTripodNormalForm (A B C : Submodule K F) : Prop :=
  let D := C ⊓ (A ⊔ B)
  ∃ (PA : Submodule K A) (PB : Submodule K B) (PC : Submodule K F)
    (e : (((D × PA) × (D × PB)) × PC) ≃ₗ[K] F),
    Set.range (fun z : D × PA => e ((z, 0), 0)) = (A : Set F) ∧
    Set.range (fun z : D × PB => e ((0, z), 0)) = (B : Set F) ∧
    Set.range (fun z : D × PC => e (((z.1, 0), (z.1, 0)), z.2)) = (C : Set F)

end UploadBroadcast
