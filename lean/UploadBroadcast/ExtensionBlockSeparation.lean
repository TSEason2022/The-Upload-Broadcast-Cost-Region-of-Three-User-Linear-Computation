import UploadBroadcast.ExtensionGenerated
import UploadBroadcast.ExtensionHomVanishing

/-! Explicit removal of cross-class couplings in a block extension. -/
namespace UploadBroadcast.QuiverRepresentation
universe u
variable {K V E : Type u} [Field K] {Q : Orientation V E}

/-- Transport the actual off-diagonal arrow maps along two representation
isomorphisms. -/
def transportCoupling {R S R' S' : Rep K Q} (eR : Iso R R') (eS : Iso S S')
    (z : ArrowMaps S R) : ArrowMaps S' R' := fun a =>
  (eR.map (Q.target a)).toLinearMap.comp
    ((z a).comp (eS.map (Q.source a)).symm.toLinearMap)

/-- The resulting block extensions are genuinely isomorphic. -/
def extensionCongr {R S R' S' : Rep K Q} (eR : Iso R R') (eS : Iso S S')
    (z : ArrowMaps S R) :
    Iso (extension R S z) (extension R' S' (transportCoupling eR eS z)) where
  map v := (eR.map v).prodCongr (eS.map v)
  comm a := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change eR.map (Q.target a) (R.arrow a x.1+z a x.2)=
        R'.arrow a (eR.map (Q.source a) x.1)+
          eR.map (Q.target a) (z a ((eS.map (Q.source a)).symm (eS.map (Q.source a) x.2)))
      rw [map_add,LinearEquiv.symm_apply_apply]
      exact congrArg (· + eR.map (Q.target a) (z a x.2)) (eR.toHom.comm_apply a x.1)
    · exact eS.toHom.comm_apply a x.2

private def blockShear {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (g : B →ₗ[K] A) : (A × B) ≃ₗ[K] (A × B) where
  toFun x := (x.1+g x.2,x.2)
  invFun x := (x.1-g x.2,x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [add_add_add_comm]
  map_smul' c x := by simp [smul_add]

/-- A coboundary changes an extension by an explicit arrow-preserving shear. -/
def extensionShear (R S : Rep K Q) (z₀ z₁ : ArrowMaps S R)
    (g : VertexMaps S R) (hg : coboundary S R g=z₁-z₀) :
    Iso (extension R S z₀) (extension R S z₁) where
  map v := blockShear (g v)
  comm a := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · have he := LinearMap.congr_fun (congrFun hg a) x.2
      change g (Q.target a) (S.arrow a x.2)-R.arrow a (g (Q.source a) x.2)=z₁ a x.2-z₀ a x.2 at he
      change (R.arrow a x.1+z₀ a x.2)+g (Q.target a) (S.arrow a x.2)=
        R.arrow a (x.1+g (Q.source a) x.2)+z₁ a x.2
      rw [map_add,sub_eq_iff_eq_add.mp he]
      abel
    · rfl

/-- Block-diagonal coupling between two pairs of representations. -/
def diagonalCoupling (R₁ R₂ S₁ S₂ : Rep K Q)
    (z₁ : ArrowMaps S₁ R₁) (z₂ : ArrowMaps S₂ R₂) :
    ArrowMaps (S₁.prod S₂) (R₁.prod R₂) := fun a => (z₁ a).prodMap (z₂ a)

/-- Reordering four actual vertex coordinates separates a diagonal extension
into its two classwise extensions. -/
def diagonalExtensionIso (R₁ R₂ S₁ S₂ : Rep K Q)
    (z₁ : ArrowMaps S₁ R₁) (z₂ : ArrowMaps S₂ R₂) :
    Iso (extension (R₁.prod R₂) (S₁.prod S₂) (diagonalCoupling R₁ R₂ S₁ S₂ z₁ z₂))
      ((extension R₁ S₁ z₁).prod (extension R₂ S₂ z₂)) where
  map _ :=
    { toFun := fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))
      invFun := fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm _ := rfl

/-- If both cross-class obstructions vanish, an extension of two sums
separates into one extension within each class. All coupling maps and the
isomorphism are constructed explicitly. -/
theorem extension_separates (R₁ R₂ S₁ S₂ : Rep K Q)
    (z : ArrowMaps (S₁.prod S₂) (R₁.prod R₂))
    (h₁₂ : Function.Surjective (coboundary S₂ R₁))
    (h₂₁ : Function.Surjective (coboundary S₁ R₂)) :
    ∃ (z₁ : ArrowMaps S₁ R₁) (z₂ : ArrowMaps S₂ R₂),
      Nonempty (Iso (extension (R₁.prod R₂) (S₁.prod S₂) z)
        ((extension R₁ S₁ z₁).prod (extension R₂ S₂ z₂))) := by
  let z₁ : ArrowMaps S₁ R₁ := fun a =>
    (LinearMap.fst K _ _).comp ((z a).comp (LinearMap.inl K _ _))
  let z₂ : ArrowMaps S₂ R₂ := fun a =>
    (LinearMap.snd K _ _).comp ((z a).comp (LinearMap.inr K _ _))
  let z₁₂ : ArrowMaps S₂ R₁ := fun a =>
    (LinearMap.fst K _ _).comp ((z a).comp (LinearMap.inr K _ _))
  let z₂₁ : ArrowMaps S₁ R₂ := fun a =>
    (LinearMap.snd K _ _).comp ((z a).comp (LinearMap.inl K _ _))
  obtain ⟨g₁₂,hg₁₂⟩ := h₁₂ z₁₂
  obtain ⟨g₂₁,hg₂₁⟩ := h₂₁ z₂₁
  let g : VertexMaps (S₁.prod S₂) (R₁.prod R₂) := fun v =>
    ((g₁₂ v).comp (LinearMap.snd K _ _)).prod ((g₂₁ v).comp (LinearMap.fst K _ _))
  have hg : coboundary (S₁.prod S₂) (R₁.prod R₂) g=
      z-diagonalCoupling R₁ R₂ S₁ S₂ z₁ z₂ := by
    funext a
    apply LinearMap.ext
    intro x
    have h₁ := LinearMap.congr_fun (congrFun hg₁₂ a) x.2
    have h₂ := LinearMap.congr_fun (congrFun hg₂₁ a) x.1
    change g₁₂ (Q.target a) (S₂.arrow a x.2)-R₁.arrow a (g₁₂ (Q.source a) x.2)=
      (z a (0,x.2)).1 at h₁
    change g₂₁ (Q.target a) (S₁.arrow a x.1)-R₂.arrow a (g₂₁ (Q.source a) x.1)=
      (z a (x.1,0)).2 at h₂
    have hz : z a x=z a (x.1,0)+z a (0,x.2) := by
      rw [←map_add]
      congr 1
      change x=(x.1+0,0+x.2)
      simp
    apply Prod.ext
    · change g₁₂ (Q.target a) (S₂.arrow a x.2)-R₁.arrow a (g₁₂ (Q.source a) x.2)=
        (z a x).1-(z a (x.1,0)).1
      rw [h₁,hz]
      change (z a (0,x.2)).1=(z a (x.1,0)).1+(z a (0,x.2)).1-(z a (x.1,0)).1
      abel
    · change g₂₁ (Q.target a) (S₁.arrow a x.1)-R₂.arrow a (g₂₁ (Q.source a) x.1)=
        (z a x).2-(z a (0,x.2)).2
      rw [h₂,hz]
      change (z a (x.1,0)).2=(z a (x.1,0)).2+(z a (0,x.2)).2-(z a (0,x.2)).2
      abel
  refine ⟨z₁,z₂,⟨?_⟩⟩
  exact (extensionShear (R₁.prod R₂) (S₁.prod S₂) _ z g hg).symm.trans
    (diagonalExtensionIso R₁ R₂ S₁ S₂ z₁ z₂)


/-- Two atom classes with vanishing obstruction in both cross directions
separate throughout their finite extension closure. -/
theorem ExtensionGenerated.separates {C D : Rep K Q → Prop}
    (hCD : ∀ A B, C A → D B → Function.Surjective (coboundary A B))
    (hDC : ∀ A B, D A → C B → Function.Surjective (coboundary A B))
    {R : Rep K Q} (hR : ExtensionGenerated (fun A => C A ∨ D A) R) :
    ∃ A B : Rep K Q, ExtensionGenerated C A ∧ ExtensionGenerated D B ∧
      Nonempty (Iso R (A.prod B)) := by
  induction hR with
  | zero R hz =>
    exact ⟨R,zeroRepresentation,.zero R hz,.zero _ zeroRepresentation_isZero,
      ⟨(isoProdZeroRight R _ zeroRepresentation_isZero).symm⟩⟩
  | atom R hc =>
    rcases hc with hc | hd
    · exact ⟨R,zeroRepresentation,.atom R hc,.zero _ zeroRepresentation_isZero,
        ⟨(isoProdZeroRight R _ zeroRepresentation_isZero).symm⟩⟩
    · exact ⟨zeroRepresentation,R,.zero _ zeroRepresentation_isZero,.atom R hd,
        ⟨(isoProdZeroLeft _ R zeroRepresentation_isZero).symm⟩⟩
  | extension R S z _ _ ihR ihS =>
    obtain ⟨R₁,R₂,hR₁,hR₂,⟨eR⟩⟩ := ihR
    obtain ⟨S₁,S₂,hS₁,hS₂,⟨eS⟩⟩ := ihS
    obtain ⟨z₁,z₂,⟨e⟩⟩ := extension_separates R₁ R₂ S₁ S₂ (transportCoupling eR eS z)
      (hS₂.coboundary_surjective hDC hR₁) (hS₁.coboundary_surjective hCD hR₂)
    exact ⟨QuiverRepresentation.extension R₁ S₁ z₁,QuiverRepresentation.extension R₂ S₂ z₂,
      .extension R₁ S₁ z₁ hR₁ hS₁,.extension R₂ S₂ z₂ hR₂ hS₂,
      ⟨(extensionCongr eR eS z).trans e⟩⟩
  | iso e _ ih =>
    obtain ⟨A,B,hA,hB,⟨e'⟩⟩ := ih
    exact ⟨A,B,hA,hB,⟨e.symm.trans e'⟩⟩

/-- An indecomposable object generated by two mutually extension-orthogonal
classes belongs entirely to one class. This is an actual decomposition proof,
not a tube-classification assumption. -/
theorem ExtensionGenerated.indecomposable_one_class {C D : Rep K Q → Prop}
    (hCD : ∀ A B, C A → D B → Function.Surjective (coboundary A B))
    (hDC : ∀ A B, D A → C B → Function.Surjective (coboundary A B))
    {R : Rep K Q} (hR : ExtensionGenerated (fun A => C A ∨ D A) R)
    (hi : Indecomposable R) : ExtensionGenerated C R ∨ ExtensionGenerated D R := by
  obtain ⟨A,B,hA,hB,⟨e⟩⟩ := hR.separates hCD hDC
  obtain hz | hz := hi.2 A B e
  · exact Or.inr (.iso (e.trans (isoProdZeroLeft A B hz)).symm hB)
  · exact Or.inl (.iso (e.trans (isoProdZeroRight A B hz)).symm hA)


/-- A nonzero map from an atom of one class locates an indecomposable in
that class, when the two classes are both Hom- and extension-orthogonal. -/
theorem ExtensionGenerated.one_class_of_detected_atom {C D : Rep K Q → Prop}
    (hCD : ∀ A B, C A → D B → Function.Surjective (coboundary A B))
    (hDC : ∀ A B, D A → C B → Function.Surjective (coboundary A B))
    (hHom : ∀ A B, C A → D B → HomZero A B)
    {R : Rep K Q} (hR : ExtensionGenerated (fun A => C A ∨ D A) R)
    (hi : Indecomposable R) (A : Rep K Q) (hA : C A)
    (f : Hom A R) (hf : f≠Hom.zero A R) : ExtensionGenerated C R := by
  obtain hc | hd := hR.indecomposable_one_class hCD hDC hi
  · exact hc
  · have hz := ExtensionGenerated.homZero hHom (ExtensionGenerated.atom A hA) hd
    exact False.elim (hf (hz f))

end UploadBroadcast.QuiverRepresentation
