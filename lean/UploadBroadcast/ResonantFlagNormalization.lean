import UploadBroadcast.ResonantClassification
import UploadBroadcast.ThreeSubspaceNormalFormCore

/-!
# Concrete flag normalization under cross-transversality

The cross-intersection hypotheses in this file are explicit geometric
conditions. They are not inferred from indecomposability here. This is the
remaining boundary between arbitrary source flags and graph classification.
-/
namespace UploadBroadcast.ResonantFlagNormalization
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Two transverse flag pairs produce three direct coordinate factors. -/
noncomputable def twoFlagFrame (A B U V : Submodule K F)
    (_hAU : A ≤ U) (hBV : B ≤ V) (hAV : IsCompl A V) (hBU : IsCompl B U) :
    (A × B × ↥(U ⊓ V)) ≃ₗ[K] F := by
  let f : (A × B × ↥(U ⊓ V)) →ₗ[K] F :=
    A.subtype.coprod (B.subtype.coprod (U ⊓ V).subtype)
  apply LinearEquiv.ofBijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro p hp
    change (p.1 : F) + ((p.2.1 : F) + p.2.2) = 0 at hp
    have ha : (p.1 : F) = 0 := by
      apply hAV.disjoint.le_bot
      refine ⟨p.1.property, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hp]
      exact V.neg_mem (V.add_mem (hBV p.2.1.property) p.2.2.property.2)
    have hb : (p.2.1 : F) = 0 := by
      apply hBU.disjoint.le_bot
      refine ⟨p.2.1.property, ?_⟩
      have he : (p.2.1 : F) + p.2.2 = 0 := by simpa [ha] using hp
      rw [eq_neg_of_add_eq_zero_left he]
      exact U.neg_mem p.2.2.property.1
    have hy : (p.2.2 : F) = 0 := by simpa [ha, hb] using hp
    exact Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hy))
  · intro x
    have hx : x ∈ A ⊔ V := by rw [hAV.sup_eq_top]; trivial
    obtain ⟨a, ha, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    have hv' : v ∈ B ⊔ U := by rw [hBU.sup_eq_top]; trivial
    obtain ⟨b, hb, u, hu, hbu⟩ := Submodule.mem_sup.mp hv'
    have huv : u ∈ V := by
      have he : u = v - b := by rw [← hbu]; abel
      rw [he]
      exact V.sub_mem hv (hBV hb)
    refine ⟨(⟨a,ha⟩,⟨b,hb⟩,⟨u,hu,huv⟩), ?_⟩
    change a + (b + u) = a + v
    rw [hbu]

@[simp] theorem twoFlagFrame_apply (A B U V : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hAV : IsCompl A V) (hBU : IsCompl B U)
    (p : A × B × ↥(U ⊓ V)) :
    twoFlagFrame A B U V hAU hBV hAV hBU p = (p.1 : F) + ((p.2.1 : F) + p.2.2) := rfl

theorem twoFlagFrame_mem_U (A B U V : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hAV : IsCompl A V) (hBU : IsCompl B U)
    (p : A × B × ↥(U ⊓ V)) :
    twoFlagFrame A B U V hAU hBV hAV hBU p ∈ U ↔ p.2.1 = 0 := by
  rw [twoFlagFrame_apply]
  constructor
  · intro hp
    have hb : (p.2.1 : F) ∈ U := by
      have he : (p.2.1 : F) = ((p.1 : F) + ((p.2.1 : F) + p.2.2)) - p.1 - p.2.2 := by abel
      rw [he]
      exact U.sub_mem (U.sub_mem hp (hAU p.1.property)) p.2.2.property.1
    exact Subtype.ext (hBU.disjoint.le_bot ⟨p.2.1.property,hb⟩)
  · intro hb
    simpa [hb] using U.add_mem (hAU p.1.property) p.2.2.property.1

theorem twoFlagFrame_mem_V (A B U V : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hAV : IsCompl A V) (hBU : IsCompl B U)
    (p : A × B × ↥(U ⊓ V)) :
    twoFlagFrame A B U V hAU hBV hAV hBU p ∈ V ↔ p.1 = 0 := by
  rw [twoFlagFrame_apply]
  constructor
  · intro hp
    have ha : (p.1 : F) ∈ V := by
      have he : (p.1 : F) = ((p.1 : F) + ((p.2.1 : F) + p.2.2)) - ((p.2.1 : F) + p.2.2) := by abel
      rw [he]
      exact V.sub_mem hp (V.add_mem (hBV p.2.1.property) p.2.2.property.2)
    exact Subtype.ext (hAV.disjoint.le_bot ⟨p.1.property,ha⟩)
  · intro ha
    simpa [ha] using V.add_mem (hBV p.2.1.property) p.2.2.property.2

/-- A side transverse to both enlarged spaces becomes a diagonal graph.
All equivalences are constructed from coordinate projections. -/
theorem exists_diagonal_frame [FiniteDimensional K F]
    (A B C U V : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hAV : IsCompl A V) (hBU : IsCompl B U)
    (hCU : Disjoint C U) (hCV : Disjoint C V)
    (hCA : Module.finrank K C = Module.finrank K A)
    (hCB : Module.finrank K C = Module.finrank K B) :
    ∃ (e : (C × C × ↥(U ⊓ V)) ≃ₗ[K] F) (L : C →ₗ[K] ↥(U ⊓ V)),
      (∀ c : C, e (c,c,L c) = (c : F)) ∧
      (∀ p, e p ∈ U ↔ p.2.1 = 0) ∧
      (∀ p, e p ∈ V ↔ p.1 = 0) ∧
      (Set.range (fun c : C => e (c,0,0)) = (A : Set F)) ∧
      (Set.range (fun c : C => e (0,c,0)) = (B : Set F)) := by
  let e₀ := twoFlagFrame A B U V hAU hBV hAV hBU
  let a : C →ₗ[K] A := (LinearMap.fst K A (B × ↥(U ⊓ V))).comp
    (e₀.symm.toLinearMap.comp C.subtype)
  let b : C →ₗ[K] B := (LinearMap.fst K B ↥(U ⊓ V)).comp
    ((LinearMap.snd K A (B × ↥(U ⊓ V))).comp (e₀.symm.toLinearMap.comp C.subtype))
  let L : C →ₗ[K] ↥(U ⊓ V) := (LinearMap.snd K B ↥(U ⊓ V)).comp
    ((LinearMap.snd K A (B × ↥(U ⊓ V))).comp (e₀.symm.toLinearMap.comp C.subtype))
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro c hc
    have hv : (c : F) ∈ V := by
      have hh := (twoFlagFrame_mem_V A B U V hAU hBV hAV hBU (e₀.symm c)).mpr hc
      simpa [e₀] using hh
    exact Subtype.ext (hCV.le_bot ⟨c.property,hv⟩)
  have hb : Function.Injective b := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro c hc
    have hu : (c : F) ∈ U := by
      have hh := (twoFlagFrame_mem_U A B U V hAU hBV hAV hBU (e₀.symm c)).mpr hc
      simpa [e₀] using hh
    exact Subtype.ext (hCU.le_bot ⟨c.property,hu⟩)
  let ea := LinearEquiv.ofBijective a ⟨ha,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hCA).mp ha⟩
  let eb := LinearEquiv.ofBijective b ⟨hb,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hCB).mp hb⟩
  let e := (ea.prodCongr (eb.prodCongr (LinearEquiv.refl K ↥(U ⊓ V)))).trans e₀
  have hA (c : C) : e (c,0,0) = (ea c : F) := by simp [e,e₀,twoFlagFrame_apply]
  have hB (c : C) : e (0,c,0) = (eb c : F) := by simp [e,e₀,twoFlagFrame_apply]
  refine ⟨e,L,?_,?_,?_,?_,?_⟩
  · intro c
    change e₀ (a c,b c,L c) = (c : F)
    have hp : (a c,b c,L c) = e₀.symm c := rfl
    rw [hp,e₀.apply_symm_apply]
  · intro p
    change e₀ (ea p.1,eb p.2.1,p.2.2) ∈ U ↔ _
    rw [twoFlagFrame_mem_U]
    exact eb.map_eq_zero_iff
  · intro p
    change e₀ (ea p.1,eb p.2.1,p.2.2) ∈ V ↔ _
    rw [twoFlagFrame_mem_V]
    exact ea.map_eq_zero_iff
  · ext x
    constructor
    · rintro ⟨c,rfl⟩; change e (c,0,0) ∈ A; rw [hA]; exact (ea c).property
    · intro hx; exact ⟨ea.symm ⟨x,hx⟩, by change e (ea.symm ⟨x,hx⟩,0,0) = x; rw [hA,ea.apply_symm_apply]⟩
  · ext x
    constructor
    · rintro ⟨c,rfl⟩; change e (0,c,0) ∈ B; rw [hB]; exact (eb c).property
    · intro hx; exact ⟨eb.symm ⟨x,hx⟩, by change e (0,eb.symm ⟨x,hx⟩,0) = x; rw [hB,eb.apply_symm_apply]⟩

theorem diagonal_map_surjective {Y : Type*} [AddCommGroup Y] [Module K Y]
    (A B C : Submodule K F) (e : (C × C × Y) ≃ₗ[K] F) (L : C →ₗ[K] Y)
    (hC : ∀ c : C, e (c,c,L c) = (c : F))
    (hA : Set.range (fun c : C => e (c,0,0)) = (A : Set F))
    (hB : Set.range (fun c : C => e (0,c,0)) = (B : Set F))
    (hspan : (A ⊔ B) ⊔ C = ⊤) : Function.Surjective L := by
  intro y
  have hy : e (0,0,y) ∈ (A ⊔ B) ⊔ C := by rw [hspan]; trivial
  obtain ⟨ab,hab,c,hc,he⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hab
  have ha' : a ∈ Set.range (fun c : C => e (c,0,0)) := by rw [hA]; exact ha
  have hb' : b ∈ Set.range (fun c : C => e (0,c,0)) := by rw [hB]; exact hb
  obtain ⟨a,rfl⟩ := ha'
  obtain ⟨b,rfl⟩ := hb'
  refine ⟨⟨c,hc⟩, ?_⟩
  rw [← hab] at he
  have hc' : e (⟨c,hc⟩,⟨c,hc⟩,L ⟨c,hc⟩) = c := hC ⟨c,hc⟩
  rw [← hc'] at he
  have hh := congrArg e.symm he
  simp only [map_add, e.symm_apply_apply] at hh
  simpa using congrArg (fun p : C × C × Y => p.2.2) hh

/-- A surjection with a one-dimensional kernel is explicitly split with its
surjection as the first coordinate. -/
theorem split_surjection_one_dim {Z Y : Type*}
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (L : Z →ₗ[K] Y) (hs : Function.Surjective L)
    (hd : Module.finrank K Z = Module.finrank K Y + 1) :
    ∃ s : (Y × K) ≃ₗ[K] Z, ∀ p, L (s p) = p.1 := by
  obtain ⟨t, ht⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  have hLt (y : Y) : L (t y) = y := LinearMap.congr_fun ht y
  let f : (LinearMap.ker L × Y) →ₗ[K] Z := (LinearMap.ker L).subtype.coprod t
  have hf : Function.Bijective f := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply eq_bot_iff.mpr
      intro p hp
      change (p.1 : Z) + t p.2 = 0 at hp
      have hy : p.2 = 0 := by
        have he := congrArg L hp
        simpa [map_add, p.1.property, hLt] using he
      have hk : (p.1 : Z) = 0 := by simpa [hy] using hp
      exact Prod.ext (Subtype.ext hk) hy
    · intro z
      refine ⟨(⟨z-t (L z), ?_⟩,L z), ?_⟩
      · change L (z-t (L z)) = 0
        simp [hLt]
      · change z-t (L z)+t (L z)=z
        abel
  let e := LinearEquiv.ofBijective f hf
  have hker : Module.finrank K (LinearMap.ker L) = 1 := by
    have he := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top] at he
    omega
  let k : K ≃ₗ[K] LinearMap.ker L := LinearEquiv.ofFinrankEq _ _ (by simp [hker])
  let s := (LinearEquiv.prodComm K Y K).trans
    ((k.prodCongr (LinearEquiv.refl K Y)).trans e)
  refine ⟨s, fun p => ?_⟩
  change L ((k p.2 : Z) + t p.1) = p.1
  rw [map_add, (k p.2).property, zero_add, hLt]

/-- The third enlarged space is a graph over the first and third factors.
Containing the diagonal side forces its exact affine-linear graph equation. -/
theorem third_space_graph {Y : Type*} [AddCommGroup Y] [Module K Y]
    (B C W : Submodule K F) (e : (C × C × Y) ≃ₗ[K] F) (L : C →ₗ[K] Y)
    (hC : ∀ c : C, e (c,c,L c) = (c : F))
    (hB : Set.range (fun c : C => e (0,c,0)) = (B : Set F))
    (hCW : C ≤ W) (hBW : IsCompl B W) :
    ∃ T : Y →ₗ[K] C, ∀ p, e p ∈ W ↔ p.2.1 = p.1 + T (p.2.2-L p.1) := by
  let π : F →ₗ[K] (C × Y) :=
    ((LinearMap.fst K C (C × Y)).prod
      ((LinearMap.snd K C Y).comp (LinearMap.snd K C (C × Y)))).comp e.symm.toLinearMap
  let q := π.comp W.subtype
  have hπ (p : C × C × Y) : π (e p) = (p.1,p.2.2) := by simp [π]
  have hπB (b : B) : π b = 0 := by
    have hb : (b : F) ∈ Set.range (fun c : C => e (0,c,0)) := by rw [hB]; exact b.property
    obtain ⟨c,hc⟩ := hb
    change e (0,c,0) = (b : F) at hc
    rw [← hc,hπ]; rfl
  have hq : Function.Bijective q := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply eq_bot_iff.mpr
      intro w hw
      have hz : π w = 0 := hw
      have hp := e.apply_symm_apply (w : F)
      have hfirst : (e.symm w).1 = 0 := congrArg Prod.fst hz
      have hthird : (e.symm w).2.2 = 0 := congrArg Prod.snd hz
      have hwB : (w : F) ∈ B := by
        change (w : F) ∈ (B : Set F)
        rw [← hB]
        refine ⟨(e.symm w).2.1, ?_⟩
        change e (0,(e.symm w).2.1,0) = (w : F)
        change e ((e.symm w).1,(e.symm w).2.1,(e.symm w).2.2) = (w : F) at hp
        simpa only [hfirst,hthird] using hp
      exact Subtype.ext (hBW.disjoint.le_bot ⟨hwB,w.property⟩)
    · rintro ⟨z,y⟩
      have hx : e (z,0,y) ∈ B ⊔ W := by rw [hBW.sup_eq_top]; trivial
      obtain ⟨b,hb,w,hw,he⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨w,hw⟩, ?_⟩
      have hh := congrArg π he
      rw [map_add,hπB ⟨b,hb⟩,zero_add,hπ] at hh
      exact hh
  let s := (LinearEquiv.ofBijective q hq).symm
  let G : (C × Y) →ₗ[K] C := (LinearMap.fst K C Y).comp
    ((LinearMap.snd K C (C × Y)).comp (e.symm.toLinearMap.comp (W.subtype.comp s.toLinearMap)))
  have hs (z : C) (y : Y) : e (z,G (z,y),y) = (s (z,y) : F) := by
    have he := (LinearEquiv.ofBijective q hq).apply_symm_apply (z,y)
    change π (s (z,y)) = (z,y) at he
    have hfirst : (e.symm (s (z,y))).1 = z := congrArg Prod.fst he
    have hthird : (e.symm (s (z,y))).2.2 = y := congrArg Prod.snd he
    have hh := e.apply_symm_apply (s (z,y) : F)
    change e ((e.symm (s (z,y))).1,G (z,y),(e.symm (s (z,y))).2.2) = _ at hh
    simpa only [hfirst,hthird] using hh
  have hgraph (p : C × C × Y) : e p ∈ W ↔ p.2.1 = G (p.1,p.2.2) := by
    constructor
    · intro hp
      let w : W := ⟨e p,hp⟩
      have hqw : q w = (p.1,p.2.2) := hπ p
      have hsw : s (p.1,p.2.2) = w := by
        rw [← hqw]
        exact (LinearEquiv.ofBijective q hq).symm_apply_apply w
      have he := hs p.1 p.2.2
      rw [hsw] at he
      have hh := e.injective he
      exact (congrArg (fun a : C × C × Y => a.2.1) hh).symm
    · intro hp
      have he := hs p.1 p.2.2
      rw [← hp] at he
      rw [he]
      exact (s (p.1,p.2.2)).property
  have hdiag (z : C) : G (z,L z) = z := by
    have hh := (hgraph (z,z,L z)).mp (by rw [hC]; exact hCW z.property)
    exact hh.symm
  let T := G.comp (LinearMap.inr K C Y)
  refine ⟨T, fun p => ?_⟩
  rw [hgraph]
  have he : G (p.1,p.2.2) = p.1+T (p.2.2-L p.1) := by
    have hp : (p.1,p.2.2) = (p.1,L p.1)+(0,p.2.2-L p.1) := by ext <;> simp
    rw [hp,map_add,hdiag]
    rfl
  rw [he]

open ResonantEndomorphisms

/-- Fixed reordering and shearing that takes the first two flag graphs to the
manuscript's first two demand spaces. -/
def coordinateShuffle (Y : Type*) [AddCommGroup Y] [Module K Y] :
    Ambient K Y ≃ₗ[K] ((Y × K) × (Y × K) × Y) where
  toFun p := ((p.1-p.2.2.1,p.2.2.2.1),(p.2.1-p.2.2.1,-p.2.2.2.2),-p.2.2.1)
  invFun p := (p.1.1-p.2.2,p.2.1.1-p.2.2,-p.2.2,p.1.2,-p.2.1.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp <;> abel
  map_smul' a p := by ext <;> simp [smul_sub]

def privateTripodChange {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) :
    Ambient K Y ≃ₗ[K] (Z × Z × Y) :=
  (coordinateShuffle Y).trans (s.prodCongr (s.prodCongr (LinearEquiv.refl K Y)))

theorem privateTripodChange_total₁ {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) (p : Ambient K Y) :
    (privateTripodChange s p).2.1 = 0 ↔ p ∈ total₁ K Y := by
  change s (p.2.1-p.2.2.1,-p.2.2.2.2) = 0 ↔
    p.2.1 = p.2.2.1 ∧ p.2.2.2.2 = 0
  simp [s.map_eq_zero_iff, Prod.mk.injEq, sub_eq_zero]

theorem privateTripodChange_total₂ {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) (p : Ambient K Y) :
    (privateTripodChange s p).1 = 0 ↔ p ∈ total₂ K Y := by
  change s (p.1-p.2.2.1,p.2.2.2.1) = 0 ↔
    p.1 = p.2.2.1 ∧ p.2.2.2.1 = 0
  simp [s.map_eq_zero_iff, Prod.mk.injEq, sub_eq_zero]

theorem privateTripodChange_side₁ {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) (p : Ambient K Y) :
    ((privateTripodChange s p).2.1 = 0 ∧ (privateTripodChange s p).2.2 = 0) ↔
      p ∈ side₁ K Y := by
  change (s (p.2.1-p.2.2.1,-p.2.2.2.2) = 0 ∧ -p.2.2.1 = 0) ↔
    p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.2 = 0
  simp only [s.map_eq_zero_iff, Prod.mk_eq_zero, Prod.mk.injEq, sub_eq_zero, neg_eq_zero]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₁.trans h₃,h₃,h₂⟩
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨⟨h₁.trans h₂.symm,h₃⟩,h₂⟩

theorem privateTripodChange_side₂ {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) (p : Ambient K Y) :
    ((privateTripodChange s p).1 = 0 ∧ (privateTripodChange s p).2.2 = 0) ↔
      p ∈ side₂ K Y := by
  change (s (p.1-p.2.2.1,p.2.2.2.1) = 0 ∧ -p.2.2.1 = 0) ↔
    p.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2.1 = 0
  simp only [s.map_eq_zero_iff, Prod.mk_eq_zero, Prod.mk.injEq, sub_eq_zero, neg_eq_zero]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₁.trans h₃,h₃,h₂⟩
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨⟨h₁.trans h₂.symm,h₃⟩,h₂⟩

theorem privateTripodChange_side₃ {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) (L : Z →ₗ[K] Y)
    (hs : ∀ p, L (s p) = p.1) (p : Ambient K Y) :
    ((privateTripodChange s p).2.1 = (privateTripodChange s p).1 ∧
      (privateTripodChange s p).2.2 = L (privateTripodChange s p).1) ↔
      p ∈ side₃ K Y := by
  change (s (p.2.1-p.2.2.1,-p.2.2.2.2) = s (p.1-p.2.2.1,p.2.2.2.1) ∧
    -p.2.2.1 = L (s (p.1-p.2.2.1,p.2.2.2.1))) ↔
    p.1 = 0 ∧ p.2.1 = 0 ∧ p.2.2.2.1+p.2.2.2.2 = 0
  rw [s.injective.eq_iff, hs]
  simp only [Prod.mk.injEq, sub_left_inj]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃⟩
    have ha : p.1 = 0 := by
      have he := congrArg (fun y : Y => y+p.2.2.1) h₃
      simpa using he.symm
    exact ⟨ha,h₁.trans ha, by linear_combination -h₂⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨⟨hb.trans ha.symm, by linear_combination -hc⟩, by simp [ha]⟩

theorem privateTripodChange_total₃ {Y Z : Type*} [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (s : (Y × K) ≃ₗ[K] Z) (L : Z →ₗ[K] Y)
    (hs : ∀ p, L (s p) = p.1) (T : Y →ₗ[K] Z) (p : Ambient K Y) :
    let D := s.symm.toLinearMap.comp T
    let J := -((LinearMap.fst K Y K).comp D)
    let h := (LinearMap.snd K Y K).comp D
    (privateTripodChange s p).2.1 = (privateTripodChange s p).1 +
      T ((privateTripodChange s p).2.2-L (privateTripodChange s p).1) ↔
      p ∈ total₃ K Y J h := by
  dsimp only
  change s (p.2.1-p.2.2.1,-p.2.2.2.2) = s (p.1-p.2.2.1,p.2.2.2.1) +
      T (-p.2.2.1-L (s (p.1-p.2.2.1,p.2.2.2.1))) ↔
    p.2.1 = p.1 + -(s.symm (T p.1)).1 ∧
      p.2.2.2.1+p.2.2.2.2 = (s.symm (T p.1)).2
  rw [hs]
  have hy : -p.2.2.1-(p.1-p.2.2.1) = -p.1 := by abel
  rw [hy,map_neg]
  rw [← s.symm.injective.eq_iff, map_add,map_neg,s.symm_apply_apply,s.symm_apply_apply]
  rw [Prod.ext_iff]
  change ((p.2.1-p.2.2.1 = (p.1-p.2.2.1)+ -(s.symm (T p.1)).1) ∧
    (-p.2.2.2.2 = p.2.2.2.1 + -(s.symm (T p.1)).2)) ↔ _
  constructor
  · rintro ⟨ha,hb⟩
    constructor
    · have he := congrArg (fun y : Y => y+p.2.2.1) ha
      simpa only [sub_eq_add_neg] using (show p.2.1 = p.1 + -(s.symm (T p.1)).1 from by
        calc p.2.1 = (p.2.1-p.2.2.1)+p.2.2.1 := by abel
             _ = ((p.1-p.2.2.1)+ -(s.symm (T p.1)).1)+p.2.2.1 := he
             _ = p.1 + -(s.symm (T p.1)).1 := by abel)
    · linear_combination -hb
  · rintro ⟨ha,hb⟩
    constructor
    · rw [ha]; abel
    · linear_combination -hb

/-- Membership in each of the three original sides in diagonal coordinates. -/
theorem diagonal_frame_side_membership {Y : Type*} [AddCommGroup Y] [Module K Y]
    (A B C : Submodule K F) (e : (C × C × Y) ≃ₗ[K] F) (L : C →ₗ[K] Y)
    (hC : ∀ c : C, e (c,c,L c) = (c : F))
    (hA : Set.range (fun c : C => e (c,0,0)) = (A : Set F))
    (hB : Set.range (fun c : C => e (0,c,0)) = (B : Set F)) :
    (∀ p, e p ∈ A ↔ p.2.1 = 0 ∧ p.2.2 = 0) ∧
    (∀ p, e p ∈ B ↔ p.1 = 0 ∧ p.2.2 = 0) ∧
    (∀ p, e p ∈ C ↔ p.2.1 = p.1 ∧ p.2.2 = L p.1) := by
  refine ⟨?_,?_,?_⟩
  · intro p
    change e p ∈ (A : Set F) ↔ _
    rw [← hA]
    constructor
    · rintro ⟨c,hc⟩
      change e (c,0,0) = e p at hc
      have he := e.injective hc
      exact ⟨(congrArg (fun q : C × C × Y => q.2.1) he).symm,
        (congrArg (fun q : C × C × Y => q.2.2) he).symm⟩
    · rintro ⟨hb,hy⟩
      exact ⟨p.1,congrArg e (Prod.ext rfl (Prod.ext hb.symm hy.symm))⟩
  · intro p
    change e p ∈ (B : Set F) ↔ _
    rw [← hB]
    constructor
    · rintro ⟨c,hc⟩
      change e (0,c,0) = e p at hc
      have he := e.injective hc
      exact ⟨(congrArg (fun q : C × C × Y => q.1) he).symm,
        (congrArg (fun q : C × C × Y => q.2.2) he).symm⟩
    · rintro ⟨ha,hy⟩
      exact ⟨p.2.1,congrArg e (Prod.ext ha.symm (Prod.ext rfl hy.symm))⟩
  · intro p
    constructor
    · intro hp
      let c : C := ⟨e p,hp⟩
      have he := e.injective (hC c)
      have ha : c = p.1 := congrArg Prod.fst he
      exact ⟨(congrArg (fun q : C × C × Y => q.2.1) he).symm.trans ha,
        (congrArg (fun q : C × C × Y => q.2.2) he).symm.trans (congrArg L ha)⟩
    · rintro ⟨hb,hy⟩
      have he : p = (p.1,p.1,L p.1) := Prod.ext rfl (Prod.ext hb hy)
      rw [he,hC]
      exact p.1.property

/-- The six subspaces of an actual three-arm flag configuration. -/
def flagSpaces (A B C U V W : Submodule K F) : Fin 6 → Submodule K F :=
  ![A,B,C,U,V,W]

/-- Concrete normalization from dimensions, spanning, and five actual cross
intersections. No hypothesis asserts existence of graph coordinates. The sixth
cross intersection is not needed for this construction. -/
theorem normalize_transverse_flags [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hCW : C ≤ W)
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (n : ℕ) (hF : Module.finrank K F = 3*n+2)
    (hA : Module.finrank K A = n+1) (hB : Module.finrank K B = n+1)
    (hC : Module.finrank K C = n+1)
    (hU : Module.finrank K U = 2*n+1) (hV : Module.finrank K V = 2*n+1)
    (hW : Module.finrank K W = 2*n+1)
    (hAV : Disjoint A V) (hBU : Disjoint B U)
    (hCU : Disjoint C U) (hCV : Disjoint C V) (hBW : Disjoint B W) :
    let Y := ↥(U ⊓ V)
    Module.finrank K Y = n ∧
    ∃ (J : Y →ₗ[K] Y) (h : Y →ₗ[K] K) (e : Ambient K Y ≃ₗ[K] F),
      ∀ i p, e p ∈ flagSpaces A B C U V W i ↔ p ∈ spaces K Y J h i := by
  dsimp only
  have hcAV : IsCompl A V := (Submodule.isCompl_iff_disjoint A V (by omega)).mpr hAV
  have hcBU : IsCompl B U := (Submodule.isCompl_iff_disjoint B U (by omega)).mpr hBU
  have hcBW : IsCompl B W := (Submodule.isCompl_iff_disjoint B W (by omega)).mpr hBW
  obtain ⟨e,L,heC,heU,heV,heA,heB⟩ := exists_diagonal_frame A B C U V
    hAU hBV hcAV hcBU hCU hCV (by omega) (by omega)
  have hY : Module.finrank K ↥(U ⊓ V) = n := by
    have he := e.finrank_eq
    simp only [Module.finrank_prod,hC] at he
    omega
  have hL := diagonal_map_surjective A B C e L heC heA heB hspan
  obtain ⟨s,hs⟩ := split_surjection_one_dim L hL (by omega)
  obtain ⟨T,hT⟩ := third_space_graph B C W e L heC heB hCW hcBW
  obtain ⟨hmA,hmB,hmC⟩ := diagonal_frame_side_membership A B C e L heC heA heB
  let D := s.symm.toLinearMap.comp T
  let J := -((LinearMap.fst K ↥(U ⊓ V) K).comp D)
  let h := (LinearMap.snd K ↥(U ⊓ V) K).comp D
  refine ⟨hY,J,h,(privateTripodChange s).trans e,?_⟩
  intro i p
  fin_cases i
  · change e (privateTripodChange s p) ∈ A ↔ p ∈ side₁ K ↥(U ⊓ V)
    rw [hmA]
    exact privateTripodChange_side₁ s p
  · change e (privateTripodChange s p) ∈ B ↔ p ∈ side₂ K ↥(U ⊓ V)
    rw [hmB]
    exact privateTripodChange_side₂ s p
  · change e (privateTripodChange s p) ∈ C ↔ p ∈ side₃ K ↥(U ⊓ V)
    rw [hmC]
    exact privateTripodChange_side₃ s L hs p
  · change e (privateTripodChange s p) ∈ U ↔ p ∈ total₁ K ↥(U ⊓ V)
    rw [heU]
    exact privateTripodChange_total₁ s p
  · change e (privateTripodChange s p) ∈ V ↔ p ∈ total₂ K ↥(U ⊓ V)
    rw [heV]
    exact privateTripodChange_total₂ s p
  · change e (privateTripodChange s p) ∈ W ↔ p ∈ total₃ K ↥(U ⊓ V) J h
    rw [hT]
    exact privateTripodChange_total₃ s L hs T p

/-- Pull indecomposability back through an actual coordinate equivalence. -/
theorem indecomposable_in_coordinates {Y ι : Type*}
    [AddCommGroup Y] [Module K Y] [Nontrivial Y]
    (S : ι → Submodule K Y) (T : ι → Submodule K F) (e : Y ≃ₗ[K] F)
    (he : ∀ i y, e y ∈ T i ↔ y ∈ S i)
    (hi : TaskDecomposition.Indecomposable T ⊤) :
    TaskDecomposition.Indecomposable S ⊤ := by
  apply TaskDecomposition.indecomposable_of_projection_eq_zero_or_id
  · exact top_ne_bot
  · intro f hf hid
    let g : Module.End K F := e.toLinearMap.comp (f.comp e.symm.toLinearMap)
    have hg : TaskDecomposition.Stable T g := by
      intro i x hx
      apply (he i (f (e.symm x))).mpr
      apply hf i
      apply (he i (e.symm x)).mp
      simpa using hx
    have hgid (x : F) : g (g x) = g x := by
      simp only [g,LinearMap.comp_apply,LinearEquiv.coe_coe,e.symm_apply_apply,hid]
    obtain hz | ho := hi.projection_eq_zero_or_id g hg hgid
    · left
      apply LinearMap.ext
      intro y
      apply e.injective
      have hh := congrArg (fun a : Module.End K F => a (e y)) hz
      simpa [g] using hh
    · right
      apply LinearMap.ext
      intro y
      apply e.injective
      have hh := congrArg (fun a : Module.End K F => a (e y)) ho
      simpa [g] using hh

/-- Classification of actual transverse flags of the resonant dimension.
The remaining source-level problem is proving the displayed cross-intersection
hypotheses from arbitrary indecomposability. -/
theorem classify_transverse_resonant_flags [Finite K] [FiniteDimensional K F]
    (A B C U V W : Submodule K F)
    (hAU : A ≤ U) (hBV : B ≤ V) (hCW : C ≤ W)
    (hspan : (A ⊔ B) ⊔ C = ⊤)
    (n : ℕ) (hF : Module.finrank K F = 3*(n+1)+2)
    (hA : Module.finrank K A = (n+1)+1) (hB : Module.finrank K B = (n+1)+1)
    (hC : Module.finrank K C = (n+1)+1)
    (hU : Module.finrank K U = 2*(n+1)+1) (hV : Module.finrank K V = 2*(n+1)+1)
    (hW : Module.finrank K W = 2*(n+1)+1)
    (hAV : Disjoint A V) (hBU : Disjoint B U)
    (hCU : Disjoint C U) (hCV : Disjoint C V) (hBW : Disjoint B W)
    (hi : TaskDecomposition.Indecomposable (flagSpaces A B C U V W) ⊤) :
    TaskDecomposition.ConfigurationIso (flagSpaces A B C U V W)
      (spaces K (JordanResonance.V K n) (JordanResonance.shift K n) (JordanResonance.head K n)) := by
  obtain ⟨hY,J,h,e,he⟩ := normalize_transverse_flags A B C U V W hAU hBV hCW hspan
    (n+1) hF hA hB hC hU hV hW hAV hBU hCU hCV hBW
  have hgraph := indecomposable_in_coordinates (spaces K ↥(U ⊓ V) J h)
    (flagSpaces A B C U V W) e he hi
  obtain ⟨g,hg,hg'⟩ := ResonantClassification.graph_model_classification J h hgraph n hY
  refine ⟨e.symm.trans g, ?_, ?_⟩
  · intro i x hx
    apply hg i
    apply (he i (e.symm x)).mp
    simpa using hx
  · intro i x hx
    apply (he i (g.symm x)).mpr
    exact hg' i x hx

end UploadBroadcast.ResonantFlagNormalization
