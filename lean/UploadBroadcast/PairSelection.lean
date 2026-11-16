import UploadBroadcast.LinearAlgebra
import Mathlib.Order.ModularLattice

namespace UploadBroadcast
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Relative complements within a specified coefficient subspace. -/
theorem exists_relative_complement (A B : Submodule K F) (h : A ≤ B) :
    ∃ C : Submodule K F, C ≤ B ∧ Disjoint A C ∧ A ⊔ C = B := by
  obtain ⟨C,hC⟩ := exists_isCompl (⟨A,h⟩ : Set.Iic B)
  refine ⟨C.1,C.2,?_,?_⟩
  · have hd := hC.disjoint.eq_bot
    exact disjoint_iff.mpr (congrArg Subtype.val hd)
  · exact congrArg Subtype.val hC.codisjoint.eq_top

/-- Select precisely n dimensions inside a finite-dimensional subspace. -/
theorem exists_submodule_finrank [FiniteDimensional K F] (P : Submodule K F)
    (n : ℕ) (hn : n ≤ Module.finrank K P) :
    ∃ Q : Submodule K F, Q ≤ P ∧ Module.finrank K Q = n := by
  obtain ⟨f,hf⟩ := exists_injective_linearMap (K := K) (V := Fin n → K) (W := P)
    (by simpa using hn)
  refine ⟨(LinearMap.range f).map P.subtype, ?_, ?_⟩
  · intro x hx; obtain ⟨y, _, rfl⟩ := hx; exact y.property
  · rw [Submodule.finrank_map_subtype_eq]
    have h := f.finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.mpr hf, finrank_bot, add_zero] at h
    simpa using h

/-- Two-space independent selection (the linear-algebra content of the
Yao–Jafar pair-block lemma). The rank-sum bound is essential. -/
theorem exists_disjoint_pair_selection [FiniteDimensional K F]
    (P Q : Submodule K F) (a b : ℕ)
    (ha : a ≤ Module.finrank K P) (hb : b ≤ Module.finrank K Q)
    (hab : a + b ≤ Module.finrank K ↥(P ⊔ Q)) :
    ∃ X Y : Submodule K F, X ≤ P ∧ Y ≤ Q ∧
      Module.finrank K X = a ∧ Module.finrank K Y = b ∧ Disjoint X Y := by
  obtain ⟨Q₀,hQ₀Q,hIQ₀,hQsplit⟩ := exists_relative_complement (P ⊓ Q) Q inf_le_right
  have hPQ₀ : Disjoint P Q₀ := by
    rw [Submodule.disjoint_def]
    intro x hxP hxQ₀
    exact (Submodule.disjoint_def.mp hIQ₀) x ⟨hxP,hQ₀Q hxQ₀⟩ hxQ₀
  have hdimQ := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ Q) Q₀
  rw [hQsplit,hIQ₀.eq_bot,finrank_bot,add_zero] at hdimQ
  have hdimPQ := Submodule.finrank_sup_add_finrank_inf_eq P Q
  obtain ⟨Y₀,hY₀,hY₀dim⟩ := exists_submodule_finrank Q₀ (min b (Module.finrank K Q₀))
    (min_le_right _ _)
  obtain ⟨Y₁,hY₁,hY₁dim⟩ := exists_submodule_finrank (P ⊓ Q)
    (b - Module.finrank K Q₀) (by omega)
  have hY₁P : Y₁ ≤ P := hY₁.trans inf_le_left
  obtain ⟨P₀,hP₀P,hY₁P₀,hPsplit⟩ := exists_relative_complement Y₁ P hY₁P
  have hdimP := Submodule.finrank_sup_add_finrank_inf_eq Y₁ P₀
  rw [hPsplit,hY₁P₀.eq_bot,finrank_bot,add_zero,hY₁dim] at hdimP
  obtain ⟨X,hX,hXdim⟩ := exists_submodule_finrank P₀ a (by omega)
  have hYdis : Disjoint Y₁ Y₀ := hPQ₀.mono hY₁P hY₀
  have hdimY := Submodule.finrank_sup_add_finrank_inf_eq Y₁ Y₀
  rw [hYdis.eq_bot,finrank_bot,add_zero,hY₁dim,hY₀dim] at hdimY
  refine ⟨X,Y₁ ⊔ Y₀,hX.trans hP₀P,
    sup_le (hY₁.trans inf_le_right) (hY₀.trans hQ₀Q),hXdim,by omega,?_⟩
  rw [Submodule.disjoint_def]
  intro x hx hxy
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hxy
  have hzP : z ∈ P := by
    have he : z = x-y := by rw [← hyz]; abel
    rw [he]
    exact P.sub_mem ((hX.trans hP₀P) hx) (hY₁P hy)
  have hz0 : z = 0 := (Submodule.disjoint_def.mp hPQ₀) z hzP (hY₀ hz)
  have hyx : y = x := by simpa [hz0] using hyz
  exact (Submodule.disjoint_def.mp hY₁P₀) x (hyx ▸ hy) (hX hx)

/-- Conditional rank is the dimension of the image in the side-information
quotient. -/
theorem condRank_eq_finrank_quotient_image [FiniteDimensional K F]
    (P A : Submodule K F) :
    condRank P A = Module.finrank K (P.map A.mkQ) := by
  have hr := (A.mkQ.comp P.subtype).finrank_range_add_finrank_ker
  have hker : LinearMap.ker (A.mkQ.comp P.subtype) = (P ⊓ A).comap P.subtype := by
    ext x
    simp [LinearMap.mem_ker, Submodule.mem_inf, x.property]
  have hdim := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : P ⊓ A ≤ P)).finrank_eq
  rw [hker,hdim] at hr
  have hrange : LinearMap.range (A.mkQ.comp P.subtype) = P.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange] at hr
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P A
  unfold condRank
  rw [sup_comm A P]
  omega

/-- Pair selection independent modulo arbitrary side information. -/
theorem exists_disjoint_pair_selection_modulo [FiniteDimensional K F]
    (A P Q : Submodule K F) (a b : ℕ)
    (ha : a ≤ condRank P A) (hb : b ≤ condRank Q A)
    (hab : a+b ≤ condRank (P ⊔ Q) A) :
    ∃ X Y : Submodule K (F ⧸ A), X ≤ P.map A.mkQ ∧ Y ≤ Q.map A.mkQ ∧
      Module.finrank K X = a ∧ Module.finrank K Y = b ∧ Disjoint X Y := by
  apply exists_disjoint_pair_selection
  · simpa only [condRank_eq_finrank_quotient_image] using ha
  · simpa only [condRank_eq_finrank_quotient_image] using hb
  · rw [condRank_eq_finrank_quotient_image, Submodule.map_sup] at hab
    exact hab

/-- Lift a whole selected subspace through a linear map, preserving the
specified source subspace. This gives simultaneous linear lifts of a basis. -/
theorem exists_linear_lift_submodule {V : Type*} [AddCommGroup V] [Module K V]
    (f : F →ₗ[K] V) (P : Submodule K F) (X : Submodule K V)
    (hX : X ≤ P.map f) :
    ∃ g : X →ₗ[K] F, LinearMap.range g ≤ P ∧ f.comp g = X.subtype := by
  let fp := f.comp P.subtype
  have he : LinearMap.range fp = P.map f := by
    dsimp [fp]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  obtain ⟨s,hs⟩ := fp.rangeRestrict.exists_rightInverse_of_surjective fp.range_rangeRestrict
  let j : X →ₗ[K] LinearMap.range fp := Submodule.inclusion (he.symm ▸ hX)
  refine ⟨P.subtype.comp (s.comp j), ?_, ?_⟩
  · rintro _ ⟨x,rfl⟩
    exact (s (j x)).property
  · ext x
    have h := congrArg Subtype.val (LinearMap.congr_fun hs (j x))
    exact h

/-- Real coefficient subspaces for the pair blocks, jointly independent
modulo the side-information subspace. -/
theorem exists_pair_blocks [FiniteDimensional K F]
    (A P Q : Submodule K F) (a b : ℕ)
    (ha : a ≤ condRank P A) (hb : b ≤ condRank Q A)
    (hab : a+b ≤ condRank (P ⊔ Q) A) :
    ∃ X Y : Submodule K F, X ≤ P ∧ Y ≤ Q ∧
      Module.finrank K X = a ∧ Module.finrank K Y = b ∧
      Disjoint X Y ∧ Disjoint A (X ⊔ Y) := by
  obtain ⟨X,Y,hXP,hYQ,hXa,hYb,hXY⟩ :=
    exists_disjoint_pair_selection_modulo A P Q a b ha hb hab
  obtain ⟨g,hgP,hg⟩ := exists_linear_lift_submodule A.mkQ P X hXP
  obtain ⟨h,hhQ,hh⟩ := exists_linear_lift_submodule A.mkQ Q Y hYQ
  have hginj : Function.Injective g := by
    intro x y he
    apply Subtype.ext
    have e := congrArg A.mkQ he
    simpa only [← LinearMap.comp_apply, hg] using e
  have hhinj : Function.Injective h := by
    intro x y he
    apply Subtype.ext
    have e := congrArg A.mkQ he
    simpa only [← LinearMap.comp_apply, hh] using e
  have hgdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hginj,finrank_bot,add_zero,hXa] at hgdim
  have hhdim := h.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hhinj,finrank_bot,add_zero,hYb] at hhdim
  refine ⟨LinearMap.range g,LinearMap.range h,hgP,hhQ,hgdim,hhdim,?_,?_⟩
  · rw [Submodule.disjoint_def]
    rintro z ⟨x,rfl⟩ ⟨y,he⟩
    have heq : (x : F ⧸ A) = y := by
      have e := congrArg A.mkQ he
      simpa only [← LinearMap.comp_apply, hg, hh] using e.symm
    have hx0 : x = 0 := Subtype.ext
      ((Submodule.disjoint_def.mp hXY) x x.property (heq.symm ▸ y.property))
    simp [hx0]
  · rw [Submodule.disjoint_def]
    intro z hzA hz
    obtain ⟨u,⟨x,rfl⟩,v,⟨y,rfl⟩,he⟩ := Submodule.mem_sup.mp hz
    have hzero : A.mkQ z = 0 := by simpa using hzA
    have heq : (x : F ⧸ A) + y = 0 := by
      rw [← he,map_add] at hzero
      simpa only [← LinearMap.comp_apply,hg,hh] using hzero
    have hxY : (x:F ⧸ A) ∈ Y := by
      rw [eq_neg_of_add_eq_zero_left heq]
      exact Y.neg_mem y.property
    have hx0 : x = 0 := Subtype.ext ((Submodule.disjoint_def.mp hXY) x x.property hxY)
    have hy0 : y = 0 := by
      apply Subtype.ext
      simpa [hx0] using heq
    simpa [hx0,hy0] using he.symm

/-- A preselected independent common block consumes exactly its dimension
from every containing conditional-rank budget. -/
theorem condRank_adjoin_independent [FiniteDimensional K F]
    (A C P : Submodule K F) (hCP : C ≤ P) (hAC : Disjoint A C) :
    condRank P (A ⊔ C) + Module.finrank K C = condRank P A := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A C
  rw [hAC.eq_bot,finrank_bot,add_zero] at hdim
  have hmono := Submodule.finrank_mono (show A ⊔ C ≤ A ⊔ P from sup_le_sup_left hCP A)
  unfold condRank
  rw [sup_assoc, sup_eq_right.mpr hCP]
  omega

/-- Select a single coefficient block independently modulo side information. -/
theorem exists_independent_block [FiniteDimensional K F]
    (A P : Submodule K F) (n : ℕ) (hn : n ≤ condRank P A) :
    ∃ X : Submodule K F, X ≤ P ∧ Module.finrank K X = n ∧ Disjoint A X := by
  obtain ⟨X,Y,hXP,_,hXn,_,_,hAXY⟩ := exists_pair_blocks A P ⊥ n 0 hn
    (Nat.zero_le _) (by simpa using hn)
  exact ⟨X,hXP,hXn,hAXY.mono_right le_sup_left⟩

/-- Separate-user completion for a fixed independent common block. This
constructs both pair blocks, the aligned block, and the individual completion
using only the allocation rank inequalities. -/
theorem exists_user_blocks [FiniteDimensional K F]
    (A C P Q E U : Submodule K F) (a b l h : ℕ)
    (hAU : A ≤ U) (hCP : C ≤ P) (hCQ : C ≤ Q)
    (hPE : P ≤ E) (hQE : Q ≤ E) (hEU : E ≤ U) (hAC : Disjoint A C)
    (ha : Module.finrank K C + a ≤ condRank P A)
    (hb : Module.finrank K C + b ≤ condRank Q A)
    (hab : Module.finrank K C + a + b ≤ condRank (P ⊔ Q) A)
    (hl : Module.finrank K C + a + b + l ≤ condRank E A)
    (htotal : Module.finrank K C + a + b + l + h = condRank U A) :
    ∃ X Y L H : Submodule K F,
      X ≤ P ∧ Y ≤ Q ∧ L ≤ E ∧ H ≤ U ∧
      Module.finrank K X = a ∧ Module.finrank K Y = b ∧
      Module.finrank K L = l ∧ Module.finrank K H = h ∧
      Disjoint X Y ∧ Disjoint (A ⊔ C) (X ⊔ Y) ∧
      Disjoint ((A ⊔ C) ⊔ (X ⊔ Y)) L ∧
      Disjoint (((A ⊔ C) ⊔ (X ⊔ Y)) ⊔ L) H ∧
      (((A ⊔ C) ⊔ (X ⊔ Y)) ⊔ L) ⊔ H = U := by
  have hP := condRank_adjoin_independent A C P hCP hAC
  have hQ := condRank_adjoin_independent A C Q hCQ hAC
  have hPQ := condRank_adjoin_independent A C (P ⊔ Q) (hCP.trans le_sup_left) hAC
  obtain ⟨X,Y,hXP,hYQ,hXa,hYb,hXY,hside⟩ := exists_pair_blocks (A ⊔ C) P Q a b
    (by omega) (by omega) (by omega)
  have hXYE : X ⊔ Y ≤ E := sup_le (hXP.trans hPE) (hYQ.trans hQE)
  have hXYdim : Module.finrank K ↥(X ⊔ Y) = a+b := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq X Y
    rw [hXY.eq_bot,finrank_bot,add_zero,hXa,hYb] at hd
    exact hd
  have hCE : C ≤ E := hCP.trans hPE
  have he₁ := condRank_adjoin_independent A C E hCE hAC
  have he₂ := condRank_adjoin_independent (A ⊔ C) (X ⊔ Y) E hXYE hside
  obtain ⟨L,hLE,hLl,hSL⟩ := exists_independent_block ((A ⊔ C) ⊔ (X ⊔ Y)) E l
    (by rw [hXYdim] at he₂; omega)
  have hSU : ((A ⊔ C) ⊔ (X ⊔ Y)) ⊔ L ≤ U :=
    sup_le (sup_le (sup_le hAU (hCE.trans hEU)) (hXYE.trans hEU)) (hLE.trans hEU)
  obtain ⟨H,hHU,hSH,hspan⟩ := exists_relative_complement _ U hSU
  have hu₁ := condRank_adjoin_independent A C U (hCE.trans hEU) hAC
  have hu₂ := condRank_adjoin_independent (A ⊔ C) (X ⊔ Y) U (hXYE.trans hEU) hside
  have hu₃ := condRank_adjoin_independent ((A ⊔ C) ⊔ (X ⊔ Y)) L U (hLE.trans hEU) hSL
  have hHdim : Module.finrank K H = h := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (((A ⊔ C) ⊔ (X ⊔ Y)) ⊔ L) H
    rw [hspan,hSH.eq_bot,finrank_bot,add_zero] at hd
    have hc : condRank U (((A ⊔ C) ⊔ (X ⊔ Y)) ⊔ L) = Module.finrank K H := by
      unfold condRank
      rw [sup_eq_right.mpr hSU]
      omega
    rw [hc,hLl] at hu₃
    rw [hXYdim] at hu₂
    omega
  exact ⟨X,Y,L,H,hXP,hYQ,hLE,hHU,hXa,hYb,hLl,hHdim,hXY,hside,hSL,hSH,hspan⟩

/-- Ambient span of any subspace basis. -/
theorem span_submodule_basis {J : Type*} (P : Submodule K F) (b : Basis J K P) :
    Submodule.span K (Set.range (fun j => (b j : F))) = P := by
  have he := congrArg (Submodule.map P.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at he
  exact he

/-- Reorder the six LCBC blocks into fixed-side/private and variable blocks. -/
theorem independent_six_blocks {IA IC IP IQ IL IH : Type*}
    (vA : IA → F) (vC : IC → F) (vP : IP → F) (vQ : IQ → F) (vL : IL → F) (vH : IH → F)
    (hi : LinearIndependent K
      (Sum.elim (Sum.elim (Sum.elim (Sum.elim vA vC) (Sum.elim vP vQ)) vL) vH)) :
    LinearIndependent K
      (Sum.elim (Sum.elim vA vH) (Sum.elim vC (Sum.elim (Sum.elim vP vQ) vL))) := by
  let e : (IA ⊕ IH) ⊕ (IC ⊕ ((IP ⊕ IQ) ⊕ IL)) → (((IA ⊕ IC) ⊕ (IP ⊕ IQ)) ⊕ IL) ⊕ IH :=
    Sum.elim (Sum.elim (fun a => Sum.inl (Sum.inl (Sum.inl (Sum.inl a)))) Sum.inr)
      (Sum.elim (fun c => Sum.inl (Sum.inl (Sum.inl (Sum.inr c))))
        (Sum.elim (fun p => Sum.inl (Sum.inl (Sum.inr p))) (fun l => Sum.inl (Sum.inr l))))
  have he : Function.Injective e := by
    intro x y h
    rcases x with (a | h₁) | c | (p | q) | l <;>
      rcases y with (a' | h') | c' | (p' | q') | l' <;> simp_all [e]
  convert hi.comp e he using 1
  funext x
  rcases x with (a | h₁) | c | (p | q) | l <;> rfl

/-- Separate-user basis-family witness in the exact fixed/shared column
layout used by homogeneous coordination. -/
theorem exists_user_column_witness [FiniteDimensional K F]
    (A T P Q E U : Submodule K F) (r a b l h : ℕ)
    (hAU : A ≤ U) (hTP : T ≤ P) (hTQ : T ≤ Q)
    (hPE : P ≤ E) (hQE : Q ≤ E) (hEU : E ≤ U)
    (hr : r ≤ condRank T A)
    (ha : r+a ≤ condRank P A) (hb : r+b ≤ condRank Q A)
    (hab : r+a+b ≤ condRank (P ⊔ Q) A)
    (hl : r+a+b+l ≤ condRank E A) (htotal : r+a+b+l+h = condRank U A) :
    ∃ (c : Fin r → F) (p : Fin a → F) (q : Fin b → F)
      (v : Fin l → F) (w : Fin h → F),
      (∀ j, c j ∈ T) ∧ (∀ j, p j ∈ P) ∧ (∀ j, q j ∈ Q) ∧
      (∀ j, v j ∈ E) ∧ (∀ j, w j ∈ U) ∧
      LinearIndependent K (Sum.elim
        (Sum.elim (fun j => (Module.finBasis K A j : F)) w)
        (Sum.elim c (Sum.elim (Sum.elim p q) v))) ∧
      Submodule.span K (Set.range (Sum.elim
        (Sum.elim (fun j => (Module.finBasis K A j : F)) w)
        (Sum.elim c (Sum.elim (Sum.elim p q) v)))) = U := by
  obtain ⟨C,hCT,hCr,hAC⟩ := exists_independent_block A T r hr
  obtain ⟨X,Y,L,H,hXP,hYQ,hLE,hHU,hXa,hYb,hLl,hHh,hXY,hside,hSL,hSH,hspan⟩ :=
    exists_user_blocks A C P Q E U a b l h hAU (hCT.trans hTP) (hCT.trans hTQ)
      hPE hQE hEU hAC (by simpa [hCr] using ha) (by simpa [hCr] using hb)
      (by simpa [hCr] using hab) (by simpa [hCr] using hl) (by simpa [hCr] using htotal)
  let ba := Module.finBasis K A
  let bc := Module.finBasisOfFinrankEq K C hCr
  let bx := Module.finBasisOfFinrankEq K X hXa
  let by' := Module.finBasisOfFinrankEq K Y hYb
  let bl := Module.finBasisOfFinrankEq K L hLl
  let bh := Module.finBasisOfFinrankEq K H hHh
  have hia := ba.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hic := bc.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hix := bx.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hiy := by'.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)
  have hil := bl.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hih := bh.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
  have hiac := hia.sum_type hic (by simpa only [Function.comp_def, Submodule.subtype_apply, span_submodule_basis] using hAC)
  have hixy := hix.sum_type hiy (by simpa only [Function.comp_def, Submodule.subtype_apply, span_submodule_basis] using hXY)
  have his := hiac.sum_type hixy (by
    simpa only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis] using hside)
  have hisl := his.sum_type hil (by
    simpa only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis] using hSL)
  have hislh := hisl.sum_type hih (by
    simpa only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis] using hSH)
  refine ⟨fun j => bc j,fun j => bx j,fun j => by' j,fun j => bl j,fun j => bh j,
    fun j => hCT (bc j).property,fun j => hXP (bx j).property,
    fun j => hYQ (by' j).property,fun j => hLE (bl j).property,
    fun j => hHU (bh j).property, independent_six_blocks _ _ _ _ _ _ hislh,?_⟩
  simp only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis]
  convert hspan using 1; ac_rfl

/-- Fixed-common-column version of separate-user witnesses. This preserves
an already coordinated common basis, as needed over the binary field. -/
theorem exists_user_column_witness_fixed_common [FiniteDimensional K F]
    (A C P Q E U : Submodule K F) {r : ℕ} (c : Fin r → F) (a b l h : ℕ)
    (hc : LinearIndependent K c) (hcs : Submodule.span K (Set.range c) = C)
    (hAU : A ≤ U) (hCP : C ≤ P) (hCQ : C ≤ Q)
    (hPE : P ≤ E) (hQE : Q ≤ E) (hEU : E ≤ U) (hAC : Disjoint A C)
    (ha : Module.finrank K C+a ≤ condRank P A)
    (hb : Module.finrank K C+b ≤ condRank Q A)
    (hab : Module.finrank K C+a+b ≤ condRank (P ⊔ Q) A)
    (hl : Module.finrank K C+a+b+l ≤ condRank E A)
    (htotal : Module.finrank K C+a+b+l+h = condRank U A) :
    ∃ (p : Fin a → F) (q : Fin b → F) (v : Fin l → F) (w : Fin h → F),
      (∀ j, p j ∈ P) ∧ (∀ j, q j ∈ Q) ∧ (∀ j, v j ∈ E) ∧ (∀ j, w j ∈ U) ∧
      LinearIndependent K (Sum.elim
        (Sum.elim (fun j => (Module.finBasis K A j : F)) w)
        (Sum.elim c (Sum.elim (Sum.elim p q) v))) ∧
      Submodule.span K (Set.range (Sum.elim
        (Sum.elim (fun j => (Module.finBasis K A j : F)) w)
        (Sum.elim c (Sum.elim (Sum.elim p q) v)))) = U := by
  obtain ⟨X,Y,L,H,hXP,hYQ,hLE,hHU,hXa,hYb,hLl,hHh,hXY,hside,hSL,hSH,hspan⟩ :=
    exists_user_blocks A C P Q E U a b l h hAU hCP hCQ
      hPE hQE hEU hAC ha hb
      hab hl htotal
  let ba := Module.finBasis K A
  let bx := Module.finBasisOfFinrankEq K X hXa
  let by' := Module.finBasisOfFinrankEq K Y hYb
  let bl := Module.finBasisOfFinrankEq K L hLl
  let bh := Module.finBasisOfFinrankEq K H hHh
  have hia := ba.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hic := hc
  have hix := bx.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hiy := by'.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)
  have hil := bl.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hih := bh.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
  have hiac := hia.sum_type hic (by simpa only [Function.comp_def, Submodule.subtype_apply, span_submodule_basis, hcs] using hAC)
  have hixy := hix.sum_type hiy (by simpa only [Function.comp_def, Submodule.subtype_apply, span_submodule_basis] using hXY)
  have his := hiac.sum_type hixy (by
    simpa only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis, hcs] using hside)
  have hisl := his.sum_type hil (by
    simpa only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis, hcs] using hSL)
  have hislh := hisl.sum_type hih (by
    simpa only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,Submodule.span_union,span_submodule_basis, hcs] using hSH)
  refine ⟨fun j => bx j,fun j => by' j,fun j => bl j,fun j => bh j,
    fun j => hXP (bx j).property,
    fun j => hYQ (by' j).property,fun j => hLE (bl j).property,
    fun j => hHU (bh j).property, independent_six_blocks _ _ _ _ _ _ hislh,?_⟩
  simp only [Function.comp_def,Submodule.subtype_apply,Set.Sum.elim_range,
    Submodule.span_union,span_submodule_basis,hcs]
  convert hspan using 1; ac_rfl

end UploadBroadcast
