import UploadBroadcast.GeneralBroadcastOptimum
import UploadBroadcast.LinearEntropy
import Mathlib.Data.Finset.Prod

/-! Finite, kernel-checked coefficient-space certificates. The finite carrier is
proved equal to a genuine submodule; cardinality then determines its finrank.
The certificates use ordinary kernel reduction, never native evaluation. -/
namespace UploadBroadcast
namespace FiniteSubspaceCertificate
variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [Fintype V] [DecidableEq V]

structure Space where
  points : Finset V
  zero_mem : 0 ∈ points
  add_mem : ∀ x ∈ points, ∀ y ∈ points, x + y ∈ points
  smul_mem : ∀ c : K, ∀ x ∈ points, c • x ∈ points

namespace Space

def submodule (P : Space (K := K) (V := V)) : Submodule K V where
  carrier := ↑P.points
  zero_mem' := P.zero_mem
  add_mem' := by intro x y hx hy; exact P.add_mem x hx y hy
  smul_mem' c := P.smul_mem c _

omit [Fintype K] [Fintype V] [DecidableEq V] in
@[simp] theorem mem_submodule (P : Space (K := K) (V := V)) (x : V) :
    x ∈ P.submodule ↔ x ∈ P.points := Iff.rfl

def line (v : V) : Space (K := K) (V := V) where
  points := Finset.univ.image (fun c : K => c • v)
  zero_mem := by simp
  add_mem := by
    intro x hx y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨a+b, Finset.mem_univ _, add_smul _ _ _⟩
  smul_mem := by
    intro c x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨c*a, Finset.mem_univ _, mul_smul _ _ _⟩

def join (P Q : Space (K := K) (V := V)) : Space (K := K) (V := V) where
  points := (P.points ×ˢ Q.points).image (fun xy => xy.1 + xy.2)
  zero_mem := Finset.mem_image.mpr ⟨(0,0), Finset.mem_product.mpr
    ⟨P.zero_mem,Q.zero_mem⟩, zero_add 0⟩
  add_mem := by
    intro x hx y hy
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨c,d⟩,hcd,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    refine Finset.mem_image.mpr ⟨(a+c,b+d), Finset.mem_product.mpr
      ⟨P.add_mem a ha c hc,Q.add_mem b hb d hd⟩, ?_⟩
    dsimp; abel
  smul_mem := by
    intro c x hx
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_image.mpr ⟨(c • a,c • b), Finset.mem_product.mpr
      ⟨P.smul_mem c a ha,Q.smul_mem c b hb⟩, (smul_add c a b).symm⟩

def meet (P Q : Space (K := K) (V := V)) : Space (K := K) (V := V) where
  points := P.points ∩ Q.points
  zero_mem := Finset.mem_inter.mpr ⟨P.zero_mem,Q.zero_mem⟩
  add_mem := by
    intro x hx y hy
    exact Finset.mem_inter.mpr ⟨P.add_mem x (Finset.mem_inter.mp hx).1 y
      (Finset.mem_inter.mp hy).1,Q.add_mem x (Finset.mem_inter.mp hx).2 y
      (Finset.mem_inter.mp hy).2⟩
  smul_mem := by
    intro c x hx
    exact Finset.mem_inter.mpr ⟨P.smul_mem c x (Finset.mem_inter.mp hx).1,
      Q.smul_mem c x (Finset.mem_inter.mp hx).2⟩

omit [Fintype K] [Fintype V] in
@[simp] theorem submodule_join (P Q : Space (K := K) (V := V)) :
    (P.join Q).submodule = P.submodule ⊔ Q.submodule := by
  ext x
  simp only [mem_submodule, join, Finset.mem_image, Finset.mem_product,
    Prod.exists, Submodule.mem_sup]
  constructor
  · rintro ⟨a,b,⟨ha,hb⟩,h⟩; exact ⟨a,ha,b,hb,h⟩
  · rintro ⟨a,ha,b,hb,h⟩; exact ⟨a,b,⟨ha,hb⟩,h⟩

omit [Fintype K] [Fintype V] in
@[simp] theorem submodule_meet (P Q : Space (K := K) (V := V)) :
    (P.meet Q).submodule = P.submodule ⊓ Q.submodule := by
  ext x; simp [meet]

omit [Fintype V] [DecidableEq V] in
theorem finrank_eq [FiniteDimensional K V] (P : Space (K := K) (V := V))
    (n : ℕ) (h : P.points.card = Fintype.card K ^ n) :
    Module.finrank K P.submodule = n := by
  letI : Fintype P.submodule := Fintype.ofFinset P.points (fun _ => Iff.rfl)
  have hc : Fintype.card P.submodule = P.points.card := Fintype.card_coe P.points
  have hp := Module.card_eq_pow_finrank (K := K) (V := P.submodule)
  rw [hc,h] at hp
  exact (Nat.pow_right_injective (by have := Fintype.one_lt_card (α := K); omega)) hp.symm

end Space
end FiniteSubspaceCertificate
end UploadBroadcast

namespace UploadBroadcast.FiniteSubspaceCertificate
/-- A computable finite image counts the genuine attained alphabet. -/
theorem range_card {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) :
    Nat.card (Set.range f) = (Finset.univ.image f).card := by
  have h : Set.range f = ↑(Finset.univ.image f) := by ext y; simp
  rw [h, Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe]
end UploadBroadcast.FiniteSubspaceCertificate
