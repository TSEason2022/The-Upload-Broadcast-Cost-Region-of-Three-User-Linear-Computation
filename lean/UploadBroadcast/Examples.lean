import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Concrete five-bit example

The source coordinates are `(a,b,c,u,v)` in that order. This file verifies
actual local encoders, a relay, and decoders, not only a claimed numerical
rate. Its code model is explicit Boolean coordinates; no equivalence with
`Task.Code` is asserted here. These finite facts do not prove the paper's
asymptotic upload or broadcast converse.
-/
namespace UploadBroadcast.Examples

abbrev BitSource := Fin 5 → Bool
abbrev Pair := Bool × Bool
abbrev Triple := Bool × Bool × Bool

def side1 (s : BitSource) : Pair := (s 0, s 3)
def side2 (s : BitSource) : Pair := (s 1, s 4)
def side3 (s : BitSource) : Pair := (s 2, Bool.xor (s 3) (s 4))
def demand1 (s : BitSource) : Bool := Bool.xor (s 1) (s 2)
def demand2 (s : BitSource) : Bool := Bool.xor (s 0) (s 2)
def demand3 (s : BitSource) : Bool := Bool.xor (Bool.xor (s 0) (s 1)) (s 3)

/-- Each two-instance upload depends only on that user's two side inputs. -/
def encode1 (w : Pair × Pair) : Triple := (w.1.1, w.1.2, w.2.1)
def encode2 (w : Pair × Pair) : Triple := (w.1.1, w.2.1, w.2.2)
def encode3 (w : Pair × Pair) : Pair := (w.1.1, w.2.1)
def relay (m1 m2 : Triple) (m3 : Pair) : Triple :=
  let t1 := Bool.xor (Bool.xor m1.1 m2.1) m3.1
  let t2 := Bool.xor (Bool.xor m1.2.2 m2.2.1) m3.2
  (Bool.xor t1 t2, Bool.xor t1 m1.2.1, Bool.xor t2 m2.2.2)
def broadcast2 (s : BitSource × BitSource) : Triple :=
  relay (encode1 (side1 s.1, side1 s.2))
    (encode2 (side2 s.1, side2 s.2)) (encode3 (side3 s.1, side3 s.2))
def decode1 (c : Triple) (w : Pair × Pair) : Pair :=
  let t1 := Bool.xor c.2.1 w.1.2
  (Bool.xor t1 w.1.1, Bool.xor (Bool.xor c.1 t1) w.2.1)
def decode2 (c : Triple) (w : Pair × Pair) : Pair :=
  let t2 := Bool.xor c.2.2 w.2.2
  (Bool.xor (Bool.xor c.1 t2) w.1.1, Bool.xor t2 w.2.1)
def decode3 (c : Triple) (w : Pair × Pair) : Pair :=
  (Bool.xor c.2.1 w.1.1, Bool.xor (Bool.xor c.2.2 w.2.1) w.2.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem two_instance_zero_error : ∀ s : BitSource × BitSource,
    decode1 (broadcast2 s) (side1 s.1, side1 s.2) = (demand1 s.1, demand1 s.2) ∧
    decode2 (broadcast2 s) (side2 s.1, side2 s.2) = (demand2 s.1, demand2 s.2) ∧
    decode3 (broadcast2 s) (side3 s.1, side3 s.2) = (demand3 s.1, demand3 s.2) := by
  intro s
  simp [decode1, decode2, decode3, broadcast2, relay, encode1, encode2, encode3,
    side1, side2, side3, demand1, demand2, demand3,
    Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

/-- Exact attained upload alphabets, not nominal codomain upper bounds. -/
theorem upload_alphabet_sizes :
    (Finset.univ.image encode1).card = 8 ∧
    (Finset.univ.image encode2).card = 8 ∧
    (Finset.univ.image encode3).card = 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem broadcast2_surjective : Function.Surjective broadcast2 := by
  intro ⟨x, y, z⟩
  refine ⟨(![false,false,false,y,false], ![x,false,false,false,Bool.xor z x]), ?_⟩
  cases x <;> cases y <;> cases z <;> rfl

theorem broadcast_alphabet_size : Fintype.card (Set.range broadcast2) = 8 := by
  simp [Set.range_eq_univ.mpr broadcast2_surjective, Triple]

/-- Actual source-attainable upload cardinalities. -/
theorem attained_upload1_surjective : Function.Surjective
    (fun s : BitSource × BitSource => encode1 (side1 s.1, side1 s.2)) := by
  intro ⟨x,y,z⟩
  exact ⟨(![x,false,false,y,false], ![z,false,false,false,false]), rfl⟩
theorem attained_upload2_surjective : Function.Surjective
    (fun s : BitSource × BitSource => encode2 (side2 s.1, side2 s.2)) := by
  intro ⟨x,y,z⟩
  exact ⟨(![false,x,false,false,false], ![false,y,false,false,z]), rfl⟩
theorem attained_upload3_surjective : Function.Surjective
    (fun s : BitSource × BitSource => encode3 (side3 s.1, side3 s.2)) := by
  intro ⟨x,y⟩
  exact ⟨(![false,false,x,false,false], ![false,false,y,false,false]), rfl⟩

theorem attained_upload_alphabet_sizes :
    Fintype.card (Set.range (fun s : BitSource × BitSource =>
      encode1 (side1 s.1, side1 s.2))) = 8 ∧
    Fintype.card (Set.range (fun s : BitSource × BitSource =>
      encode2 (side2 s.1, side2 s.2))) = 8 ∧
    Fintype.card (Set.range (fun s : BitSource × BitSource =>
      encode3 (side3 s.1, side3 s.2))) = 4 := by
  simp [Set.range_eq_univ.mpr attained_upload1_surjective,
    Set.range_eq_univ.mpr attained_upload2_surjective,
    Set.range_eq_univ.mpr attained_upload3_surjective, Triple, Pair]

/-- The three source assignments form a triangle in the scalar confusability graph. -/
def source0 : BitSource := ![false,false,false,false,false]
def source1 : BitSource := ![false,false,false,true,true]
def source2 : BitSource := ![false,false,true,false,true]

/-- No fully informed scalar binary broadcast can satisfy all three users.
This permits arbitrary nonlinear encoders and decoders. -/
theorem source_triangle_distinct {S : Type*}
    (b : BitSource → S) (d1 d2 d3 : S → Pair → Bool)
    (h1 : ∀ s, d1 (b s) (side1 s) = demand1 s)
    (h2 : ∀ s, d2 (b s) (side2 s) = demand2 s)
    (h3 : ∀ s, d3 (b s) (side3 s) = demand3 s) :
    b source0 ≠ b source1 ∧ b source0 ≠ b source2 ∧ b source1 ≠ b source2 := by
  have h01 : b source0 ≠ b source1 := by
    intro h
    have a := h3 source0
    have z := h3 source1
    rw [h] at a
    have sides : side3 source0 = side3 source1 := by decide
    rw [sides] at a
    have : demand3 source0 = demand3 source1 := a.symm.trans z
    contradiction
  have h02 : b source0 ≠ b source2 := by
    intro h
    have a := h1 source0
    have z := h1 source2
    rw [h] at a
    have sides : side1 source0 = side1 source2 := by decide
    rw [sides] at a
    have : demand1 source0 = demand1 source2 := a.symm.trans z
    contradiction
  have h12 : b source1 ≠ b source2 := by
    intro h
    have a := h2 source1
    have z := h2 source2
    rw [h] at a
    have sides : side2 source1 = side2 source2 := by decide
    rw [sides] at a
    have : demand2 source1 = demand2 source2 := a.symm.trans z
    contradiction
  exact ⟨h01, h02, h12⟩

theorem no_scalar_bit_broadcast
    (b : BitSource → Bool) (d1 d2 d3 : Bool → Pair → Bool)
    (h1 : ∀ s, d1 (b s) (side1 s) = demand1 s)
    (h2 : ∀ s, d2 (b s) (side2 s) = demand2 s)
    (h3 : ∀ s, d3 (b s) (side3 s) = demand3 s) : False := by
  obtain ⟨h01, h02, h12⟩ := source_triangle_distinct b d1 d2 d3 h1 h2 h3
  cases hb0 : b source0 <;> cases hb1 : b source1 <;> cases hb2 : b source2 <;>
    simp_all

/-- A nonlinear fully informed scalar broadcast requires at least three
attainable messages, independent of its nominal codomain. -/
theorem three_le_scalar_broadcast_range {S : Type*} [Fintype S] [DecidableEq S]
    (b : BitSource → S) (d1 d2 d3 : S → Pair → Bool)
    (h1 : ∀ s, d1 (b s) (side1 s) = demand1 s)
    (h2 : ∀ s, d2 (b s) (side2 s) = demand2 s)
    (h3 : ∀ s, d3 (b s) (side3 s) = demand3 s) :
    3 ≤ Fintype.card (Set.range b) := by
  classical
  obtain ⟨h01, h02, h12⟩ := source_triangle_distinct b d1 d2 d3 h1 h2 h3
  let f : Fin 3 → Set.range b := fun i =>
    ⟨b (![source0, source1, source2] i), ⟨![source0, source1, source2] i, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa using Fintype.card_le_of_injective f hf

theorem logb_two_eight : Real.logb 2 8 = 3 := by
  have h := Real.logb_pow 2 2 3
  norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at h
  exact h

theorem logb_two_four : Real.logb 2 4 = 2 := by
  have h := Real.logb_pow 2 2 2
  norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at h
  exact h

/-- The original-field two-instance code has the claimed normalized alphabet costs. -/
theorem two_instance_costs :
    (Real.logb 2 8 + Real.logb 2 8 + Real.logb 2 4) / 2 = 4 ∧
    Real.logb 2 8 / 2 = (3:ℝ) / 2 := by
  rw [logb_two_eight, logb_two_four]
  norm_num

/-- Costs computed directly from the source-attainable alphabets of the
specified code, using the paper's base-two and blocklength-two convention. -/
noncomputable def twoInstanceUploadCost : ℝ :=
  (Real.logb 2 (Fintype.card (Set.range (fun s : BitSource × BitSource =>
      encode1 (side1 s.1, side1 s.2)))) +
   Real.logb 2 (Fintype.card (Set.range (fun s : BitSource × BitSource =>
      encode2 (side2 s.1, side2 s.2)))) +
   Real.logb 2 (Fintype.card (Set.range (fun s : BitSource × BitSource =>
      encode3 (side3 s.1, side3 s.2))))) / 2
noncomputable def twoInstanceBroadcastCost : ℝ :=
  Real.logb 2 (Fintype.card (Set.range broadcast2)) / 2

theorem actual_two_instance_costs :
    twoInstanceUploadCost = 4 ∧ twoInstanceBroadcastCost = (3:ℝ)/2 := by
  obtain ⟨h1,h2,h3⟩ := attained_upload_alphabet_sizes
  simp only [twoInstanceUploadCost, twoInstanceBroadcastCost, h1, h2, h3,
    broadcast_alphabet_size]
  norm_num only [Nat.cast_ofNat]
  exact two_instance_costs

/-- A single complete certificate of the stated two-instance code: all users
recover both demands, and its attained alphabet costs are exactly `(4,3/2)`.
The named encoders above explicitly factor through their local side information. -/
theorem two_instance_achievability :
    (∀ s : BitSource × BitSource,
      decode1 (broadcast2 s) (side1 s.1, side1 s.2) = (demand1 s.1, demand1 s.2) ∧
      decode2 (broadcast2 s) (side2 s.1, side2 s.2) = (demand2 s.1, demand2 s.2) ∧
      decode3 (broadcast2 s) (side3 s.1, side3 s.2) = (demand3 s.1, demand3 s.2)) ∧
    twoInstanceUploadCost = 4 ∧ twoInstanceBroadcastCost = (3:ℝ)/2 :=
  ⟨two_instance_zero_error, actual_two_instance_costs⟩

/-- Thus no scalar code, even nonlinear and fully informed, can reach
broadcast cost 3/2 for this example. -/
theorem scalar_broadcast_cost_gt_three_halves {S : Type*} [Fintype S] [DecidableEq S]
    (b : BitSource → S) (d1 d2 d3 : S → Pair → Bool)
    (h1 : ∀ s, d1 (b s) (side1 s) = demand1 s)
    (h2 : ∀ s, d2 (b s) (side2 s) = demand2 s)
    (h3 : ∀ s, d3 (b s) (side3 s) = demand3 s) :
    (3:ℝ) / 2 < Real.logb 2 (Fintype.card (Set.range b)) := by
  have hc : (3:ℝ) ≤ Fintype.card (Set.range b) := by
    exact_mod_cast three_le_scalar_broadcast_range b d1 d2 d3 h1 h2 h3
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (by norm_num : (0:ℝ) < 3) hc
  have hstrict := Real.logb_lt_logb (by norm_num : (1:ℝ) < 2)
    (by norm_num : (0:ℝ) < 8) (by norm_num : (8:ℝ) < 3^2)
  rw [logb_two_eight, Real.logb_pow] at hstrict
  norm_num at hstrict
  linarith

/-! ## Repeating the fixed scalar relay input

The fixed relay sees `(a,u,b,c)` and never sees `v`. The following proof
uses this restriction explicitly. It permits arbitrary nonlinear broadcast
and decoders at every blocklength.
-/
abbrev BitBlock (L : ℕ) := Fin L → Bool
abbrev RelayInput (L : ℕ) := BitBlock L × BitBlock L × BitBlock L × BitBlock L
def xorBlock {L : ℕ} (a b : BitBlock L) : BitBlock L := fun i => Bool.xor (a i) (b i)
def zeroBlock (L : ℕ) : BitBlock L := fun _ => false

/-- A broadcast of the fixed relay input is injective in `(a,u)` when
`b=c=0`. User 2 decodes `a` with `v=0`; user 3 decodes `a+u` with `v=u`.
The relay cannot distinguish these choices of the unobserved `v`. -/
theorem fixed_relay_injective {L : ℕ} {S : Type*}
    (b : RelayInput L → S)
    (d2 d3 : S → BitBlock L → BitBlock L → BitBlock L)
    (h2 : ∀ a u x c v, d2 (b (a,u,x,c)) x v = xorBlock a c)
    (h3 : ∀ a u x c v,
      d3 (b (a,u,x,c)) c (xorBlock u v) = xorBlock (xorBlock a x) u) :
    Function.Injective (fun w : BitBlock L × BitBlock L =>
      b (w.1,w.2,zeroBlock L,zeroBlock L)) := by
  intro w z heq
  have ha : w.1 = z.1 := by
    have h := congrArg (fun s => d2 s (zeroBlock L) (zeroBlock L)) heq
    dsimp only at h
    rw [h2, h2] at h
    funext i
    simpa [xorBlock, zeroBlock] using congrFun h i
  have hz (a u : BitBlock L) :
      d3 (b (a,u,zeroBlock L,zeroBlock L)) (zeroBlock L) (zeroBlock L) =
        xorBlock a u := by
    have h := h3 a u (zeroBlock L) (zeroBlock L) u
    have hu0 : xorBlock u u = zeroBlock L := by
      funext i
      exact Bool.xor_self (u i)
    have ha0 : xorBlock a (zeroBlock L) = a := by
      funext i
      exact Bool.xor_false (a i)
    simpa only [hu0, ha0] using h
  have hu : w.2 = z.2 := by
    have h := congrArg (fun s => d3 s (zeroBlock L) (zeroBlock L)) heq
    dsimp only at h
    rw [hz, hz, ha] at h
    funext i
    exact Bool.xor_right_inj.mp (congrFun h i)
  exact Prod.ext ha hu

/-- At least `4^L` attained broadcast messages are necessary when the paper's
fixed scalar relay tuple is repeated, even for nonlinear block broadcasts. -/
theorem fixed_relay_range_card_lower {L : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (b : RelayInput L → S)
    (d2 d3 : S → BitBlock L → BitBlock L → BitBlock L)
    (h2 : ∀ a u x c v, d2 (b (a,u,x,c)) x v = xorBlock a c)
    (h3 : ∀ a u x c v,
      d3 (b (a,u,x,c)) c (xorBlock u v) = xorBlock (xorBlock a x) u) :
    4^L ≤ Fintype.card (Set.range b) := by
  classical
  let f : BitBlock L × BitBlock L → Set.range b := fun w =>
    ⟨b (w.1,w.2,zeroBlock L,zeroBlock L), ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro w z h
    exact fixed_relay_injective b d2 d3 h2 h3 (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  simpa [BitBlock, Fintype.card_prod, Fintype.card_fun, ← mul_pow] using h

/-- Matching broadcast: `(a+b+c, a+b+c+u)` coordinate by coordinate. -/
def fixedBroadcast {L : ℕ} (w : RelayInput L) : BitBlock L × BitBlock L :=
  let t := xorBlock (xorBlock w.1 w.2.2.1) w.2.2.2
  (t, xorBlock t w.2.1)

theorem fixed_broadcast_decodes {L : ℕ} (a u x c : BitBlock L) :
    xorBlock (fixedBroadcast (a,u,x,c)).1 a = xorBlock x c ∧
    xorBlock (fixedBroadcast (a,u,x,c)).1 x = xorBlock a c ∧
    xorBlock (fixedBroadcast (a,u,x,c)).2 c = xorBlock (xorBlock a x) u := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;>
    simp [fixedBroadcast, xorBlock, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem fixed_broadcast_surjective (L : ℕ) :
    Function.Surjective (@fixedBroadcast L) := by
  intro ⟨x,y⟩
  refine ⟨(x, xorBlock x y, zeroBlock L, zeroBlock L), ?_⟩
  apply Prod.ext <;> funext i <;>
    simp [fixedBroadcast, xorBlock, zeroBlock, Bool.xor_assoc]

theorem fixed_broadcast_range_card (L : ℕ) :
    Fintype.card (Set.range (@fixedBroadcast L)) = 4^L := by
  simp [Set.range_eq_univ.mpr (fixed_broadcast_surjective L),
    BitBlock, Fintype.card_prod, Fintype.card_fun, ← mul_pow]

/-- The lower cardinality bound implies at least two bits per instance. -/
theorem fixed_relay_broadcast_cost_lower {L : ℕ} (hL : 0 < L)
    {S : Type*} [Fintype S] [DecidableEq S]
    (b : RelayInput L → S)
    (d2 d3 : S → BitBlock L → BitBlock L → BitBlock L)
    (h2 : ∀ a u x c v, d2 (b (a,u,x,c)) x v = xorBlock a c)
    (h3 : ∀ a u x c v,
      d3 (b (a,u,x,c)) c (xorBlock u v) = xorBlock (xorBlock a x) u) :
    2 ≤ Real.logb 2 (Fintype.card (Set.range b)) / L := by
  have hc : (4:ℝ)^L ≤ Fintype.card (Set.range b) := by
    exact_mod_cast fixed_relay_range_card_lower b d2 d3 h2 h3
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (pow_pos (by norm_num : (0:ℝ) < 4) L) hc
  rw [Real.logb_pow, logb_two_four] at hl
  have hpos : (0:ℝ) < L := by exact_mod_cast hL
  apply (le_div_iff₀ hpos).mpr
  nlinarith

theorem fixed_broadcast_cost (L : ℕ) (hL : 0 < L) :
    Real.logb 2 (Fintype.card (Set.range (@fixedBroadcast L))) / L = 2 := by
  rw [fixed_broadcast_range_card]
  push_cast
  rw [Real.logb_pow, logb_two_four]
  have hne : (L:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  exact mul_div_cancel_left₀ 2 hne

end UploadBroadcast.Examples
