import UploadBroadcast.PassiveComposition
import UploadBroadcast.BroadcastFiniteEndpoints

/-! Fully informed operational broadcast invariance under the actual passive
coefficient retractions used in original-task reduction. -/
namespace UploadBroadcast.PassiveRetraction
variable {K F V : Type*} [Field K] [AddCommGroup F] [Module K F]
  [AddCommGroup V] [Module K V]
  {T : Task K F} {R : Task K V} (r : PassiveRetraction T R)
  {L : ℕ} {S : Type*}

def deleteBlockBroadcast (c : BlockBroadcastCode T.A T.U L S) :
    BlockBroadcastCode R.A R.U L S where
  encode x := c.encode (x.comp r.project)
  decode i b a := (c.decode i b (a.comp (r.sideProject i))).comp (r.signalInclude i)
  zero_error x i := by
    have hA : (observe K V (R.A i) x).comp (r.sideProject i)=
        observe K F (T.A i) (x.comp r.project) := by
      ext a k
      change x (r.sideProject i a : V) k=x (r.project a) k
      rw [r.sideProject_coe]
    rw [hA,c.zero_error]
    ext u k
    change x (r.project (r.signalInclude i u : F)) k=x (u : V) k
    rw [r.signalInclude_coe]
    have h := LinearMap.congr_fun r.project_include (u : V)
    rw [show r.project (r.embed (u : V))=u from h]

def restoreBlockBroadcast (c : BlockBroadcastCode R.A R.U L S) :
    BlockBroadcastCode T.A T.U L S where
  encode x := c.encode (x.comp r.embed)
  decode i b a := (c.decode i b (a.comp (r.sideInclude i))).comp (r.signalProject i)+
    a.comp (r.localPart i)
  zero_error x i := by
    have hA : (observe K F (T.A i) x).comp (r.sideInclude i)=
        observe K V (R.A i) (x.comp r.embed) := by
      ext a k
      change x (r.sideInclude i a : F) k=x (r.embed a) k
      rw [r.sideInclude_coe]
    rw [hA,c.zero_error]
    ext u k
    change x (r.embed (r.signalProject i u : V)) k+x (r.localPart i u : F) k=x (u : F) k
    rw [r.signalProject_coe,←Pi.add_apply,←map_add,r.reconstruct]

private theorem log_image_mono {X Y Z : Type*} [Nonempty X] [Finite Z]
    (f : X→Z) (g : Y→Z) (h : Set.range f ⊆ Set.range g) (q : ℝ) (hq : 1<q) :
    Real.logb q (Nat.card (Set.range f)) ≤ Real.logb q (Nat.card (Set.range g)) := by
  apply Real.logb_le_logb_of_le hq
  · exact_mod_cast (Nat.card_pos (α:=Set.range f))
  · exact_mod_cast Nat.card_le_card_of_injective (Set.inclusion h) (Set.inclusion_injective h)

variable [Finite K]

theorem deleteBlockBroadcast_cost_le [Finite S] (c : BlockBroadcastCode T.A T.U L S) :
    (r.deleteBlockBroadcast c).cost ≤ c.cost := by
  have hr : Set.range (r.deleteBlockBroadcast c).encode ⊆ Set.range c.encode := by
    rintro _ ⟨x,rfl⟩
    exact ⟨x.comp r.project,rfl⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  exact log_image_mono _ _ hr _ (by exact_mod_cast (Finite.one_lt_card (α:=K)))

theorem restoreBlockBroadcast_cost_le [Finite S] (c : BlockBroadcastCode R.A R.U L S) :
    (r.restoreBlockBroadcast c).cost ≤ c.cost := by
  have hr : Set.range (r.restoreBlockBroadcast c).encode ⊆ Set.range c.encode := by
    rintro _ ⟨x,rfl⟩
    exact ⟨x.comp r.embed,rfl⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  exact log_image_mono _ _ hr _ (by exact_mod_cast (Finite.one_lt_card (α:=K)))

variable [FiniteDimensional K F] [FiniteDimensional K V]

include r in
/-- The actual nonlinear fully informed optimum survives passive deletion
and restoration over the original finite field. -/
theorem broadcastOptimum_eq : broadcastOptimum T.A T.U=broadcastOptimum R.A R.U := by
  obtain ⟨L,n,c,_,hL,_,hc⟩ := fullyInformed_one_two_or_four T.A T.U T.side_le_signal
  obtain ⟨M,m,d,_,hM,_,hd⟩ := fullyInformed_one_two_or_four R.A R.U R.side_le_signal
  apply le_antisymm
  · calc
      broadcastOptimum T.A T.U = Allocation.rawRankBound T.A T.U :=
        general_broadcastOptimum_eq_rankBound T.A T.U T.side_le_signal
      _ ≤ (r.restoreBlockBroadcast d).cost := (r.restoreBlockBroadcast d).rankBound_le_cost T.side_le_signal hM
      _ ≤ d.cost := r.restoreBlockBroadcast_cost_le d
      _ = broadcastOptimum R.A R.U := hd
  · calc
      broadcastOptimum R.A R.U = Allocation.rawRankBound R.A R.U :=
        general_broadcastOptimum_eq_rankBound R.A R.U R.side_le_signal
      _ ≤ (r.deleteBlockBroadcast c).cost := (r.deleteBlockBroadcast c).rankBound_le_cost R.side_le_signal hL
      _ ≤ c.cost := r.deleteBlockBroadcast_cost_le c
      _ = broadcastOptimum T.A T.U := hc

include r in
/-- Consequently the actual maximum fifteen-entry bound is invariant. -/
theorem rankBound_eq : Profile.rankBound T=Profile.rankBound R := by
  rw [←task_general_broadcastOptimum_eq_rankBound T,←task_general_broadcastOptimum_eq_rankBound R]
  exact r.broadcastOptimum_eq

end UploadBroadcast.PassiveRetraction
