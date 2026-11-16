import UploadBroadcast.ResidualOperational
import UploadBroadcast.BroadcastReindex
import UploadBroadcast.LinearCode

/-! Actual scalar linear upload/broadcast composition on a feasible locally
generated relay. All maps, including the final decoders, are constructed. -/
namespace UploadBroadcast.RelayLinearComposition
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- A scalar linear code on the relay's induced task yields linear decoders
for the original signals, using each original user's side information. -/
theorem decoder_lift (T : Task K F) (P : Submodule K F) (hP : T.RelayFeasible P)
    {n : ℕ} (c : ScalarBroadcastCode (fun i => (T.A i).comap P.subtype)
      (fun i => (T.U i).comap P.subtype) n) :
    ∃ d : ∀ i, ((Fin n → K) × (T.A i →ₗ[K] K)) →ₗ[K] (T.U i →ₗ[K] K),
      ∀ x i, d i (c.encode (dualObserve P x), dualObserve (T.A i) x) = dualObserve (T.U i) x := by
  have hk (i : Three) :
      LinearMap.ker ((c.encode.comp (dualObserve P)).prod (dualObserve (T.A i))) ≤
        LinearMap.ker (dualObserve (T.U i)) := by
    intro x hx
    have hh : (c.encode (dualObserve P x), dualObserve (T.A i) x) = (0,0) := hx
    have hb := congrArg Prod.fst hh
    have ha := congrArg Prod.snd hh
    dsimp only at hb ha
    have hpa : dualObserve ((T.A i).comap P.subtype) (dualObserve P x) = 0 := by
      ext a
      exact LinearMap.congr_fun ha ⟨(a : P),a.property⟩
    have hu := c.zero_error (dualObserve P x) i
    rw [hb,hpa,show ((0 : Fin n → K), (0 : (T.A i).comap P.subtype →ₗ[K] K)) = 0 from rfl,
      map_zero] at hu
    apply LinearMap.mem_ker.mpr
    ext u
    have hm : (u : F) ∈ T.A i ⊔ (T.U i ⊓ P) := by
      rw [← relay_decomposition (T.A i) (T.U i) P (T.side_le_signal i) (hP i)]
      exact u.property
    obtain ⟨a,ha',b,hb',he⟩ := Submodule.mem_sup.mp hm
    have ea := LinearMap.congr_fun ha ⟨a,ha'⟩
    have eb := (LinearMap.congr_fun hu ⟨⟨b,hb'.2⟩,hb'.1⟩).symm
    change x (u : F) = 0
    rw [← he,map_add]
    exact (congrArg₂ (· + ·) ea eb).trans (zero_add 0)
  choose d hd using fun i => factors_through_of_ker_le
    ((c.encode.comp (dualObserve P)).prod (dualObserve (T.A i))) (dualObserve (T.U i)) (hk i)
  exact ⟨d,fun x i => LinearMap.congr_fun (hd i) x⟩

/-- Original-field scalar linear code from an actual locally generated relay
and an actual scalar linear broadcast code for its induced task. -/
theorem exists_linear_code [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P) {n : ℕ}
    (c : ScalarBroadcastCode (fun i => (T.A i).comap P.subtype)
      (fun i => (T.U i).comap P.subtype) n) :
    ∃ r : Three → ℕ, ∃ d : T.LinearCode 1 r n,
      (∑ i, r i) = finrank K P ∧
      d.toCode.uploadCost ≤ finrank K P ∧ d.toCode.broadcastCost ≤ n := by
  classical
  obtain ⟨owner,enc,relay,hlen,hrelay⟩ :=
    ResidualUpload.exists_local_linear_uploads T.A P hlocal
  obtain ⟨dec,hdec⟩ := decoder_lift T P hfeas c
  let r : Three → ℕ := fun i => Fintype.card {j // owner j = i}
  let e : ∀ i, ({j // owner j = i} → K) ≃ₗ[K] (Fin (r i) → K) := fun i =>
    LinearEquiv.funCongrLeft K K (Fintype.equivFin _).symm
  let enc' := fun i => ((e i).toLinearMap.comp (enc i)).comp
    (ResidualOperational.scalarize (K := K) (F := T.A i))
  let assemble : (∀ i, Fin (r i) → K) →ₗ[K] (P →ₗ[K] K) :=
    relay.comp (LinearEquiv.piCongrRight (fun i => (e i).symm)).toLinearMap
  let broadcast := c.encode.comp assemble
  let decode := fun i => (ResidualOperational.vectorize (K := K) (F := T.U i)).comp
    ((dec i).comp ((LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)).prodMap
      (ResidualOperational.scalarize (K := K) (F := T.A i))))
  have he (x : Source K F 1) :
      assemble (fun i => enc' i (observe K F (T.A i) x)) =
        dualObserve P (ResidualOperational.scalarize x) := by
    change relay (fun i => (e i).symm (e i (enc i
      (ResidualOperational.scalarize (observe K F (T.A i) x))))) = _
    simp only [LinearEquiv.symm_apply_apply,ResidualOperational.scalarize_observe]
    exact hrelay _
  let d : T.LinearCode 1 r n :=
    { encode := enc'
      broadcast := broadcast
      decode := decode
      zero_error := by
        intro x i
        change ResidualOperational.vectorize (dec i
          (c.encode (assemble (fun j => enc' j (observe K F (T.A j) x))),
          ResidualOperational.scalarize (observe K F (T.A i) x))) = _
        rw [he,ResidualOperational.scalarize_observe]
        change ResidualOperational.vectorize (dec i
          (c.encode (dualObserve P (ResidualOperational.scalarize x)),
            dualObserve (T.A i) (ResidualOperational.scalarize x))) = _
        rw [hdec]
        exact ResidualOperational.vectorize_scalarize (observe K F (T.U i) x) }
  refine ⟨r,d,hlen,?_,?_⟩
  · rw [Task.LinearCode.uploadCost_eq_rank]
    simp only [Nat.cast_one,div_one]
    calc
      _ ≤ ∑ i, (r i : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast (LinearMap.range (d.encode i)).finrank_le.trans_eq (by simp)
      _ = finrank K P := by exact_mod_cast hlen
  · rw [Task.LinearCode.broadcastCost_eq_rank]
    simp only [Nat.cast_one,div_one]
    exact_mod_cast (LinearMap.range d.transmittedLinear).finrank_le.trans_eq (by simp)

/-- Complete original-field scalar composition for q ≥ 3. The remaining
geometric relay-selection problem is exposed as its actual local-generation
and feasibility hypotheses. -/
theorem exists_code_at_induced_ceiling [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P) (hq : 3 ≤ Nat.card K) :
    ∃ (r : Three → ℕ) (n : ℕ) (d : T.LinearCode 1 r n),
      (∑ i, r i) = finrank K P ∧ d.toCode.uploadCost ≤ finrank K P ∧
      d.toCode.broadcastCost ≤
        (⌈broadcastOptimum (fun i => (T.A i).comap P.subtype)
          (fun i => (T.U i).comap P.subtype)⌉ : ℤ) := by
  obtain ⟨n,c,hn,_⟩ := scalar_at_operational_ceiling
    (fun i => (T.A i).comap P.subtype) (fun i => (T.U i).comap P.subtype)
    (fun i => Submodule.comap_mono (T.side_le_signal i)) hq
  obtain ⟨r,d,hr,hu,hd⟩ := exists_linear_code T P hlocal hfeas c
  refine ⟨r,n,d,hr,hu,?_⟩
  have he : (n : ℝ) = (⌈broadcastOptimum (fun i => (T.A i).comap P.subtype)
      (fun i => (T.U i).comap P.subtype)⌉ : ℤ) := by exact_mod_cast hn
  exact hd.trans_eq he

/-- Binary version when the actual induced side spaces satisfy the paper's
separation condition after any permutation of the users. -/
theorem exists_binary_code_at_induced_ceiling [Fintype K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P) (hK : Fintype.card K = 2)
    (hspan : (⨆ i, (T.A i).comap P.subtype) = ⊤) (p : Equiv.Perm Three)
    (hsep : (T.A (p 0)).comap P.subtype ⊓
      ((T.A (p 1)).comap P.subtype ⊔ (T.A (p 2)).comap P.subtype) = ⊥) :
    ∃ (r : Three → ℕ) (n : ℕ) (d : T.LinearCode 1 r n),
      (∑ i, r i) = finrank K P ∧ d.toCode.uploadCost ≤ finrank K P ∧
      d.toCode.broadcastCost ≤
        (⌈broadcastOptimum (fun i => (T.A i).comap P.subtype)
          (fun i => (T.U i).comap P.subtype)⌉ : ℤ) := by
  obtain ⟨n,c,hn,_⟩ := binary_at_operational_ceiling_permuted hK
    (fun i => (T.A i).comap P.subtype) (fun i => (T.U i).comap P.subtype)
    (fun i => Submodule.comap_mono (T.side_le_signal i)) hspan p hsep
  obtain ⟨r,d,hr,hu,hd⟩ := exists_linear_code T P hlocal hfeas c
  refine ⟨r,n,d,hr,hu,?_⟩
  have he : (n : ℝ) = (⌈broadcastOptimum (fun i => (T.A i).comap P.subtype)
      (fun i => (T.U i).comap P.subtype)⌉ : ℤ) := by exact_mod_cast hn
  exact hd.trans_eq he

/-- Sending a basis of the whole relay gives an actual scalar linear code
over every field, without a field-size restriction or a broadcast optimum. -/
theorem full_relay_linear_code [Finite K] [FiniteDimensional K F]
    (T : Task K F) (P : Submodule K F) (hlocal : T.LocallyGenerated P)
    (hfeas : T.RelayFeasible P) :
    ∃ r : Three → ℕ, ∃ d : T.LinearCode 1 r (finrank K P),
      (∑ i, r i) = finrank K P ∧ d.toCode.uploadCost ≤ finrank K P ∧
      d.toCode.broadcastCost ≤ finrank K P := by
  let b := Module.finBasis K P
  have hs (i : Three) : (T.U i).comap P.subtype ≤
      (T.A i).comap P.subtype ⊔ Submodule.span K (Set.range b) := by
    rw [b.span_eq,sup_top_eq]
    exact le_top
  obtain ⟨c⟩ := scalarBroadcastCode_of_span
    (fun i => (T.A i).comap P.subtype) (fun i => (T.U i).comap P.subtype) b hs
  exact exists_linear_code T P hlocal hfeas c

end UploadBroadcast.RelayLinearComposition
