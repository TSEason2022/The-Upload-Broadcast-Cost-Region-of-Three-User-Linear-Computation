import UploadBroadcast.ResidualUpload

/-! Convert the actual scalar local relay protocol into the manuscript's
Task.FiniteCode interface, with its proved operational upload-cost bound. -/
namespace UploadBroadcast.ResidualOperational
open Module
variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Remove the singleton block-coordinate index of a scalar source. -/
def scalarize : Source K F 1 →ₗ[K] (F →ₗ[K] K) where
  toFun x := (LinearMap.proj (0 : Fin 1)).comp x
  map_add' x y := by ext a; rfl
  map_smul' a x := by ext b; rfl

/-- Restore the singleton block-coordinate index. -/
def vectorize : (F →ₗ[K] K) →ₗ[K] Source K F 1 where
  toFun x := LinearMap.pi fun _ => x
  map_add' x y := by ext a j; rfl
  map_smul' a x := by ext b j; rfl

@[simp] theorem vectorize_scalarize (x : Source K F 1) : vectorize (scalarize x) = x := by
  ext a j
  fin_cases j
  rfl

@[simp] theorem scalarize_observe (A : Submodule K F) (x : Source K F 1) :
    scalarize (UploadBroadcast.observe K F A x) = (scalarize x).comp A.subtype := rfl

/-- A locally generated feasible relay supplies an actual scalar finite code
in the operational task model. Its attained-alphabet upload cost is no more
than the relay dimension. Every encoder, relay, and decoder is constructed
from the already proved linear scalar protocol over the original field. -/
theorem finiteCode_of_local_relay [Finite K] [FiniteDimensional K F]
    (task : Task K F) (P : Submodule K F)
    (hlocal : task.LocallyGenerated P) (hfeas : task.RelayFeasible P) :
    ∃ owner : Fin (finrank K P) → Three,
      ∃ code : task.FiniteCode 1 (fun i => {j // owner j = i} → K) (P →ₗ[K] K),
        code.toCode.uploadCost ≤ finrank K P := by
  classical
  obtain ⟨owner,enc,relay,dec,hlen,hzero⟩ :=
    ResidualUpload.exists_local_linear_upload_code task.A task.U P hlocal hfeas
  let e := fun i => (enc i).comp (scalarize (K := K) (F := task.A i))
  let c : task.Code 1 (fun i => {j // owner j = i} → K) (P →ₗ[K] K) :=
    { encode := fun i => e i
      broadcast := relay
      decode := fun i p a => vectorize (dec i (p,scalarize a))
      zero_error := by
        intro x i
        have hz := hzero (scalarize x) i
        have hv := congrArg (vectorize (K := K) (F := task.U i)) hz
        change vectorize (dec i (relay (fun j => e j (UploadBroadcast.observe K F (task.A j) x)),
          scalarize (UploadBroadcast.observe K F (task.A i) x))) = UploadBroadcast.observe K F (task.U i) x
        have hlift : vectorize ((scalarize x).comp (task.U i).subtype) =
            UploadBroadcast.observe K F (task.U i) x :=
          vectorize_scalarize (UploadBroadcast.observe K F (task.U i) x)
        simpa only [e,LinearMap.comp_apply,scalarize_observe] using hv.trans hlift }
  let fc : task.FiniteCode 1 (fun i => {j // owner j = i} → K) (P →ₗ[K] K) :=
    { toCode := c
      positive_blocklength := by decide
      finite_upload := fun _ => inferInstance
      finite_broadcast := Module.finite_of_finite K }
  refine ⟨owner,fc,?_⟩
  dsimp only [fc,c,Task.Code.uploadCost]
  rw [Nat.cast_one,div_one]
  simp_rw [linear_alphabet_log]
  have hdim (i : Three) : finrank K (LinearMap.range (e i)) ≤ Fintype.card {j // owner j = i} := by
    exact (LinearMap.range (e i)).finrank_le.trans_eq (by simp)
  have hh : (∑ i, (finrank K (LinearMap.range (e i)) : ℝ)) ≤
      ∑ i, (Fintype.card {j // owner j = i} : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast hdim i
  have hlen' : (∑ i, (Fintype.card {j // owner j = i} : ℝ)) = finrank K P := by
    exact_mod_cast hlen
  exact hh.trans_eq hlen'

end UploadBroadcast.ResidualOperational
