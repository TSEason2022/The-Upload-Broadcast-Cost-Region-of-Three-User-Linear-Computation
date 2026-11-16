import UploadBroadcast.CitedEntropyData

/-! Literal correspondence between the independent coordinate source and the
coefficient-space Task source used by the operational optimum theorem. -/
namespace UploadBroadcast.CitedEntropyCounterexample
open FiniteSubspaceCertificate MeasureTheory ProbabilityTheory
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

/-- The actual one-instance source matrix, viewed as evaluation on coefficients. -/
def scalarSource (x : V) : Source K V 1 where
  toFun v _ := x.1*v.1 + x.2.1*v.2.1 + x.2.2*v.2.2
  map_add' := by intro v w; ext l; simp; ring
  map_smul' := by intro c v; ext l; simp; ring

theorem scalarSource_injective : Function.Injective scalarSource := by
  intro x y h
  have h0 := congrArg (fun f : Source K V 1 => f (1,0,0) 0) h
  have h1 := congrArg (fun f : Source K V 1 => f (0,1,0) 0) h
  have h2 := congrArg (fun f : Source K V 1 => f (0,0,1) 0) h
  simp only [scalarSource,LinearMap.coe_mk,AddHom.coe_mk,mul_one,mul_zero,
    add_zero,zero_add] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem scalarSource_surjective : Function.Surjective scalarSource := by
  intro f
  refine ⟨(f (1,0,0) 0,f (0,1,0) 0,f (0,0,1) 0), ?_⟩
  apply LinearMap.ext
  intro v
  funext l
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  change f (1,0,0) 0 * v.1 + f (0,1,0) 0 * v.2.1 +
    f (0,0,1) 0 * v.2.2 = f v 0
  have hv : v = v.1 • (1,0,0) + v.2.1 • (0,1,0) + v.2.2 • (0,0,1) := by
    ext <;> simp
  conv_rhs => rw [hv]
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- These are exactly the six original variables, rather than six bundled signals. -/
theorem joint_original_coefficients (t : K) (s : Fin 6 → Bool) (x : V) (i : Fin 6) :
    joint t s x i = if s i then scalarSource x (vectors t i) 0 else 0 := by
  fin_cases i <;> simp [joint,scalarSource,vectors]
  split_ifs <;> ring

/-- The task has the same side observations and respective original demands. -/
theorem task_signal_eq (t : K) (i : Three) :
    (task t).U i = (side i).submodule ⊔ (demand t i).submodule := by
  exact Space.submodule_join _ _

def sideCoefficient (i : Three) : (task (1:K)).A i :=
  ⟨vectors 1 i.castSucc.castSucc.castSucc, by
    change _ ∈ Finset.univ.image (fun c : K => c • vectors 1 i.castSucc.castSucc.castSucc)
    exact Finset.mem_image.mpr ⟨(1:K),Finset.mem_univ _,one_smul K _⟩⟩

def demandCoefficient (t : K) (i : Three) : (task t).U i :=
  ⟨vectors t (⟨i.val+3,by omega⟩ : Fin 6), by
    rw [task_signal_eq]
    apply (show (demand t i).submodule ≤ _ from le_sup_right)
    change _ ∈ Finset.univ.image (fun c : K => c • vectors t (⟨i.val+3,by omega⟩ : Fin 6))
    exact Finset.mem_image.mpr ⟨(1:K),Finset.mem_univ _,one_smul K _⟩⟩

/-- Evaluating a side-space observation returns the corresponding original side variable. -/
theorem original_side (t : K) (x : V) (i : Three) :
    observe K V ((task t).A i) (scalarSource x) (sideCoefficient i) 0 =
      ![x.1,x.2.1,x.2.2] i := by
  fin_cases i <;> simp [observe,scalarSource,sideCoefficient,vectors]

/-- Evaluating the demanded coefficient returns B+C, A+C, or A+tB, respectively. -/
theorem original_demand (t : K) (x : V) (i : Three) :
    observe K V ((task t).U i) (scalarSource x) (demandCoefficient t i) 0 =
      ![x.2.1+x.2.2,x.1+x.2.2,x.1+t*x.2.1] i := by
  fin_cases i <;> simp [observe,scalarSource,demandCoefficient,vectors]
  ring


/-- This coordinate encoding is linear, so uniform independent coordinates
induce exactly the uniform measure on the actual model source. -/
def scalarSourceLinear : V →ₗ[K] Source K V 1 where
  toFun := scalarSource
  map_add' := by
    intro x y; apply LinearMap.ext; intro v; funext l; simp [scalarSource]; ring
  map_smul' := by
    intro c x; apply LinearMap.ext; intro v; funext l; simp [scalarSource]; ring

local instance modelMeasurableV : MeasurableSpace V := ⊤
local instance modelDiscreteV : DiscreteMeasurableSpace V := ⟨fun _ => trivial⟩

theorem scalarSource_uniform : ProbabilityTheory.IsUniform Set.univ scalarSource
    (uniformOn (Set.univ : Set V)) := by
  have h := linear_isUniform scalarSourceLinear
  have hr : Set.range scalarSourceLinear = Set.univ :=
    Set.range_eq_univ.mpr scalarSource_surjective
  rw [hr] at h
  exact h

end UploadBroadcast.CitedEntropyCounterexample
