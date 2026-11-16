import UploadBroadcast.CitedEntropyData
namespace UploadBroadcast.CitedEntropyCounterexample
open FiniteSubspaceCertificate
/-- All finite cardinality certificates needed by the fifteen-entry profile. -/
def firstConditional (t : K) (r : Fin 6) : Space (K := K) (V := V) :=
  let (i,j,_) := Profile.firstOrder r
  (side j).join ((signal t i).meet (signal t j))

def lastConditional (t : K) (r : Fin 6) : Space (K := K) (V := V) :=
  let (i,j,k) := Profile.firstOrder r
  (side k).join ((signal t k).meet ((signal t i).join (signal t j)))

def tripleConditional (t : K) (i : Three) : Space (K := K) (V := V) :=
  (side i).join (((signal t 0).meet (signal t 1)).meet (signal t 2))

def forkConditional (t : K) (i : Three) : Space (K := K) (V := V) :=
  (side i).join (((signal t i).meet (signal t (i+1))).join
    ((signal t i).meet (signal t (i+2))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem first_card : ∀ (t : Fin 2) r, (firstConditional (t.val+1) r).points.card = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair_meet_card : ∀ (t : Fin 2) r,
    ((signal (t.val+1) (Profile.firstOrder r).1).meet
      (signal (t.val+1) (Profile.firstOrder r).2.1)).points.card = 5 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triple_card : ∀ i, (tripleConditional 1 i).points.card = 25 ∧
    (tripleConditional 2 i).points.card = 5 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fork_card : ∀ (t : Fin 2) i, (forkConditional (t.val+1) i).points.card = 25 := by decide +kernel


end UploadBroadcast.CitedEntropyCounterexample
