import UploadBroadcast.MatrixTaskFrontend
#check UploadBroadcast.MatrixFrontend.Data.finite_set_matrix
#print axioms UploadBroadcast.MatrixFrontend.Data.finite_set_matrix
example {K : Type*} {d : ℕ} (a : Set (Fin d → K)) (ha : a.Finite) :
    ∃ (m : ℕ) (V : Matrix (Fin d) (Fin m) K),
      Set.range V.col = a ∧ Function.Injective V.col :=
  UploadBroadcast.MatrixFrontend.Data.finite_set_matrix a ha
