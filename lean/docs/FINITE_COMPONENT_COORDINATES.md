# Actual finite component coordinates

`FiniteComponentCoordinates.exists_operational_component_coordinates` constructs a finite family of original coefficient subspaces and an actual linear equivalence from their dependent product to the original ambient space. Every factor is genuinely indecomposable. The component side and signal spaces are exactly the inverse images under the original subspace inclusions; feasibility is inherited through an actual coordinate projection. Mapping the product task back by the equivalence gives the original task literally.

The proof uses the independently proved finite-dimensional simultaneous decomposition. Its list of summands spans each of the six designated subspaces and has the exact ambient dimension sum. The explicit sum map is therefore surjective and injective. No product chart, profile identity, or representation classification is assumed.

The construction does not by itself prove that components are active residual, classify their families, or establish upload additivity. Those obligations remain separate.

Build: `source scripts/env.sh && lake build UploadBroadcast.FiniteComponentCoordinates`.
Audit: `lake env lean scripts/AuditFiniteComponentCoordinates.lean`.
All audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
