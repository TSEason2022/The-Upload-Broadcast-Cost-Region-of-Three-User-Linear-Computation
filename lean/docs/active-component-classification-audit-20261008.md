# Actual active-residual component classification

Source: `TIT_LCBC_optimized.tex`, Table `tab:residues` (2365ff), the component definitions (2412ff), and the boundary paragraph (2786–2801). This is an assignment/classification result, not by itself the complete residual relay proposition.

## Actual inputs and outputs

`ActiveComponentClassification.active_residual_assignment` starts with an actual finite-dimensional operational task over its original finite field, genuine simultaneous-subspace indecomposability, side spanning, positive side excess, at least one active demand, and at least one non-full signal. It derives one of:

- an actual `R2PermutedMenus.pathPerm k`, a natural `n >= 1`, and `NonzeroFamilyRanks.Dimensions` for one of all eight nonzero-defect families;
- the actual `T1` boundary at natural index zero;
- the actual `T2` boundary at natural index zero;
- a linear equivalence of the original coefficient space under which the entire operational task is exactly `ResonantRelay.jordanTask K n`.

The Jordan library parameter `n` corresponds to the manuscript's positive block index `n+1`.

`ResidualComponentClassification.positive_excess_assignment` derives activity and the non-omniscience exclusion from `ResidualComponentAdditivity.ActiveResidual`; they are not additional input certificates. `residual_exhaustion` includes every zero-excess component as a separate alternative and proves there is no negative-excess active residual.

## No classification oracle

The nonzero-defect branch derives Tits value one through `Task.nonzero_defect_tits_one`, whose input is the actual configuration indecomposability. The integer table is converted into an actual arm permutation and a natural parameter. The zero-defect branch invokes the proved original-field regular classification, then turns its labeled configuration isomorphism into an equality of operational tasks under `Profile.mapTask`.

No theorem assumes `q_T = 1`, an absolutely indecomposable extension-field model, family membership, transversality, a rank/profile conclusion, or a desired relay. The numerical helper `exists_table_permutation` still has a Tits-one premise, but every source-facing assignment theorem discharges it.

## Low-index scope

O and H require natural index at least one. R0/R2 at zero are proved passive; R1/T3 at zero are proved all-omniscience. The passive regular endpoint is eliminated only after establishing a genuinely active demand. Crucially, T2 at zero is retained: the manuscript supplies a profile-preserving side-line relay for it, and it is not removed with the passive or omniscience endpoints.

## Verification

`verification/ActiveComponentClassificationAudit.lean` audits the actual family, indexed, low-index and regular-chart assignment theorems. The printed dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

The assignment modules do not yet alone imply source `thm:profiles`: that proposition additionally needs the exact boundary menus, existing nonzero-family relay menus, actual resonant relay transport and optimality, and the zero-excess full relay.
