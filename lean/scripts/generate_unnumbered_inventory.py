#!/usr/bin/env python3
"""Record review routing for every frozen displayed-equation inventory item.
This is a semantic review ledger, not a proof or a completeness certificate.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir', type=Path, required=True,
                    help='Private directory containing the matching frozen TIT_LCBC_optimized.tex')
parser.add_argument('--inventory-dir', type=Path,
                    help='Original inventories; defaults to source-dir when present, otherwise source-ledger/')
args = parser.parse_args()
SRC = args.source_dir.resolve()
INVENTORY = args.inventory_dir or (SRC if (SRC / 'claims_inventory.json').is_file() else ROOT / 'source-ledger')
source = (SRC / 'TIT_LCBC_optimized.tex').read_bytes()
claims = json.loads((INVENTORY / 'claims_inventory.json').read_text())
proofs = json.loads((INVENTORY / 'proof_blocks.json').read_text())
displays = json.loads((INVENTORY / 'displayed_equations.json').read_text())
coverage = json.loads((ROOT / 'coverage.json').read_text())
if hashlib.sha256(source).hexdigest() != coverage['source_sha256']:
    raise SystemExit('The supplied manuscript does not match the frozen coverage source hash.')

proof_owner = {
 876:'lem:five-cmi',937:'lem:omni-lift',1021:'thm:upload',1072:'thm:upload',
 1125:'lem:pis',1504:'thm:packing',1574:'lem:edge-identity',1624:'thm:endpoint',
 1729:'prop:stable',1827:'cor:scalar-budget',1843:'thm:intro-main',
 1943:'prop:active-pair',2000:'lem:active-empty-row',2033:'prop:exhaustion',
 2068:'lem:bridges',2164:'lem:zero-common-row-relay',2228:'lem:ck-omniscience',
 2339:'lem:base-field-components',2496:'lem:same-chart',2963:'thm:profiles',
 2978:'thm:packing',3028:'lem:edge-identity',3135:'lem:optimal-residual-sides',
 3168:'lem:binary-menu',3244:'lem:binary-additional-menus',3406:'lem:binary-integer-relay',
 3466:'prop:stable',3544:'lem:integer-lcbc-allocation',3591:'lem:column-reconciliation',
 3619:'prop:small-field-lcbc',3671:'lem:binary-common-complement',3686:'prop:binary-lcbc'
}
# Pure definitions are separated from assertions that require proof.
definition_lines = {
 193,229,324,367,384,392,397,442,455,460,563,622,643,667,
 796,810,816,824,1102,1155,1194,1214,1311,1421,1435,1463,1522,1529,1537,
 1546,1552,2311,2424,2454,2817,2889,3513,3527,3604
}
# A display outside a named statement/proof has an explicit semantic route.
standalone = {
 214:('U12','Examples.fixed_relay_broadcast_cost_lower'),
 403:('U02','Task.Code.exists_upload_only_decoder; Task.codeOfUploadOnly'),
 411:('U02','deterministic_condEntropy_zero; condEntropy_zero_of_factor'),
 418:('U02','entropy_div_log_le_logb_attainable; BroadcastOperational.entropy_le_cost'),
 427:('U02','LinearObservation.model_entropy_rank; model_condEntropy_rank; model_mutualInfo_rank'),
 471:('U03','general_broadcastOptimum_eq_rankBound; general_block_profile_attained'),
 575:('U04','Task.exists_pairKnown_charts; ResidualTaskAssembly.exists_canonical_chart'),
 638:('U04','ResidualTaskAssembly.privateTrim_fully_used'),
 693:('U04','ResidualTaskAssembly.tripodDimension_eq_stacked_rank'),
 756:('U04','CommonTripodAssembly.common_product_mapTask; PairOmniscienceAdapter.mapTask_combined'),
 764:('U04','CommonTripodAssembly.common_product_mapTask; PairOmniscienceAdapter.mapTask_combined'),
 976:('U02','ResidualUpload.gamma_rank; GlobalUploadConverse.code_omniscience_entropy_bound'),
 986:('U02','SignalBridge.private_slice_inverse'),
 1170:('U05','Profile.entry_directSum; FiniteRelayAssembly.entry_task'),
 1176:('U05','Profile.rankBound_directSum_le; task_general_broadcastOptimum_eq_rankBound'),
 1202:('U05','FiniteRelayAssembly.inducedRelay_entry'),
 1321:('U05','ActualPairCapacities.margin_nonneg'),
 1340:('U06','ActualPairCapacities; NonzeroSameChartOptimality; ResonantProfile'),
 1394:('U07','OmniscienceProfile.first_entry; OmniscienceProfile.second_entry; OmniscienceRelayProfile.entry_preserved'),
 1484:('U08','ActualPairCapacities'),
 1712:('U08','EdgeDeficits; OrientationRepairAllocation'),
 2023:('U04','ActualBlockGraph.G0_direct_sum; mixed_rank_additive; tripod_rank_additive; UploadParameterDirectSum.private_dimension_additive; IntrinsicUploadDirectSums.activePairRank_additive'),
 2052:('U04','CommonTripodRanks; ResidualRowPaperEndpoint'),
 2317:('U09','Structural.tits_squares'),
 2400:('U09','RootClassification.legal_translate; RootClassification.table_legal_thresholds'),
 2441:('U09','Structural; NonzeroDefectProfile'),
 2788:('U10','BoundaryComponentMenus.T1_all_permuted_choices; T2_permuted_preserving'),
 2852:('U10','ResonantEndomorphisms'),
 2861:('U10','ResonantEndomorphisms.scalar_plus_nilpotent; ResonantBaseChange.source_absolutely_indecomposable'),
 2907:('U10','ResonantProfile.jordan_full_firstProfile; jordan_full_secondProfile; ResonantRelay'),
 2923:('U10','ResonantProfile.full_firstProfile; ResonantProfile.full_secondProfile; CycleProfile'),
 2931:('U10','ResonantProfile pair-space and conditional-rank theorems')
}

def containing(line, records, textkey):
    for r in records:
        end = r['line'] + len(r[textkey].splitlines()) - 1
        if r['line'] <= line <= end:
            return r
    return None

rows = []
for item in displays:
    line = item['line']
    row = {'line': line, 'labels': item['labels'],
           'display_sha256': hashlib.sha256(item['latex'].encode()).hexdigest()}
    c = containing(line, claims, 'statement')
    p = containing(line, proofs, 'latex')
    if c:
        row.update(category='named_statement', owner=c['labels'][0])
    elif p:
        row.update(category='proof_step_of_named_claim', owner=proof_owner[p['line']])
    elif line in definition_lines:
        row.update(category='definition_or_construction_data', owner='not an independent correctness claim')
    elif line in standalone:
        owner, formal = standalone[line]
        row.update(category='standalone_unmapped' if owner.startswith('OPEN-') else 'standalone_mapped_for_review',
                   owner=owner, formal_route=formal)
    else:
        raise RuntimeError(f'Unrouted display at source line {line}: {item["labels"]}')
    rows.append(row)

# Manual semantic-review checkpoint, separate from the clean release build.
# All source-facing resonant/five-bit specializations passed independent review.
U12_SPECIALIZATION_COMPLETE = True
review_doc = 'docs/final-semantic-coverage-review-20261008.md'
all_named_complete = len(coverage['claims']) == 28 and all(
    c['status'] == 'reviewed_complete' for c in coverage['claims'])
review_complete = (all_named_complete and U12_SPECIALIZATION_COMPLETE and
                   coverage.get('unnumbered_and_external_dependencies_reviewed', False))

# Every numbered mathematical table is included, even when it belongs to an
# internal proof construction rather than an additional source conclusion.
table_routes = {
 'tab:menus': ('named_conclusion_table', 'thm:profiles; thm:packing',
   'ResidualProfiles.profiles; NonzeroSameChartPermutations.indexed_menu_table; Allocation.aggregate_selection_paper_coordinates'),
 'tab:residues': ('standalone_classification_table', 'U09; lem:base-field-components',
   'RootClassification.classification_iff; tableRow_sound; table_legal_thresholds; ActiveComponentClassification.active_residual_assignment'),
 'tab:primitive-flags': ('kernel_checked_literal_proof_construction', 'lem:same-chart',
   'LiteralPrimitiveTables: all seven literal A/B flag rows; actual signal_from_demands, side/signal column-span identities, full_rankConditions and full profiles over every field. Independent source/signature/axiom review in FinalLiteralConstructionReview20261008.'),
 'tab:primitive-relays': ('kernel_checked_literal_proof_construction', 'lem:same-chart',
   'LiteralPrimitiveTables: all ten exact common kernels, dimensions, local generation, relay feasibility, induced RankConditions/profiles, genuine side-relation values, designated-form annihilation and actual R2 wedge determinant. The external open-orbit theory is not claimed.'),
 'tab:binary-extra-menus': ('named_conclusion_table', 'lem:binary-additional-menus',
   'BinaryMenuOptimality.additional_optimal_menu; r2_optimal_menu; charge_le_actual_margin; r2_charge_le_actual_margin; BinaryAdditionalMenuPermutations')
}
numbered_tables = []
for match in re.finditer(r'\\begin\{(table\*?)\}(.*?)\\end\{\1\}', source.decode(), re.S):
    labels = re.findall(r'\\label\{([^}]+)\}', match.group(0))
    if len(labels) != 1 or labels[0] not in table_routes:
        raise RuntimeError(f'Unrouted numbered table: {labels}')
    label = labels[0]
    category, owner, route = table_routes[label]
    start = source.decode()[:match.start()].count('\n') + 1
    end = start + match.group(0).count('\n')
    numbered_tables.append({'label':label, 'source_lines':[start,end],
      'table_sha256':hashlib.sha256(match.group(0).encode()).hexdigest(),
      'category':category, 'owner':owner, 'formal_route':route,
      'status':'reviewed_literal_construction' if category == 'kernel_checked_literal_proof_construction' else 'reviewed_conclusion_table'})
if len(numbered_tables) != 5:
    raise RuntimeError(f'Expected all five frozen mathematical tables, got {len(numbered_tables)}')
if set(proof_owner) != {p['line'] for p in proofs}:
    raise RuntimeError('Proof routing does not match every frozen proof block')
if coverage['source_sha256'] != hashlib.sha256(source).hexdigest():
    raise RuntimeError('Coverage source hash does not match the frozen source')

closed_conclusions = [
 {'id':'OPEN-G0-DIRECT-SUM','source_lines':[2021,2028],
  'claim':'Literal componentwise B/G/G0 maps and each individual upload-rank sum.',
  'status':'reviewed_complete',
  'formal_route':'ActualBlockGraph.incidence_conjugacy; graph_conjugacy; G0_direct_sum; mixed_rank_additive; common_rank_additive; pure_rank_additive; tripod_rank_additive; UploadParameterDirectSum.private_dimension_additive; IntrinsicUploadDirectSums.activePairRank_additive',
  'audit':'verification/FinalDirectSumReview20261008.lean'},
 {'id':'OPEN-OPPOSITE-DEMAND-EXAMPLE','source_lines':[1182,1189],
  'claim':'Each opposite one-symbol task has D*=1; its actual direct sum has D*=1 with scalar x+y.',
  'status':'reviewed_complete',
  'formal_route':'OppositeDemandExample.strict_subadditivity_example',
  'audit':'verification/FinalStandaloneReview20261008.lean'},
 {'id':'CITED-ENTROPY-INSUFFICIENCY','source_lines':[434,436],
  'claim':'All original-observation subset entropies need not determine D*.',
  'status':'reviewed_complete_corrected_F5_witness',
  'formal_route':'CitedEntropyCounterexample.corrected_entropy_counterexample; equal_subset_entropies_distinct_operational_optima; joint_original_coefficients; original_side; original_demand; scalarSource_uniform',
  'audit':'verification/FinalEntropyWitnessReview20261008.lean',
  'source_correction':'The cited F3 pair has demand-triple ranks 3 versus 2 and is not entropy-identical. The frozen manuscript states an existential claim; the project proves it with the corrected F5 pair and leaves the source unchanged.'},
 {'id':'CITED-BINARY-FIELD-SIZE-NECESSITY','source_lines':[1804,1806],
  'claim':'The general scalar LCBC ceiling guarantee cannot be extended to every binary task.',
  'status':'reviewed_complete',
  'formal_route':'CitedBinaryFieldNecessity.signal_from_demands; broadcastOptimum_eq_one; scalar_broadcast_card; scalar_cost_ge_two; scalar_cost_gt_ceiling',
  'audit':'verification/FinalBinaryNecessityReview20261008.lean'}
]
if U12_SPECIALIZATION_COMPLETE:
    closed_conclusions.append({
      'id':'OPEN-RESONANT-UPLOAD-SPECIALIZATION','source_lines':[1277,2887],
      'claim':'U*(R_n)=3n+1 for every source n>=1; the literal five-bit task has U*=4 and an actual L=2 code at (4,3/2).',
      'status':'reviewed_complete',
      'formal_route':'ResonantUploadSpecializations.source_uploadOptimum; jordan_active; map_scalarCoordinates; binary_uploadOptimum; binary_joint_two',
      'audit':'verification/FinalResonantSpecializationReview20261008.lean'})

for row in rows:
    if row['category'] == 'standalone_mapped_for_review':
        row['category'] = 'reviewed_standalone_conclusion'
        row['semantic_review'] = review_doc
    elif row['category'] in ('named_statement', 'proof_step_of_named_claim'):
        row['owner_review_status'] = next(
            c['status'] for c in coverage['claims'] if c['id'] == row['owner'])

open_conclusions = [] if U12_SPECIALIZATION_COMPLETE else [
 {'id':'OPEN-RESONANT-UPLOAD-SPECIALIZATION','source_lines':[1277,2887],
  'claim':'The explicit R_n task has U*=3n+1, including exact U*=4 for the five-bit task.',
  'status':'The general optimality theorem and actual cycle activity are verified; an unconditional source-facing specialization is being exposed and checked.'}
]

ledger = {
 'source_sha256':hashlib.sha256(source).hexdigest(),
 'source_identity':'TIT_LCBC_optimized.tex',
 'scope':'All 125 displayed-equation inventory items; all 32 proof blocks; all five numbered mathematical tables; all 13 additional-obligation groups; the separately asserted counterexamples and model correspondence.',
 'semantic_review':review_doc,
 'full_unnumbered_review_complete':review_complete,
 'release_build_verification_is_separate':True,
 'definitions_are_not_claims':True,
 'proof_steps_in_named_proofs_are_routed_not_independently_promoted':True,
 'all_display_inventory_items_routed':len(rows)==125,
 'all_proof_inventory_items_routed':True,
 'all_numbered_tables_routed':True,
 'numbered_coverage_snapshot':{c['id']:c['status'] for c in coverage['claims']},
 'display_items':rows,
 'standalone_open_conclusions':open_conclusions,
 'standalone_closed_conclusions':closed_conclusions,
 'model_correspondence_not_exposed':[],
 'model_correspondence_reviewed':[
  {'id':'MODEL-COLUMN-REDUNDANCY','source_lines':[315,343],
   'claim':'Arbitrary original matrices, literal redundant-column removal, complement normalization and ambient restriction preserve every original blocklength region.',
   'status':'reviewed_complete',
   'formal_route':'MatrixFrontend.Data.achievableAt_eq; Code.toTask_upload_range; Code.toTask_broadcast_range; normalize_code; denormalize_code; normalize_linearCode; denormalize_linearCode; exists_retained_normalization; ambient_achievableAt_eq; ambient_linearCode_nonempty_iff',
   'audit':'verification/FinalMatrixFrontendReview20261008.lean'}
 ],
 'external_proof_replacement_boundary':{
   'policy':'The project proves each needed paper-specific endpoint without new mathematical axioms. General cited theories and historical/bibliographic claims are not advertised as entire project theorems. Alternative proofs may replace internal proof routes; stronger standalone conclusions are tracked separately.',
   'additional_trusted_mathematical_axioms':[],
   'accepted_standard_axioms':['propext','Classical.choice','Quot.sound'],
   'literal_primitive_and_theta_constructions':{
     'status':'independently_reviewed_kernel_checked',
     'source_lines':[2569,2667],
     'formal_route':'LiteralPrimitiveTables; LiteralThetaBlocks.R0_same_chart_profile; D.append_dimensions; D.append_conditional_ranks; D.append_profile',
     'audit':'verification/FinalLiteralConstructionReview20261008.lean',
     'scope':'Exact primitive matrices and theta blocks, including the actual one-copy append operation; no claim to formalize the external geometric transfer theory.'
   }
 },
 'external_assertions_not_independent_project_theorems':[
  {'source_lines':[2300,2328],'claim':'General Kac positive-root and affine Tits assertions.',
   'status':'needed_consequences_independently_proved; entire_external_theory_not_claimed',
   'formal_replacement':'TaskDecomposition.Task.source_base_field_components; E6RealRoots.nonnegative_realRoot_iff_norm_one; ActiveComponentClassification; ResidualComponentClassification'},
  {'source_lines':[2340,2356],'claim':'Splitting fields, finite-field real-root uniqueness and Krull–Schmidt proof route.',
   'status':'replaced_by_constructive_actual_field_extension_and_component_proofs',
   'formal_replacement':'TaskDecomposition.Task.source_base_field_components; tensorRep_indec_iff; FiniteComponentCoordinates.exists_operational_component_coordinates'},
  {'source_lines':[2444,2448],'claim':'Preinjectivity, self-extension vanishing and open/dense representation orbits.',
   'status':'entire_geometric_theory_not_claimed; needed_family_endpoints_proved_without_it',
   'formal_replacement':'NonzeroSameChartOptimality.same_chart_full_and_optimal_relay; NonzeroSameChartPermutations.same_chart_all_permuted_choices'},
  {'source_lines':[2807,2810],'claim':'Cited original-field resonant normal-form identification.',
   'status':'needed_identification_independently_constructed',
   'formal_replacement':'RegularResonantClassification.classification; ActiveComponentClassification.regular_assignment; ResonantEndomorphisms; ResonantBaseChange'}
 ],
 'numbered_tables':numbered_tables,
 'additional_groups':[
  {'id':'U01','inventory_item':1,'scope':'Arbitrary matrix frontend, column redundancy and ambient normalization','route':'MatrixTaskFrontend; MatrixTaskEndpoints; Model; Task.normalizationRetraction','status':'reviewed_complete'},
  {'id':'U02','inventory_item':2,'scope':'Upload-only equivalence, genuine entropy/alphabet inequalities and linear rank identities','route':'Model; EntropyCoding; LinearEntropy; GlobalUploadConverse','status':'reviewed_complete'},
  {'id':'U03','inventory_item':3,'scope':'Fully informed simulation, closure, operational LCBC formula and attaining code','route':'BroadcastRegion; GeneralBroadcastOptimum','status':'reviewed_complete'},
  {'id':'U04','inventory_item':4,'scope':'Actual normal forms, arbitrary-choice invariance, nonlinear passive/common reductions, individual rank direct sums and component costs','route':'ActiveReductionEndpoint; IntrinsicUploadInvariance; ActualBlockGraph; UploadParameterDirectSum; PassiveBroadcast; OriginalUploadTheorem; ResidualComponentAdditivity','status':'reviewed_complete'},
  {'id':'U05','inventory_item':5,'scope':'Profile additivity, strict/non-strict subadditivity and pair margins','route':'Profile; FiniteRelayAssembly; OppositeDemandExample; ActualPairCapacities','status':'reviewed_complete'},
  {'id':'U06','inventory_item':6,'scope':'Complete local menus, root/profile tables, binary choices and charges','route':'ResidualProfiles; NonzeroSameChartPermutations; BinaryMenuPermutations; BinaryAdditionalMenuPermutations; RootClassification; Task.binary_integer_relay (SourceMainTheorem)','status':'reviewed_complete; literal primitive proof tables separately kernel_checked'},
  {'id':'U07','inventory_item':7,'scope':'Omniscience profiles, arbitrary feasible-relay profile preservation and zero margins','route':'OmniscienceProfile; OmniscienceRelayProfile; ActualPairCapacities.omniscience_margin','status':'reviewed_complete'},
  {'id':'U08','inventory_item':8,'scope':'Orientation prices, maximal simultaneous physical edges, both optimal scalar cycle repairs','route':'EdgeProfile; EdgeExtraction; EdgeDeficits; CycleSourceEndpoint; ActualComponentCapacities; OrientationSlackCounts','status':'reviewed_complete'},
  {'id':'U09','inventory_item':9,'scope':'Tits identities, actual real-root membership, exhaustive family classification and legal thresholds','route':'Structural; RootClassification; E6RealRoots; BaseFieldComponents; ActiveComponentClassification; ResidualComponentClassification','status':'reviewed_complete; no general Kac axiom'},
  {'id':'U10','inventory_item':10,'scope':'Original-field coordinate families, actual ranks, resonant models and arbitrary extension indecomposability','route':'NonzeroSameChart; NonzeroFamilyRanks; BoundaryComponentMenus; ResonantEndomorphisms; ResonantBaseChange; ResonantProfile; LiteralPrimitiveTables; LiteralThetaBlocks; exact source endpoint audits','status':'reviewed_complete including literal primitive/theta constructions; external geometric transfer replaced by independent family proof'},
  {'id':'U11','inventory_item':11,'scope':'Waterfilling optimum/rounding, relation projections and deterministic coefficient coordination','route':'AllocationWaterfill; AllocationProfile; AllocationNat; ScalarIncidence; Coordination; BinaryRelationBridge; ScalarPaperEndpoints','status':'reviewed_complete'},
  {'id':'U12','inventory_item':12,'scope':'Literal five-bit example, U*=4, D*=3/2, exact two-instance code, all-block fixed-relay lower bound and nonlinear scalar obstruction','route':'Examples; BinaryOperationalTightness; ResonantUploadSpecializations.binary_uploadOptimum; ResonantUploadSpecializations.binary_joint_two','status':'reviewed_complete' if U12_SPECIALIZATION_COMPLETE else 'pending_explicit_upload_specialization'},
  {'id':'U13','inventory_item':13,'scope':'Operational half-integrality, doubling, closure, exact least linear blocklength and nonlinear tightness','route':'EndpointArithmetic; DoubleOperationalScaling; SourceMainTheorem; BinaryOperationalTightness','status':'reviewed_complete'}
 ]
}
path = ROOT / 'verification/unnumbered-coverage-inventory-20261008.json'
path.write_text(json.dumps(ledger,indent=2)+'\n')
print(f'Routed {len(rows)} displays, {len(proof_owner)} proof blocks, {len(numbered_tables)} tables, and 13 additional-obligation groups.')
print('Standalone open conclusions: '+(', '.join(x['id'] for x in open_conclusions) or 'none'))
print(f'Global unnumbered semantic review complete: {review_complete}; release verification remains separate.')
