import GluingEPPA.Steiner.ChainValuation.All
import GluingEPPA.Steiner.ChainValuation.ChainRestrictionCore
import GluingEPPA.Steiner.ChainValuation.MaskRestriction
import GluingEPPA.Steiner.ChainValuation.CosetCycleCore
import GluingEPPA.Steiner.ChainValuation.Pushout
import GluingEPPA.Steiner.ChainValuation.GroupAttachment
import GluingEPPA.Steiner.ChainValuation.ChainExtend
import GluingEPPA.Steiner.ChainValuation.Matching
import GluingEPPA.Steiner.ChainValuation.BlockMatching
import GluingEPPA.Steiner.ChainValuation.ChainState
import GluingEPPA.Steiner.ChainValuation.ChainAttach
import GluingEPPA.Steiner.ChainValuation.LinkChain
import GluingEPPA.Steiner.ChainValuation.ChainTests
import GluingEPPA.Steiner.ChainValuation.AugmentedRecord
import GluingEPPA.Steiner.ChainValuation.AugmentedStep
import GluingEPPA.Steiner.ChainValuation.AugmentedInclusion
import GluingEPPA.Steiner.ChainValuation.ParameterizedFamily
import GluingEPPA.Steiner.ChainValuation.WordAction
import GluingEPPA.Steiner.ChainValuation.ChainIndex
import GluingEPPA.Steiner.ChainValuation.SeparatedChains

#print axioms GluingEPPA.Steiner.ChainValuation.self_mem_leftCoset
#print axioms GluingEPPA.Steiner.ChainValuation.leftCoset_eq_of_mem
#print axioms GluingEPPA.Steiner.ChainValuation.leftCoset_inter_of_mem
#print axioms GluingEPPA.Steiner.ChainValuation.mask_coset_inter
#print axioms GluingEPPA.Steiner.ChainValuation.reflection_coordinate
#print axioms GluingEPPA.Steiner.EdgeGraph.chain_walkValue_mem
#print axioms GluingEPPA.Steiner.EdgeGraph.chain_reflection_witness
#print axioms GluingEPPA.Steiner.EdgeGraph.chainComponentImage_distinguished
#print axioms GluingEPPA.Steiner.EdgeGraph.chainComponentImage_edge
#print axioms GluingEPPA.Steiner.EdgeGraph.chainComponentImage_word
#print axioms GluingEPPA.Steiner.EdgeGraph.chain_componentWord_internal
#print axioms GluingEPPA.Steiner.EdgeGraph.chain_word_map_value
#print axioms GluingEPPA.Steiner.EdgeGraph.chain_reflection_from_records
#print axioms GluingEPPA.Steiner.EdgeGraph.chain_coset_component_reflection

#print axioms GluingEPPA.Steiner.ChainValuation.attachment_same_intersection_coset
#print axioms GluingEPPA.Steiner.ChainValuation.attachment_no_merge
#print axioms GluingEPPA.Steiner.ChainValuation.restricted_attachments_disjoint

#print axioms GluingEPPA.Steiner.ChainValuation.mask_attachment_piece
#print axioms GluingEPPA.Steiner.ChainValuation.mask_triple_intersection
#print axioms GluingEPPA.Steiner.ChainValuation.mask_attachment_no_merge

#print axioms GluingEPPA.Steiner.ChainValuation.separated_link_not_le
#print axioms GluingEPPA.Steiner.ChainValuation.separated_link_not_ge

#print axioms GluingEPPA.Steiner.ChainValuation.pushoutInl_injective
#print axioms GluingEPPA.Steiner.ChainValuation.pushoutInr_injective
#print axioms GluingEPPA.Steiner.ChainValuation.pushoutInl_eq_inr_iff
#print axioms GluingEPPA.Steiner.ChainValuation.pushout_attachment

#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.value_cons
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.letter_involutive
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.generator_involutive
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.forget_valuation
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.valuation_test_coordinate

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.AugmentedStep.forget_edge

#print axioms GluingEPPA.Steiner.ChainValuation.attachLeft_injective
#print axioms GluingEPPA.Steiner.ChainValuation.group_attachment_transition
#print axioms GluingEPPA.Steiner.ChainValuation.group_attachment_overlap_iff

#print axioms GluingEPPA.Steiner.ChainValuation.attachInto_injective
#print axioms GluingEPPA.Steiner.ChainValuation.chainExtend_old_injective
#print axioms GluingEPPA.Steiner.ChainValuation.chainExtend_new_injective
#print axioms GluingEPPA.Steiner.ChainValuation.chainExtend_overlap_iff

#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.component_coordinate_eq_of_value_eq
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.component_record_of_word_eq

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.parameterizedFamily_step
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.parameterizedFamily_generated
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.parameterizedFamily_square

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.chainLength_le
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.chainLength_pos

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.separatedList_short

#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.coordinateHom_generator
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.inclusion_word
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.inclusion_injective
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.forget_inclusion
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.inclusion_replacement

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm_append
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.wordActionValue_word
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.wordRightAction_edge

#print axioms GluingEPPA.Steiner.ChainValuation.Matching.next_eq_of_rel
#print axioms GluingEPPA.Steiner.ChainValuation.Matching.next_involutive
#print axioms GluingEPPA.Steiner.ChainValuation.Matching.perm_eq_of_rel
#print axioms GluingEPPA.Steiner.ChainValuation.Matching.perm_fixed_of_none

#print axioms GluingEPPA.Steiner.ChainValuation.blockMatching_perm_apply
#print axioms GluingEPPA.Steiner.ChainValuation.blockMatching_perm_involutive

#print axioms GluingEPPA.Steiner.ChainValuation.GroupBlock.matching_perm
#print axioms GluingEPPA.Steiner.ChainValuation.GroupBlock.matching_none
#print axioms GluingEPPA.Steiner.ChainValuation.ChainState.first_perm

#print axioms GluingEPPA.Steiner.ChainValuation.cross_endpoint
#print axioms GluingEPPA.Steiner.ChainValuation.extendedMatching

#print axioms GluingEPPA.Steiner.ChainValuation.range_eq_leftCoset_one
#print axioms GluingEPPA.Steiner.ChainValuation.translated_range_eq_leftCoset

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.left_injective
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.right_injective
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.shared_edge

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.separatedList_three_iff

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.separatedList_three_iff

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.rawChain_list_nonempty
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.chainPerm_involutive
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.chainPerm_square

#print axioms GluingEPPA.Steiner.ChainValuation.restrictedAttachment_old_unique
#print axioms GluingEPPA.Steiner.ChainValuation.restrictedAttachment_new_unique

#print axioms GluingEPPA.Steiner.ChainValuation.Matching.quotient_eq_iff
#print axioms GluingEPPA.Steiner.ChainValuation.Matching.inl_component_injective
#print axioms GluingEPPA.Steiner.ChainValuation.Matching.inr_component_injective
#print axioms GluingEPPA.Steiner.ChainValuation.restrictedPiece_old_injective
#print axioms GluingEPPA.Steiner.ChainValuation.restrictedPiece_new_injective

#print axioms GluingEPPA.Steiner.ChainValuation.twoGroupAttachment_old_unique
#print axioms GluingEPPA.Steiner.ChainValuation.twoGroupAttachment_new_unique
#print axioms GluingEPPA.Steiner.ChainValuation.twoGroup_old_components_injective
#print axioms GluingEPPA.Steiner.ChainValuation.twoGroup_new_components_injective

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.inclusion_comp
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.projector_edge
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.mem_range_iff_projector
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.projector_inter
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.range_mono
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.range_inter

#print axioms GluingEPPA.Steiner.ChainValuation.comap_range_of_exact_intersection
#print axioms GluingEPPA.Steiner.ChainValuation.two_block_pullbacks_agree

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.projector_natural
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.comap_range

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.mask_pullbacks_agree

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.AugmentedStep.inclusion_edge
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.AugmentedStep.deletion_edge
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.AugmentedStep.inclusion_replace

#print axioms GluingEPPA.Steiner.ChainValuation.differenceProduct_to_last
#print axioms GluingEPPA.Steiner.ChainValuation.differenceProduct_cycle
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.valuation_one_test_fixed
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.moved_test_implies_nontrivial
#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.impossible_identity_cycle_test

#print axioms GluingEPPA.Steiner.ChainValuation.outside_exit_not_new
#print axioms GluingEPPA.Steiner.ChainValuation.outside_last_not_new
#print axioms GluingEPPA.Steiner.ChainValuation.outside_last_propagates

#print axioms GluingEPPA.Steiner.ChainValuation.TailAnchor.start
#print axioms GluingEPPA.Steiner.ChainValuation.TailAnchor.extend

#print axioms GluingEPPA.Steiner.ChainValuation.lastBlock_word
#print axioms GluingEPPA.Steiner.ChainValuation.old_edge_survives
#print axioms GluingEPPA.Steiner.ChainValuation.old_edge_survives_perm

#print axioms GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.testValue_eq_testWordPerm

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.inclusion_range_congr

#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.equivariantCover_word
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm_eq_of_equivariantCover
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation.rightAction_of_equivariantCover_edge

#print axioms GluingEPPA.Steiner.ChainValuation.attachment_fiber_coset
#print axioms GluingEPPA.Steiner.ChainValuation.two_group_attachment_fiber
#print axioms GluingEPPA.Steiner.ChainValuation.two_group_attachment_mem_iff
#print axioms GluingEPPA.Steiner.ChainValuation.attachment_intersection_exact
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.restrictedLink_fibre_mem_iff
#print axioms GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.restrictedLink_fibre_inter

#print axioms GluingEPPA.Steiner.ChainValuation.LayerMatch.root_le
#print axioms GluingEPPA.Steiner.ChainValuation.LayerMatch.backward_same
#print axioms GluingEPPA.Steiner.ChainValuation.LayerMatch.root_injective
#print axioms GluingEPPA.Steiner.ChainValuation.LayerMatch.root_of_connected
#print axioms GluingEPPA.Steiner.ChainValuation.LayerMatch.connected_same_layer
