import OperatorKO7.Meta.RDRSSemanticNormalizedRawSyntax

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticNormalizedRawSyntaxReach

open OperatorKO7.RDRSSemanticNormalizedRawSyntax

#check @counterFirstLexRaw_R
#check @RawDirectMeasureShape
#check @compile
#check @InRawGrammar
#check @compile_inRawGrammar
#check @compileDirect

#check @counterProjection_orients
#check @counterPlusPayload_orients

#check @payloadProjection_lens_pump_witness
#check @constantMeasure_lens_pump_witness
#check @payloadPlusConst_lens_pump_witness
#check @payloadProjection_raw_payload_sensitive
#check @payloadPlusConst_raw_payload_sensitive
#check @constantMeasure_not_raw_payload_sensitive

#check @classifyRaw
#check @classifyRaw_total
#check @classifyRaw_no_temporary_unclassified

#check @blocked_shape_has_lens_pump_witness
#check @blocked_shape_raw_payload_sensitive
#check @blocked_shape_not_orients
#check @notDirect_shape_orients_or_payload_blind
#check @notDirect_rawSensitive_shape_orients

#check @RawGrammarClosed
#check @raw_grammar_closed
#check @rdrs_semantic_normalized_raw_syntax_anchor

end OperatorKO7.RDRSSemanticNormalizedRawSyntaxReach
