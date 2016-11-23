type pointer = int
type source_location = {
  ?file <ocaml mutable> : string option;
  ?line <ocaml mutable> : int option;
  ?column <ocaml mutable> : int option;
} <ocaml field_prefix="sl_" validator="Clang_ast_visit.visit_source_loc">
type source_range = (source_location * source_location)
type opt_type = [Type of string | NoType]
type qual_type = {
  type_ptr : type_ptr;
  ~is_const : bool;
} <ocaml field_prefix="qt_">
type named_decl_info = {
  name : string;
  qual_name : string list;
} <ocaml field_prefix="ni_">
type decl_ref = {
  kind : decl_kind;
  decl_pointer : pointer;
  ?name : named_decl_info option;
  ~is_hidden : bool;
  ?type_ptr : type_ptr option
} <ocaml field_prefix="dr_">
type decl_kind = [
| AccessSpec
| Block
| Captured
| ClassScopeFunctionSpecialization
| Empty
| ExternCContext
| FileScopeAsm
| Friend
| FriendTemplate
| Import
| LinkageSpec
| Named
| Label
| Namespace
| NamespaceAlias
| ObjCCompatibleAlias
| ObjCContainer
| ObjCCategory
| ObjCImpl
| ObjCCategoryImpl
| ObjCImplementation
| ObjCInterface
| ObjCProtocol
| ObjCMethod
| ObjCProperty
| Template
| BuiltinTemplate
| RedeclarableTemplate
| ClassTemplate
| FunctionTemplate
| TypeAliasTemplate
| VarTemplate
| TemplateTemplateParm
| Type
| Tag
| Enum
| Record
| CXXRecord
| ClassTemplateSpecialization
| ClassTemplatePartialSpecialization
| TemplateTypeParm
| TypedefName
| ObjCTypeParam
| TypeAlias
| Typedef
| UnresolvedUsingTypename
| Using
| UsingDirective
| UsingShadow
| ConstructorUsingShadow
| Value
| Binding
| Declarator
| Field
| ObjCAtDefsField
| ObjCIvar
| Function
| CXXMethod
| CXXConstructor
| CXXConversion
| CXXDestructor
| MSProperty
| NonTypeTemplateParm
| Var
| Decomposition
| ImplicitParam
| OMPCapturedExpr
| ParmVar
| VarTemplateSpecialization
| VarTemplatePartialSpecialization
| EnumConstant
| IndirectField
| OMPDeclareReduction
| UnresolvedUsingValue
| OMPThreadPrivate
| ObjCPropertyImpl
| PragmaComment
| PragmaDetectMismatch
| StaticAssert
| TranslationUnit
]
#define decl_context_tuple decl list * decl_context_info
type decl_context_info = {
  ~has_external_lexical_storage : bool;
  ~has_external_visible_storage : bool
} <ocaml field_prefix="dci_">
type lookups = {
  decl_ref : decl_ref;
  ?primary_context_pointer : pointer option;
  lookups : lookup list;
  ~has_undeserialized_decls : bool;
} <ocaml field_prefix="lups_">
type lookup = {
  decl_name : string;
  decl_refs : decl_ref list;
} <ocaml field_prefix="lup_">
type attribute = [
| FallThroughAttr of attribute_info
| SwiftContextAttr of attribute_info
| SwiftErrorResultAttr of attribute_info
| SwiftIndirectResultAttr of attribute_info
| AnnotateAttr of attribute_info
| CFConsumedAttr of attribute_info
| CarriesDependencyAttr of attribute_info
| NSConsumedAttr of attribute_info
| PassObjectSizeAttr of attribute_info
| AMDGPUNumSGPRAttr of attribute_info
| AMDGPUNumVGPRAttr of attribute_info
| ARMInterruptAttr of attribute_info
| AcquireCapabilityAttr of attribute_info
| AcquiredAfterAttr of attribute_info
| AcquiredBeforeAttr of attribute_info
| AlignMac68kAttr of attribute_info
| AlignedAttr of attribute_info
| AlwaysInlineAttr of attribute_info
| AnalyzerNoReturnAttr of attribute_info
| AnyX86InterruptAttr of attribute_info
| ArcWeakrefUnavailableAttr of attribute_info
| ArgumentWithTypeTagAttr of attribute_info
| AsmLabelAttr of attribute_info
| AssertCapabilityAttr of attribute_info
| AssertExclusiveLockAttr of attribute_info
| AssertSharedLockAttr of attribute_info
| AssumeAlignedAttr of attribute_info
| AvailabilityAttr of attribute_info
| BlocksAttr of attribute_info
| C11NoReturnAttr of attribute_info
| CDeclAttr of attribute_info
| CFAuditedTransferAttr of attribute_info
| CFReturnsNotRetainedAttr of attribute_info
| CFReturnsRetainedAttr of attribute_info
| CFUnknownTransferAttr of attribute_info
| CUDAConstantAttr of attribute_info
| CUDADeviceAttr of attribute_info
| CUDAGlobalAttr of attribute_info
| CUDAHostAttr of attribute_info
| CUDAInvalidTargetAttr of attribute_info
| CUDALaunchBoundsAttr of attribute_info
| CUDASharedAttr of attribute_info
| CXX11NoReturnAttr of attribute_info
| CallableWhenAttr of attribute_info
| CapabilityAttr of attribute_info
| CapturedRecordAttr of attribute_info
| CleanupAttr of attribute_info
| ColdAttr of attribute_info
| CommonAttr of attribute_info
| ConstAttr of attribute_info
| ConstructorAttr of attribute_info
| ConsumableAttr of attribute_info
| ConsumableAutoCastAttr of attribute_info
| ConsumableSetOnReadAttr of attribute_info
| DLLExportAttr of attribute_info
| DLLImportAttr of attribute_info
| DeprecatedAttr of attribute_info
| DestructorAttr of attribute_info
| DisableTailCallsAttr of attribute_info
| EmptyBasesAttr of attribute_info
| EnableIfAttr of attribute_info
| ExclusiveTrylockFunctionAttr of attribute_info
| FastCallAttr of attribute_info
| FinalAttr of attribute_info
| FlagEnumAttr of attribute_info
| FlattenAttr of attribute_info
| FormatAttr of attribute_info
| FormatArgAttr of attribute_info
| GNUInlineAttr of attribute_info
| GuardedByAttr of attribute_info
| GuardedVarAttr of attribute_info
| HotAttr of attribute_info
| IBActionAttr of attribute_info
| IBOutletAttr of attribute_info
| IBOutletCollectionAttr of attribute_info
| InitPriorityAttr of attribute_info
| IntelOclBiccAttr of attribute_info
| InternalLinkageAttr of attribute_info
| LTOVisibilityPublicAttr of attribute_info
| LayoutVersionAttr of attribute_info
| LockReturnedAttr of attribute_info
| LocksExcludedAttr of attribute_info
| MSABIAttr of attribute_info
| MSInheritanceAttr of attribute_info
| MSNoVTableAttr of attribute_info
| MSP430InterruptAttr of attribute_info
| MSStructAttr of attribute_info
| MSVtorDispAttr of attribute_info
| MaxFieldAlignmentAttr of attribute_info
| MayAliasAttr of attribute_info
| MinSizeAttr of attribute_info
| Mips16Attr of attribute_info
| MipsInterruptAttr of attribute_info
| NSConsumesSelfAttr of attribute_info
| NSReturnsAutoreleasedAttr of attribute_info
| NSReturnsNotRetainedAttr of attribute_info
| NSReturnsRetainedAttr of attribute_info
| NakedAttr of attribute_info
| NoAliasAttr of attribute_info
| NoCommonAttr of attribute_info
| NoDebugAttr of attribute_info
| NoDuplicateAttr of attribute_info
| NoInlineAttr of attribute_info
| NoInstrumentFunctionAttr of attribute_info
| NoMips16Attr of attribute_info
| NoReturnAttr of attribute_info
| NoSanitizeAttr of attribute_info
| NoSplitStackAttr of attribute_info
| NoThreadSafetyAnalysisAttr of attribute_info
| NoThrowAttr of attribute_info
| NonNullAttr of attribute_info
| NotTailCalledAttr of attribute_info
| OMPCaptureNoInitAttr of attribute_info
| OMPThreadPrivateDeclAttr of attribute_info
| ObjCBridgeAttr of attribute_info
| ObjCBridgeMutableAttr of attribute_info
| ObjCBridgeRelatedAttr of attribute_info
| ObjCExceptionAttr of attribute_info
| ObjCExplicitProtocolImplAttr of attribute_info
| ObjCIndependentClassAttr of attribute_info
| ObjCMethodFamilyAttr of attribute_info
| ObjCNSObjectAttr of attribute_info
| ObjCPreciseLifetimeAttr of attribute_info
| ObjCRequiresPropertyDefsAttr of attribute_info
| ObjCRequiresSuperAttr of attribute_info
| ObjCReturnsInnerPointerAttr of attribute_info
| ObjCRootClassAttr of attribute_info
| OpenCLKernelAttr of attribute_info
| OpenCLUnrollHintAttr of attribute_info
| OptimizeNoneAttr of attribute_info
| OverrideAttr of attribute_info
| OwnershipAttr of attribute_info
| PackedAttr of attribute_info
| ParamTypestateAttr of attribute_info
| PascalAttr of attribute_info
| PcsAttr of attribute_info
| PreserveAllAttr of attribute_info
| PreserveMostAttr of attribute_info
| PtGuardedByAttr of attribute_info
| PtGuardedVarAttr of attribute_info
| PureAttr of attribute_info
| ReleaseCapabilityAttr of attribute_info
| ReqdWorkGroupSizeAttr of attribute_info
| RequiresCapabilityAttr of attribute_info
| RestrictAttr of attribute_info
| ReturnTypestateAttr of attribute_info
| ReturnsNonNullAttr of attribute_info
| ReturnsTwiceAttr of attribute_info
| ScopedLockableAttr of attribute_info
| SectionAttr of attribute_info
| SelectAnyAttr of attribute_info
| SentinelAttr of attribute_info
| SetTypestateAttr of attribute_info
| SharedTrylockFunctionAttr of attribute_info
| StdCallAttr of attribute_info
| SwiftCallAttr of attribute_info
| SysVABIAttr of attribute_info
| TLSModelAttr of attribute_info
| TargetAttr of attribute_info
| TestTypestateAttr of attribute_info
| ThisCallAttr of attribute_info
| TransparentUnionAttr of attribute_info
| TryAcquireCapabilityAttr of attribute_info
| TypeTagForDatatypeAttr of attribute_info
| TypeVisibilityAttr of attribute_info
| UnavailableAttr of attribute_info
| UnusedAttr of attribute_info
| UsedAttr of attribute_info
| UuidAttr of attribute_info
| VecReturnAttr of attribute_info
| VecTypeHintAttr of attribute_info
| VectorCallAttr of attribute_info
| VisibilityAttr of attribute_info
| WarnUnusedAttr of attribute_info
| WarnUnusedResultAttr of attribute_info
| WeakAttr of attribute_info
| WeakImportAttr of attribute_info
| WeakRefAttr of attribute_info
| WorkGroupSizeHintAttr of attribute_info
| X86ForceAlignArgPointerAttr of attribute_info
| XRayInstrumentAttr of attribute_info
| AbiTagAttr of attribute_info
| AliasAttr of attribute_info
| AlignValueAttr of attribute_info
| IFuncAttr of attribute_info
| InitSegAttr of attribute_info
| LoopHintAttr of attribute_info
| ModeAttr of attribute_info
| OMPDeclareSimdDeclAttr of attribute_info
| OMPDeclareTargetDeclAttr of attribute_info
| ObjCBoxableAttr of attribute_info
| ObjCDesignatedInitializerAttr of attribute_info
| ObjCRuntimeNameAttr of attribute_info
| ObjCRuntimeVisibleAttr of attribute_info
| OpenCLAccessAttr of attribute_info
| OverloadableAttr of attribute_info
| RenderScriptKernelAttr of attribute_info
| ThreadAttr of attribute_info
] <ocaml repr="classic">
type attribute_info = {
  pointer : pointer;
  source_range : source_range;
  parameters : string list;
  ~is_inherited : bool;
  ~is_implicit : bool
} <ocaml field_prefix="ai_">
type previous_decl = [
| None
| First of pointer
| Previous of pointer
]
type access_specifier = [ None | Public | Protected | Private ]
type cxx_ctor_initializer = {
  subject : cxx_ctor_initializer_subject;
  source_range : source_range;
  ?init_expr : stmt option
} <ocaml field_prefix="xci_">
type cxx_ctor_initializer_subject = [
  Member of decl_ref
| Delegating of type_ptr
| BaseClass of (type_ptr * bool)
]
type declaration_name = {
  kind : declaration_name_kind;
  name : string;
}  <ocaml field_prefix="dn_">
type declaration_name_kind = [
  Identifier
| ObjCZeroArgSelector
| ObjCOneArgSelector
| ObjCMultiArgSelector
| CXXConstructorName
| CXXDestructorName
| CXXConversionFunctionName
| CXXOperatorName
| CXXLiteralOperatorName
| CXXUsingDirective
]
type nested_name_specifier_loc = {
  kind : specifier_kind;
  ?ref : decl_ref option;
} <ocaml field_prefix="nnsl_">
type specifier_kind = [
   Identifier
 | Namespace
 | NamespaceAlias
 | TypeSpec
 | TypeSpecWithTemplate
 | Global
 | Super
]
#define access_spec_decl_tuple decl_tuple
#define block_decl_tuple decl_tuple
#define captured_decl_tuple decl_tuple
#define class_scope_function_specialization_decl_tuple decl_tuple
#define empty_decl_tuple decl_tuple
#define extern_c_context_decl_tuple decl_tuple
#define file_scope_asm_decl_tuple decl_tuple
#define friend_decl_tuple decl_tuple
#define friend_template_decl_tuple decl_tuple
#define import_decl_tuple decl_tuple
#define linkage_spec_decl_tuple decl_tuple
#define named_decl_tuple decl_tuple
#define label_decl_tuple named_decl_tuple
#define namespace_decl_tuple named_decl_tuple
#define namespace_alias_decl_tuple named_decl_tuple
#define obj_c_compatible_alias_decl_tuple named_decl_tuple
#define obj_c_container_decl_tuple named_decl_tuple
#define obj_c_category_decl_tuple obj_c_container_decl_tuple
#define obj_c_impl_decl_tuple obj_c_container_decl_tuple
#define obj_c_category_impl_decl_tuple obj_c_impl_decl_tuple
#define obj_c_implementation_decl_tuple obj_c_impl_decl_tuple
#define obj_c_interface_decl_tuple obj_c_container_decl_tuple
#define obj_c_protocol_decl_tuple obj_c_container_decl_tuple
#define obj_c_method_decl_tuple named_decl_tuple
#define obj_c_property_decl_tuple named_decl_tuple
#define template_decl_tuple named_decl_tuple
#define builtin_template_decl_tuple template_decl_tuple
#define redeclarable_template_decl_tuple template_decl_tuple
#define class_template_decl_tuple redeclarable_template_decl_tuple
#define function_template_decl_tuple redeclarable_template_decl_tuple
#define type_alias_template_decl_tuple redeclarable_template_decl_tuple
#define var_template_decl_tuple redeclarable_template_decl_tuple
#define template_template_parm_decl_tuple template_decl_tuple
#define type_decl_tuple named_decl_tuple
#define tag_decl_tuple type_decl_tuple
#define enum_decl_tuple tag_decl_tuple
#define record_decl_tuple tag_decl_tuple
#define cxx_record_decl_tuple record_decl_tuple
#define class_template_specialization_decl_tuple cxx_record_decl_tuple
#define class_template_partial_specialization_decl_tuple class_template_specialization_decl_tuple
#define template_type_parm_decl_tuple type_decl_tuple
#define typedef_name_decl_tuple type_decl_tuple
#define obj_c_type_param_decl_tuple typedef_name_decl_tuple
#define type_alias_decl_tuple typedef_name_decl_tuple
#define typedef_decl_tuple typedef_name_decl_tuple
#define unresolved_using_typename_decl_tuple type_decl_tuple
#define using_decl_tuple named_decl_tuple
#define using_directive_decl_tuple named_decl_tuple
#define using_shadow_decl_tuple named_decl_tuple
#define constructor_using_shadow_decl_tuple using_shadow_decl_tuple
#define value_decl_tuple named_decl_tuple
#define binding_decl_tuple value_decl_tuple
#define declarator_decl_tuple value_decl_tuple
#define field_decl_tuple declarator_decl_tuple
#define obj_c_at_defs_field_decl_tuple field_decl_tuple
#define obj_c_ivar_decl_tuple field_decl_tuple
#define function_decl_tuple declarator_decl_tuple
#define cxx_method_decl_tuple function_decl_tuple
#define cxx_constructor_decl_tuple cxx_method_decl_tuple
#define cxx_conversion_decl_tuple cxx_method_decl_tuple
#define cxx_destructor_decl_tuple cxx_method_decl_tuple
#define ms_property_decl_tuple declarator_decl_tuple
#define non_type_template_parm_decl_tuple declarator_decl_tuple
#define var_decl_tuple declarator_decl_tuple
#define decomposition_decl_tuple var_decl_tuple
#define implicit_param_decl_tuple var_decl_tuple
#define omp_captured_expr_decl_tuple var_decl_tuple
#define parm_var_decl_tuple var_decl_tuple
#define var_template_specialization_decl_tuple var_decl_tuple
#define var_template_partial_specialization_decl_tuple var_template_specialization_decl_tuple
#define enum_constant_decl_tuple value_decl_tuple
#define indirect_field_decl_tuple value_decl_tuple
#define omp_declare_reduction_decl_tuple value_decl_tuple
#define unresolved_using_value_decl_tuple value_decl_tuple
#define omp_thread_private_decl_tuple decl_tuple
#define obj_c_property_impl_decl_tuple decl_tuple
#define pragma_comment_decl_tuple decl_tuple
#define pragma_detect_mismatch_decl_tuple decl_tuple
#define static_assert_decl_tuple decl_tuple
#define translation_unit_decl_tuple decl_tuple
#define decl_tuple decl_info
type decl_info = {
  pointer : pointer;
  ?parent_pointer : pointer option;
  ~previous_decl <ocaml default="`None"> : previous_decl;
  source_range : source_range;
  ?owning_module : string option;
  ~is_hidden : bool;
  ~is_implicit : bool;
  ~is_used : bool;
  ~is_this_declaration_referenced : bool;
  ~is_invalid_decl : bool;
  ~attributes : attribute list;
  ?full_comment : comment option
} <ocaml field_prefix="di_">
#define captured_decl_tuple decl_tuple * decl_context_tuple
#define linkage_spec_decl_tuple decl_tuple * decl_context_tuple
#define namespace_decl_tuple named_decl_tuple * decl_context_tuple * namespace_decl_info
type namespace_decl_info = {
  ~is_inline : bool;
  ?original_namespace : decl_ref option;
} <ocaml field_prefix="ndi_">
#define obj_c_container_decl_tuple named_decl_tuple * decl_context_tuple
#define tag_decl_tuple type_decl_tuple * decl_context_tuple
#define type_decl_tuple named_decl_tuple * opt_type * type_ptr
#define value_decl_tuple named_decl_tuple * qual_type
type input_kind = [
  IK_None
| IK_Asm
| IK_C
| IK_CXX
| IK_ObjC
| IK_ObjCXX
| IK_PreprocessedC
| IK_PreprocessedCXX
| IK_PreprocessedObjC
| IK_PreprocessedObjCXX
| IK_OpenCL
| IK_CUDA
| IK_PreprocessedCuda
| IK_RenderScript
| IK_AST
| IK_LLVM_IR
]
#define translation_unit_decl_tuple decl_tuple * decl_context_tuple * translation_unit_decl_info
type  translation_unit_decl_info = {
  input_path : string;
  input_kind : input_kind;
  ~arc_enabled : bool;
  types : c_type list;
} <ocaml field_prefix="tudi_">
#define named_decl_tuple decl_tuple * named_decl_info
#define typedef_decl_tuple typedef_name_decl_tuple * typedef_decl_info
type typedef_decl_info = {
  ~is_module_private : bool
} <ocaml field_prefix="tdi_">
#define enum_decl_tuple tag_decl_tuple * enum_decl_info
type enum_decl_info = {
  ?scope : enum_decl_scope option;
  ~is_module_private : bool
} <ocaml field_prefix="edi_">
type enum_decl_scope = [Class | Struct]
#define record_decl_tuple tag_decl_tuple * record_decl_info
type record_decl_info = {
  ~is_module_private : bool;
  ~is_complete_definition : bool
} <ocaml field_prefix="rdi_">
#define enum_constant_decl_tuple value_decl_tuple * enum_constant_decl_info
type enum_constant_decl_info = {
  ?init_expr : stmt option
} <ocaml field_prefix="ecdi_">
#define indirect_field_decl_tuple value_decl_tuple * decl_ref list
#define function_decl_tuple declarator_decl_tuple * function_decl_info
type function_decl_info = {
  ?mangled_name : string option;
  ?storage_class : string option;
  ~is_inline : bool;
  ~is_module_private : bool;
  ~is_pure : bool;
  ~is_delete_as_written : bool;
  ~decls_in_prototype_scope : decl list;
  ~parameters : decl list;
  ?decl_ptr_with_body : pointer option;
  ?body : stmt option
} <ocaml field_prefix="fdi_">
#define field_decl_tuple declarator_decl_tuple * field_decl_info
type field_decl_info = {
  ~is_mutable : bool;
  ~is_module_private : bool;
  ?init_expr : stmt option;
  ?bit_width_expr : stmt option
} <ocaml field_prefix="fldi_">
#define var_decl_tuple declarator_decl_tuple * var_decl_info
type var_decl_info = {
  ?storage_class : string option;
  ~tls_kind <ocaml default="`Tls_none">: tls_kind;
  ~is_global : bool;
  ~is_static_local : bool;
  ~is_module_private : bool;
  ~is_nrvo_variable : bool;
  ~is_const_expr : bool;
  ?init_expr : stmt option;
  ?parm_index_in_function : int option;
} <ocaml field_prefix="vdi_">
type tls_kind = [ Tls_none | Tls_static | Tls_dynamic ]
#define file_scope_asm_decl_tuple decl_tuple * string
#define import_decl_tuple decl_tuple * string
#define using_directive_decl_tuple named_decl_tuple * using_directive_decl_info
type using_directive_decl_info = {
  using_location : source_location;
  namespace_key_location : source_location;
  nested_name_specifier_locs : nested_name_specifier_loc list;
  ?nominated_namespace : decl_ref option;
} <ocaml field_prefix="uddi_">
#define namespace_alias_decl_tuple named_decl_tuple * namespace_alias_decl_info
type namespace_alias_decl_info = {
  namespace_loc : source_location;
  target_name_loc : source_location;
  nested_name_specifier_locs : nested_name_specifier_loc list;
  namespace : decl_ref;
} <ocaml field_prefix="nadi_">
#define cxx_record_decl_tuple record_decl_tuple * cxx_record_decl_info
type cxx_record_decl_info = {
  ~bases : type_ptr list;
  ~vbases : type_ptr list;
  ~is_pod : bool;
  ?destructor : decl_ref option;
  ?lambda_call_operator : decl_ref option;
} <ocaml field_prefix="xrdi_">
type template_instantiation_arg_info = [
  | Null
  | Type of type_ptr
  | Declaration
  | NullPtr
  | Integral
  | Template
  | TemplateExpansion
  | Expression
  | Pack
]
#define class_template_specialization_decl_tuple cxx_record_decl_tuple * template_instantiation_arg_info list
#define cxx_method_decl_tuple function_decl_tuple * cxx_method_decl_info
type cxx_method_decl_info = {
  ~is_virtual : bool;
  ~is_static : bool;
  ~cxx_ctor_initializers : cxx_ctor_initializer list;
  ~overriden_methods : decl_ref list;
} <ocaml field_prefix="xmdi_">
#define class_template_decl_tuple redeclarable_template_decl_tuple * template_decl_info
type template_decl_info = {
  ~specializations : decl list;
} <ocaml field_prefix="tdi_">
#define function_template_decl_tuple redeclarable_template_decl_tuple * template_decl_info
#define friend_decl_tuple decl_tuple * friend_info
type friend_info = [ Type of type_ptr | Decl of decl ]
#define obj_c_ivar_decl_tuple field_decl_tuple * obj_c_ivar_decl_info
type obj_c_ivar_decl_info = {
  ~is_synthesize : bool;
  ~access_control <ocaml default="`None"> : obj_c_access_control;
} <ocaml field_prefix="ovdi_">
type obj_c_access_control = [ None | Private | Protected | Public | Package
]
#define obj_c_method_decl_tuple named_decl_tuple * obj_c_method_decl_info
type obj_c_method_decl_info = {
  ~is_instance_method : bool;
  result_type : type_ptr;
  ~is_property_accessor : bool;
  ?property_decl : decl_ref option;
  ~parameters : decl list;
  ~implicit_parameters : decl list;
  ~is_variadic : bool;
  ?body : stmt option;
} <ocaml field_prefix="omdi_">
#define obj_c_category_decl_tuple obj_c_container_decl_tuple * obj_c_category_decl_info
type obj_c_category_decl_info = {
  ?class_interface : decl_ref option;
  ?implementation : decl_ref option;
  ~protocols : decl_ref list;
} <ocaml field_prefix="odi_">
#define obj_c_category_impl_decl_tuple obj_c_impl_decl_tuple * obj_c_category_impl_decl_info
type obj_c_category_impl_decl_info = {
  ?class_interface : decl_ref option;
  ?category_decl : decl_ref option;
} <ocaml field_prefix="ocidi_">
#define obj_c_protocol_decl_tuple obj_c_container_decl_tuple * obj_c_protocol_decl_info
type obj_c_protocol_decl_info = {
  ~protocols : decl_ref list;
} <ocaml field_prefix="opcdi_">
#define obj_c_interface_decl_tuple obj_c_container_decl_tuple * obj_c_interface_decl_info
type obj_c_interface_decl_info = {
  ?super : decl_ref option;
  ?implementation : decl_ref option;
  ~protocols : decl_ref list;
  ~known_categories : decl_ref list;
} <ocaml field_prefix="otdi_">
#define obj_c_implementation_decl_tuple obj_c_impl_decl_tuple * obj_c_implementation_decl_info
type obj_c_implementation_decl_info = {
  ?super : decl_ref option;
  ?class_interface : decl_ref option;
  ~ivar_initializers : cxx_ctor_initializer list;
} <ocaml field_prefix="oidi_">
#define obj_c_compatible_alias_decl_tuple named_decl_tuple * obj_c_compatible_alias_decl_info
type obj_c_compatible_alias_decl_info = {
  ?class_interface : decl_ref option;
} <ocaml field_prefix="ocadi_">
#define obj_c_property_decl_tuple named_decl_tuple * obj_c_property_decl_info
type obj_c_property_decl_info = {
  type_ptr : type_ptr;
  ?getter_method : decl_ref option;
  ?setter_method : decl_ref option;
  ?ivar_decl : decl_ref option;
  ~property_control <ocaml default="`None"> : obj_c_property_control;
  ~property_attributes : property_attribute list
} <ocaml field_prefix="opdi_">
type obj_c_property_control = [ None | Required | Optional ]
type property_attribute = [
  Readonly
| Assign
| Readwrite
| Retain
| Copy
| Nonatomic
| Atomic
| Weak
| Strong
| Unsafe_unretained
| ExplicitGetter
| ExplicitSetter
]
#define obj_c_property_impl_decl_tuple decl_tuple * obj_c_property_impl_decl_info
type obj_c_property_impl_decl_info = {
  implementation : property_implementation;
  ?property_decl : decl_ref option;
  ?ivar_decl : decl_ref option;
} <ocaml field_prefix="opidi_">
type property_implementation = [ Synthesize | Dynamic ]
#define block_decl_tuple decl_tuple * block_decl_info
type block_decl_info = {
  ~parameters : decl list;
  ~is_variadic : bool;
  ~captures_cxx_this : bool;
  ~captured_variables : block_captured_variable list;
  ?body : stmt option;
} <ocaml field_prefix="bdi_">
type block_captured_variable = {
   ~is_by_ref : bool;
   ~is_nested : bool;
   ?variable : decl_ref option;
   ?copy_expr : stmt option
} <ocaml field_prefix="bcv_">
type decl = [
| AccessSpecDecl of (access_spec_decl_tuple)
| BlockDecl of (block_decl_tuple)
| CapturedDecl of (captured_decl_tuple)
| ClassScopeFunctionSpecializationDecl of (class_scope_function_specialization_decl_tuple)
| EmptyDecl of (empty_decl_tuple)
| ExternCContextDecl of (extern_c_context_decl_tuple)
| FileScopeAsmDecl of (file_scope_asm_decl_tuple)
| FriendDecl of (friend_decl_tuple)
| FriendTemplateDecl of (friend_template_decl_tuple)
| ImportDecl of (import_decl_tuple)
| LinkageSpecDecl of (linkage_spec_decl_tuple)
| LabelDecl of (label_decl_tuple)
| NamespaceDecl of (namespace_decl_tuple)
| NamespaceAliasDecl of (namespace_alias_decl_tuple)
| ObjCCompatibleAliasDecl of (obj_c_compatible_alias_decl_tuple)
| ObjCCategoryDecl of (obj_c_category_decl_tuple)
| ObjCCategoryImplDecl of (obj_c_category_impl_decl_tuple)
| ObjCImplementationDecl of (obj_c_implementation_decl_tuple)
| ObjCInterfaceDecl of (obj_c_interface_decl_tuple)
| ObjCProtocolDecl of (obj_c_protocol_decl_tuple)
| ObjCMethodDecl of (obj_c_method_decl_tuple)
| ObjCPropertyDecl of (obj_c_property_decl_tuple)
| BuiltinTemplateDecl of (builtin_template_decl_tuple)
| ClassTemplateDecl of (class_template_decl_tuple)
| FunctionTemplateDecl of (function_template_decl_tuple)
| TypeAliasTemplateDecl of (type_alias_template_decl_tuple)
| VarTemplateDecl of (var_template_decl_tuple)
| TemplateTemplateParmDecl of (template_template_parm_decl_tuple)
| EnumDecl of (enum_decl_tuple)
| RecordDecl of (record_decl_tuple)
| CXXRecordDecl of (cxx_record_decl_tuple)
| ClassTemplateSpecializationDecl of (class_template_specialization_decl_tuple)
| ClassTemplatePartialSpecializationDecl of (class_template_partial_specialization_decl_tuple)
| TemplateTypeParmDecl of (template_type_parm_decl_tuple)
| ObjCTypeParamDecl of (obj_c_type_param_decl_tuple)
| TypeAliasDecl of (type_alias_decl_tuple)
| TypedefDecl of (typedef_decl_tuple)
| UnresolvedUsingTypenameDecl of (unresolved_using_typename_decl_tuple)
| UsingDecl of (using_decl_tuple)
| UsingDirectiveDecl of (using_directive_decl_tuple)
| UsingShadowDecl of (using_shadow_decl_tuple)
| ConstructorUsingShadowDecl of (constructor_using_shadow_decl_tuple)
| BindingDecl of (binding_decl_tuple)
| FieldDecl of (field_decl_tuple)
| ObjCAtDefsFieldDecl of (obj_c_at_defs_field_decl_tuple)
| ObjCIvarDecl of (obj_c_ivar_decl_tuple)
| FunctionDecl of (function_decl_tuple)
| CXXMethodDecl of (cxx_method_decl_tuple)
| CXXConstructorDecl of (cxx_constructor_decl_tuple)
| CXXConversionDecl of (cxx_conversion_decl_tuple)
| CXXDestructorDecl of (cxx_destructor_decl_tuple)
| MSPropertyDecl of (ms_property_decl_tuple)
| NonTypeTemplateParmDecl of (non_type_template_parm_decl_tuple)
| VarDecl of (var_decl_tuple)
| DecompositionDecl of (decomposition_decl_tuple)
| ImplicitParamDecl of (implicit_param_decl_tuple)
| OMPCapturedExprDecl of (omp_captured_expr_decl_tuple)
| ParmVarDecl of (parm_var_decl_tuple)
| VarTemplateSpecializationDecl of (var_template_specialization_decl_tuple)
| VarTemplatePartialSpecializationDecl of (var_template_partial_specialization_decl_tuple)
| EnumConstantDecl of (enum_constant_decl_tuple)
| IndirectFieldDecl of (indirect_field_decl_tuple)
| OMPDeclareReductionDecl of (omp_declare_reduction_decl_tuple)
| UnresolvedUsingValueDecl of (unresolved_using_value_decl_tuple)
| OMPThreadPrivateDecl of (omp_thread_private_decl_tuple)
| ObjCPropertyImplDecl of (obj_c_property_impl_decl_tuple)
| PragmaCommentDecl of (pragma_comment_decl_tuple)
| PragmaDetectMismatchDecl of (pragma_detect_mismatch_decl_tuple)
| StaticAssertDecl of (static_assert_decl_tuple)
| TranslationUnitDecl of (translation_unit_decl_tuple)
] <ocaml repr="classic" validator="Clang_ast_visit.visit_decl">
#define asm_stmt_tuple stmt_tuple
#define gcc_asm_stmt_tuple asm_stmt_tuple
#define ms_asm_stmt_tuple asm_stmt_tuple
#define attributed_stmt_tuple stmt_tuple
#define break_stmt_tuple stmt_tuple
#define cxx_catch_stmt_tuple stmt_tuple
#define cxx_for_range_stmt_tuple stmt_tuple
#define cxx_try_stmt_tuple stmt_tuple
#define captured_stmt_tuple stmt_tuple
#define compound_stmt_tuple stmt_tuple
#define continue_stmt_tuple stmt_tuple
#define coreturn_stmt_tuple stmt_tuple
#define coroutine_body_stmt_tuple stmt_tuple
#define decl_stmt_tuple stmt_tuple
#define do_stmt_tuple stmt_tuple
#define expr_tuple stmt_tuple
#define abstract_conditional_operator_tuple expr_tuple
#define binary_conditional_operator_tuple abstract_conditional_operator_tuple
#define conditional_operator_tuple abstract_conditional_operator_tuple
#define addr_label_expr_tuple expr_tuple
#define array_subscript_expr_tuple expr_tuple
#define array_type_trait_expr_tuple expr_tuple
#define as_type_expr_tuple expr_tuple
#define atomic_expr_tuple expr_tuple
#define binary_operator_tuple expr_tuple
#define compound_assign_operator_tuple binary_operator_tuple
#define block_expr_tuple expr_tuple
#define cxx_bind_temporary_expr_tuple expr_tuple
#define cxx_bool_literal_expr_tuple expr_tuple
#define cxx_construct_expr_tuple expr_tuple
#define cxx_temporary_object_expr_tuple cxx_construct_expr_tuple
#define cxx_default_arg_expr_tuple expr_tuple
#define cxx_default_init_expr_tuple expr_tuple
#define cxx_delete_expr_tuple expr_tuple
#define cxx_dependent_scope_member_expr_tuple expr_tuple
#define cxx_fold_expr_tuple expr_tuple
#define cxx_inherited_ctor_init_expr_tuple expr_tuple
#define cxx_new_expr_tuple expr_tuple
#define cxx_noexcept_expr_tuple expr_tuple
#define cxx_null_ptr_literal_expr_tuple expr_tuple
#define cxx_pseudo_destructor_expr_tuple expr_tuple
#define cxx_scalar_value_init_expr_tuple expr_tuple
#define cxx_std_initializer_list_expr_tuple expr_tuple
#define cxx_this_expr_tuple expr_tuple
#define cxx_throw_expr_tuple expr_tuple
#define cxx_typeid_expr_tuple expr_tuple
#define cxx_unresolved_construct_expr_tuple expr_tuple
#define cxx_uuidof_expr_tuple expr_tuple
#define call_expr_tuple expr_tuple
#define cuda_kernel_call_expr_tuple call_expr_tuple
#define cxx_member_call_expr_tuple call_expr_tuple
#define cxx_operator_call_expr_tuple call_expr_tuple
#define user_defined_literal_tuple call_expr_tuple
#define cast_expr_tuple expr_tuple
#define explicit_cast_expr_tuple cast_expr_tuple
#define c_style_cast_expr_tuple explicit_cast_expr_tuple
#define cxx_functional_cast_expr_tuple explicit_cast_expr_tuple
#define cxx_named_cast_expr_tuple explicit_cast_expr_tuple
#define cxx_const_cast_expr_tuple cxx_named_cast_expr_tuple
#define cxx_dynamic_cast_expr_tuple cxx_named_cast_expr_tuple
#define cxx_reinterpret_cast_expr_tuple cxx_named_cast_expr_tuple
#define cxx_static_cast_expr_tuple cxx_named_cast_expr_tuple
#define obj_c_bridged_cast_expr_tuple explicit_cast_expr_tuple
#define implicit_cast_expr_tuple cast_expr_tuple
#define character_literal_tuple expr_tuple
#define choose_expr_tuple expr_tuple
#define compound_literal_expr_tuple expr_tuple
#define convert_vector_expr_tuple expr_tuple
#define coroutine_suspend_expr_tuple expr_tuple
#define coawait_expr_tuple coroutine_suspend_expr_tuple
#define coyield_expr_tuple coroutine_suspend_expr_tuple
#define decl_ref_expr_tuple expr_tuple
#define dependent_scope_decl_ref_expr_tuple expr_tuple
#define designated_init_expr_tuple expr_tuple
#define designated_init_update_expr_tuple expr_tuple
#define expr_with_cleanups_tuple expr_tuple
#define expression_trait_expr_tuple expr_tuple
#define ext_vector_element_expr_tuple expr_tuple
#define floating_literal_tuple expr_tuple
#define function_parm_pack_expr_tuple expr_tuple
#define gnu_null_expr_tuple expr_tuple
#define generic_selection_expr_tuple expr_tuple
#define imaginary_literal_tuple expr_tuple
#define implicit_value_init_expr_tuple expr_tuple
#define init_list_expr_tuple expr_tuple
#define integer_literal_tuple expr_tuple
#define lambda_expr_tuple expr_tuple
#define ms_property_ref_expr_tuple expr_tuple
#define ms_property_subscript_expr_tuple expr_tuple
#define materialize_temporary_expr_tuple expr_tuple
#define member_expr_tuple expr_tuple
#define no_init_expr_tuple expr_tuple
#define omp_array_section_expr_tuple expr_tuple
#define obj_c_array_literal_tuple expr_tuple
#define obj_c_availability_check_expr_tuple expr_tuple
#define obj_c_bool_literal_expr_tuple expr_tuple
#define obj_c_boxed_expr_tuple expr_tuple
#define obj_c_dictionary_literal_tuple expr_tuple
#define obj_c_encode_expr_tuple expr_tuple
#define obj_c_indirect_copy_restore_expr_tuple expr_tuple
#define obj_c_isa_expr_tuple expr_tuple
#define obj_c_ivar_ref_expr_tuple expr_tuple
#define obj_c_message_expr_tuple expr_tuple
#define obj_c_property_ref_expr_tuple expr_tuple
#define obj_c_protocol_expr_tuple expr_tuple
#define obj_c_selector_expr_tuple expr_tuple
#define obj_c_string_literal_tuple expr_tuple
#define obj_c_subscript_ref_expr_tuple expr_tuple
#define offset_of_expr_tuple expr_tuple
#define opaque_value_expr_tuple expr_tuple
#define overload_expr_tuple expr_tuple
#define unresolved_lookup_expr_tuple overload_expr_tuple
#define unresolved_member_expr_tuple overload_expr_tuple
#define pack_expansion_expr_tuple expr_tuple
#define paren_expr_tuple expr_tuple
#define paren_list_expr_tuple expr_tuple
#define predefined_expr_tuple expr_tuple
#define pseudo_object_expr_tuple expr_tuple
#define shuffle_vector_expr_tuple expr_tuple
#define size_of_pack_expr_tuple expr_tuple
#define stmt_expr_tuple expr_tuple
#define string_literal_tuple expr_tuple
#define subst_non_type_template_parm_expr_tuple expr_tuple
#define subst_non_type_template_parm_pack_expr_tuple expr_tuple
#define type_trait_expr_tuple expr_tuple
#define typo_expr_tuple expr_tuple
#define unary_expr_or_type_trait_expr_tuple expr_tuple
#define unary_operator_tuple expr_tuple
#define va_arg_expr_tuple expr_tuple
#define for_stmt_tuple stmt_tuple
#define goto_stmt_tuple stmt_tuple
#define if_stmt_tuple stmt_tuple
#define indirect_goto_stmt_tuple stmt_tuple
#define label_stmt_tuple stmt_tuple
#define ms_dependent_exists_stmt_tuple stmt_tuple
#define null_stmt_tuple stmt_tuple
#define omp_executable_directive_tuple stmt_tuple
#define omp_atomic_directive_tuple omp_executable_directive_tuple
#define omp_barrier_directive_tuple omp_executable_directive_tuple
#define omp_cancel_directive_tuple omp_executable_directive_tuple
#define omp_cancellation_point_directive_tuple omp_executable_directive_tuple
#define omp_critical_directive_tuple omp_executable_directive_tuple
#define omp_flush_directive_tuple omp_executable_directive_tuple
#define omp_loop_directive_tuple omp_executable_directive_tuple
#define omp_distribute_directive_tuple omp_loop_directive_tuple
#define omp_distribute_parallel_for_directive_tuple omp_loop_directive_tuple
#define omp_distribute_parallel_for_simd_directive_tuple omp_loop_directive_tuple
#define omp_distribute_simd_directive_tuple omp_loop_directive_tuple
#define omp_for_directive_tuple omp_loop_directive_tuple
#define omp_for_simd_directive_tuple omp_loop_directive_tuple
#define omp_parallel_for_directive_tuple omp_loop_directive_tuple
#define omp_parallel_for_simd_directive_tuple omp_loop_directive_tuple
#define omp_simd_directive_tuple omp_loop_directive_tuple
#define omp_target_parallel_for_simd_directive_tuple omp_loop_directive_tuple
#define omp_target_simd_directive_tuple omp_loop_directive_tuple
#define omp_task_loop_directive_tuple omp_loop_directive_tuple
#define omp_task_loop_simd_directive_tuple omp_loop_directive_tuple
#define omp_master_directive_tuple omp_executable_directive_tuple
#define omp_ordered_directive_tuple omp_executable_directive_tuple
#define omp_parallel_directive_tuple omp_executable_directive_tuple
#define omp_parallel_sections_directive_tuple omp_executable_directive_tuple
#define omp_section_directive_tuple omp_executable_directive_tuple
#define omp_sections_directive_tuple omp_executable_directive_tuple
#define omp_single_directive_tuple omp_executable_directive_tuple
#define omp_target_data_directive_tuple omp_executable_directive_tuple
#define omp_target_directive_tuple omp_executable_directive_tuple
#define omp_target_enter_data_directive_tuple omp_executable_directive_tuple
#define omp_target_exit_data_directive_tuple omp_executable_directive_tuple
#define omp_target_parallel_directive_tuple omp_executable_directive_tuple
#define omp_target_parallel_for_directive_tuple omp_executable_directive_tuple
#define omp_target_update_directive_tuple omp_executable_directive_tuple
#define omp_task_directive_tuple omp_executable_directive_tuple
#define omp_taskgroup_directive_tuple omp_executable_directive_tuple
#define omp_taskwait_directive_tuple omp_executable_directive_tuple
#define omp_taskyield_directive_tuple omp_executable_directive_tuple
#define omp_teams_directive_tuple omp_executable_directive_tuple
#define obj_c_at_catch_stmt_tuple stmt_tuple
#define obj_c_at_finally_stmt_tuple stmt_tuple
#define obj_c_at_synchronized_stmt_tuple stmt_tuple
#define obj_c_at_throw_stmt_tuple stmt_tuple
#define obj_c_at_try_stmt_tuple stmt_tuple
#define obj_c_autorelease_pool_stmt_tuple stmt_tuple
#define obj_c_for_collection_stmt_tuple stmt_tuple
#define return_stmt_tuple stmt_tuple
#define seh_except_stmt_tuple stmt_tuple
#define seh_finally_stmt_tuple stmt_tuple
#define seh_leave_stmt_tuple stmt_tuple
#define seh_try_stmt_tuple stmt_tuple
#define switch_case_tuple stmt_tuple
#define case_stmt_tuple switch_case_tuple
#define default_stmt_tuple switch_case_tuple
#define switch_stmt_tuple stmt_tuple
#define while_stmt_tuple stmt_tuple
#define stmt_tuple stmt_info * stmt list
type stmt_info = {
  pointer : pointer;
  source_range : source_range;
} <ocaml field_prefix="si_">
#define decl_stmt_tuple stmt_tuple * decl list
#define attributed_stmt_tuple stmt_tuple * attribute list
#define label_stmt_tuple stmt_tuple * string
#define goto_stmt_tuple stmt_tuple * goto_stmt_info
type goto_stmt_info = {
  label : string;
  pointer : pointer
} <ocaml field_prefix="gsi_">
#define cxx_catch_stmt_tuple stmt_tuple * cxx_catch_stmt_info
type cxx_catch_stmt_info = {
  ?variable : decl option
} <ocaml field_prefix="xcsi_">
#define expr_tuple stmt_tuple * expr_info
type expr_info = {
  type_ptr : type_ptr;
  ~value_kind <ocaml default="`RValue"> : value_kind;
  ~object_kind <ocaml default="`Ordinary"> : object_kind;
} <ocaml field_prefix="ei_">
type value_kind = [ RValue | LValue | XValue ]
type object_kind = [ Ordinary | BitField | ObjCProperty | ObjCSubscript |
VectorComponent ]
type cxx_base_specifier = {
  name : string;
  ~virtual : bool;
} <ocaml field_prefix="xbs_">
type cast_kind = [
| Dependent
| BitCast
| LValueBitCast
| LValueToRValue
| NoOp
| BaseToDerived
| DerivedToBase
| UncheckedDerivedToBase
| Dynamic
| ToUnion
| ArrayToPointerDecay
| FunctionToPointerDecay
| NullToPointer
| NullToMemberPointer
| BaseToDerivedMemberPointer
| DerivedToBaseMemberPointer
| MemberPointerToBoolean
| ReinterpretMemberPointer
| UserDefinedConversion
| ConstructorConversion
| IntegralToPointer
| PointerToIntegral
| PointerToBoolean
| ToVoid
| VectorSplat
| IntegralCast
| IntegralToBoolean
| IntegralToFloating
| FloatingToIntegral
| FloatingToBoolean
| FloatingCast
| CPointerToObjCPointerCast
| BlockPointerToObjCPointerCast
| AnyPointerToBlockPointerCast
| ObjCObjectLValueCast
| FloatingRealToComplex
| FloatingComplexToReal
| FloatingComplexToBoolean
| FloatingComplexCast
| FloatingComplexToIntegralComplex
| IntegralRealToComplex
| IntegralComplexToReal
| IntegralComplexToBoolean
| IntegralComplexCast
| IntegralComplexToFloatingComplex
| ARCProduceObject
| ARCConsumeObject
| ARCReclaimReturnedObject
| ARCExtendBlockObject
| AtomicToNonAtomic
| NonAtomicToAtomic
| CopyAndAutoreleaseBlockObject
| BuiltinFnToFnPtr
| ZeroToOCLEvent
]
#define cast_expr_tuple expr_tuple * cast_expr_info
type cast_expr_info = {
  cast_kind : cast_kind;
  base_path : cxx_base_specifier list;
} <ocaml field_prefix="cei_">
#define explicit_cast_expr_tuple cast_expr_tuple * type_ptr
#define decl_ref_expr_tuple expr_tuple * decl_ref_expr_info
type decl_ref_expr_info = {
  ?decl_ref : decl_ref option;
  ?found_decl_ref : decl_ref option
} <ocaml field_prefix="drti_">
#define overload_expr_tuple expr_tuple * overload_expr_info
type overload_expr_info = {
  ~decls : decl_ref list;
  name : declaration_name;
} <ocaml field_prefix="oei_">
#define unresolved_lookup_expr_tuple overload_expr_tuple * unresolved_lookup_expr_info
type unresolved_lookup_expr_info = {
  ~requires_ADL : bool;
  ~is_overloaded : bool;
  ?naming_class : decl_ref option;
} <ocaml field_prefix="ulei_">
#define obj_c_ivar_ref_expr_tuple expr_tuple * obj_c_ivar_ref_expr_info
type obj_c_ivar_ref_expr_info = {
  decl_ref : decl_ref;
  pointer : pointer;
  ~is_free_ivar : bool
} <ocaml field_prefix="ovrei_">
#define predefined_expr_tuple expr_tuple * predefined_expr_type
type predefined_expr_type = [
| Func
| Function
| LFunction
| FuncDName
| FuncSig
| PrettyFunction
| PrettyFunctionNoVirtual
]
#define character_literal_tuple expr_tuple * int
#define integer_literal_tuple expr_tuple * integer_literal_info
type integer_literal_info = {
  ~is_signed : bool;
  bitwidth : int;
  value : string;
} <ocaml field_prefix="ili_">
#define floating_literal_tuple expr_tuple * string
#define string_literal_tuple expr_tuple * string
#define unary_operator_tuple expr_tuple * unary_operator_info
type unary_operator_info = {
  kind : unary_operator_kind;
  ~is_postfix : bool;
} <ocaml field_prefix="uoi_">
type unary_operator_kind = [
  PostInc
| PostDec
| PreInc
| PreDec
| AddrOf
| Deref
| Plus
| Minus
| Not
| LNot
| Real
| Imag
| Extension
| Coawait
]
#define unary_expr_or_type_trait_expr_tuple expr_tuple * unary_expr_or_type_trait_expr_info
type unary_expr_or_type_trait_expr_info = {
  kind : unary_expr_or_type_trait_kind;
  ?type_ptr : type_ptr option
} <ocaml field_prefix="uttei_">
type unary_expr_or_type_trait_kind = [ SizeOf | AlignOf | VecStep |
OpenMPRequiredSimdAlign ]
#define member_expr_tuple expr_tuple * member_expr_info
type member_expr_info = {
  ~is_arrow : bool;
  ~performs_virtual_dispatch : bool;
  name : named_decl_info;
  decl_ref : decl_ref
} <ocaml field_prefix="mei_">
#define ext_vector_element_tuple expr_tuple * string
#define binary_operator_tuple expr_tuple * binary_operator_info
type binary_operator_info = {
  kind : binary_operator_kind
} <ocaml field_prefix="boi_">
type binary_operator_kind = [
  PtrMemD |
  PtrMemI |
  Mul |
  Div |
  Rem |
  Add |
  Sub |
  Shl |
  Shr |
  LT |
  GT |
  LE |
  GE |
  EQ |
  NE |
  And |
  Xor |
  Or |
  LAnd |
  LOr |
  Assign |
  MulAssign |
  DivAssign |
  RemAssign |
  AddAssign |
  SubAssign |
  ShlAssign |
  ShrAssign |
  AndAssign |
  XorAssign |
  OrAssign |
  Comma
]
#define compound_assign_operator_tuple binary_operator_tuple * compound_assign_operator_info
type compound_assign_operator_info = {
  lhs_type : type_ptr;
  result_type : type_ptr;
} <ocaml field_prefix="caoi_">
#define block_expr_tuple expr_tuple * decl
#define opaque_value_expr_tuple expr_tuple * opaque_value_expr_info
type  opaque_value_expr_info = {
  ?source_expr : stmt option;
} <ocaml field_prefix="ovei_">
#define addr_label_expr_tuple expr_tuple * addr_label_expr_info
type addr_label_expr_info = {
  label : string;
  pointer : pointer;
} <ocaml field_prefix="alei_">
#define cxx_named_cast_expr_tuple explicit_cast_expr_tuple * string
#define cxx_bool_literal_expr_tuple expr_tuple * int
#define cxx_construct_expr_tuple expr_tuple * cxx_construct_expr_info
type cxx_construct_expr_info = {
  decl_ref : decl_ref;
  ~is_elidable : bool;
  ~requires_zero_initialization : bool;
} <ocaml field_prefix="xcei_">
#define cxx_bind_temporary_expr_tuple expr_tuple * cxx_bind_temporary_expr_info
type cxx_bind_temporary_expr_info = {
  cxx_temporary : cxx_temporary;
} <ocaml field_prefix="xbtei_">
#define materialize_temporary_expr_tuple expr_tuple * materialize_temporary_expr_info
type materialize_temporary_expr_info = {
  ?decl_ref : decl_ref option;
} <ocaml field_prefix="mtei_">
#define expr_with_cleanups_tuple expr_tuple * expr_with_cleanups_info
type expr_with_cleanups_info = {
 ~decl_refs : decl_ref list;
} <ocaml field_prefix="ewci_">
type cxx_temporary = pointer
type lambda_capture_info = {
  capture_kind : lambda_capture_kind;
  ~capture_this : bool;
  ~capture_variable : bool;
  ~capture_VLAtype : bool;
  ?captured_var : decl_ref option;
  ~is_implicit : bool;
  location : source_range;
  ~is_pack_expansion: bool;
} <ocaml field_prefix="lci_">
type lambda_capture_kind = [
        | LCK_This
        | LCK_ByCopy
        | LCK_ByRef
        | LCK_VLAType
        | LCK_StarThis]
#define lambda_expr_tuple expr_tuple * lambda_expr_info
type lambda_expr_info = {
  ~captures: lambda_capture_info list;
  lambda_decl: decl;
} <ocaml field_prefix="lei_">
#define cxx_new_expr_tuple expr_tuple * cxx_new_expr_info
type cxx_new_expr_info = {
  ~is_array : bool;
  ?array_size_expr : pointer option;
  ?initializer_expr : pointer option;
} <ocaml field_prefix="xnei_">
#define cxx_delete_expr_tuple expr_tuple * cxx_delete_expr_info
type cxx_delete_expr_info = {
  ~is_array : bool;
  destroyed_type : type_ptr;
} <ocaml field_prefix="xdei_">
#define cxx_default_arg_expr_tuple expr_tuple * cxx_default_expr_info
type cxx_default_expr_info = {
  ?init_expr : stmt option;
} <ocaml field_prefix="xdaei_">
#define cxx_default_init_expr_tuple expr_tuple * cxx_default_expr_info
#define type_trait_expr_tuple expr_tuple * type_trait_info
type type_trait_info = {
  ~value : bool;
} <ocaml field_prefix="xtti_">
#define cxx_noexcept_expr_tuple expr_tuple * cxx_noexcept_expr_info
type cxx_noexcept_expr_info = {
  ~value : bool;
} <ocaml field_prefix="xnee_">
#define obj_c_message_expr_tuple expr_tuple * obj_c_message_expr_info
type obj_c_message_expr_info = {
  selector : string;
  ~is_definition_found : bool;
  ?decl_pointer : pointer option;
  ~receiver_kind <ocaml default="`Instance"> : receiver_kind
} <ocaml field_prefix="omei_">
type receiver_kind = [ Instance | Class of type_ptr | SuperInstance |
SuperClass ]
type selector = string
#define obj_c_boxed_expr_tuple expr_tuple * objc_boxed_expr_info
type objc_boxed_expr_info = {
  ?boxing_method : selector option;
}  <ocaml field_prefix="obei_">
#define obj_c_at_catch_stmt_tuple stmt_tuple * obj_c_message_expr_kind
type obj_c_message_expr_kind = [
| CatchParam of decl
| CatchAll
]
#define obj_c_encode_expr_tuple expr_tuple * objc_encode_expr_info
type objc_encode_expr_info = {
  type_ptr : type_ptr;
  raw : string;
} <ocaml field_prefix="oeei_">
#define obj_c_selector_expr_tuple expr_tuple * selector
#define obj_c_protocol_expr_tuple expr_tuple * decl_ref
#define obj_c_property_ref_expr_tuple expr_tuple * obj_c_property_ref_expr_info
type obj_c_property_ref_expr_info = {
  kind : property_ref_kind;
  ~is_super_receiver : bool;
  ~is_messaging_getter : bool;
  ~is_messaging_setter : bool;
} <ocaml field_prefix="oprei_">
type property_ref_kind = [
| MethodRef of obj_c_method_ref_info
| PropertyRef of decl_ref
]
type obj_c_method_ref_info = {
  ?getter : selector option;
  ?setter : selector option
} <ocaml field_prefix="mri_">
#define obj_c_subscript_ref_expr_tuple expr_tuple * obj_c_subscript_ref_expr_info
type obj_c_subscript_ref_expr_info = {
  kind : obj_c_subscript_kind;
  ?getter : selector option;
  ?setter : selector option
} <ocaml field_prefix="osrei_">
type obj_c_subscript_kind = [ ArraySubscript | DictionarySubscript ]
#define obj_c_bool_literal_expr_tuple expr_tuple * int
type stmt = [
| GCCAsmStmt of (gcc_asm_stmt_tuple)
| MSAsmStmt of (ms_asm_stmt_tuple)
| AttributedStmt of (attributed_stmt_tuple)
| BreakStmt of (break_stmt_tuple)
| CXXCatchStmt of (cxx_catch_stmt_tuple)
| CXXForRangeStmt of (cxx_for_range_stmt_tuple)
| CXXTryStmt of (cxx_try_stmt_tuple)
| CapturedStmt of (captured_stmt_tuple)
| CompoundStmt of (compound_stmt_tuple)
| ContinueStmt of (continue_stmt_tuple)
| CoreturnStmt of (coreturn_stmt_tuple)
| CoroutineBodyStmt of (coroutine_body_stmt_tuple)
| DeclStmt of (decl_stmt_tuple)
| DoStmt of (do_stmt_tuple)
| BinaryConditionalOperator of (binary_conditional_operator_tuple)
| ConditionalOperator of (conditional_operator_tuple)
| AddrLabelExpr of (addr_label_expr_tuple)
| ArraySubscriptExpr of (array_subscript_expr_tuple)
| ArrayTypeTraitExpr of (array_type_trait_expr_tuple)
| AsTypeExpr of (as_type_expr_tuple)
| AtomicExpr of (atomic_expr_tuple)
| BinaryOperator of (binary_operator_tuple)
| CompoundAssignOperator of (compound_assign_operator_tuple)
| BlockExpr of (block_expr_tuple)
| CXXBindTemporaryExpr of (cxx_bind_temporary_expr_tuple)
| CXXBoolLiteralExpr of (cxx_bool_literal_expr_tuple)
| CXXConstructExpr of (cxx_construct_expr_tuple)
| CXXTemporaryObjectExpr of (cxx_temporary_object_expr_tuple)
| CXXDefaultArgExpr of (cxx_default_arg_expr_tuple)
| CXXDefaultInitExpr of (cxx_default_init_expr_tuple)
| CXXDeleteExpr of (cxx_delete_expr_tuple)
| CXXDependentScopeMemberExpr of (cxx_dependent_scope_member_expr_tuple)
| CXXFoldExpr of (cxx_fold_expr_tuple)
| CXXInheritedCtorInitExpr of (cxx_inherited_ctor_init_expr_tuple)
| CXXNewExpr of (cxx_new_expr_tuple)
| CXXNoexceptExpr of (cxx_noexcept_expr_tuple)
| CXXNullPtrLiteralExpr of (cxx_null_ptr_literal_expr_tuple)
| CXXPseudoDestructorExpr of (cxx_pseudo_destructor_expr_tuple)
| CXXScalarValueInitExpr of (cxx_scalar_value_init_expr_tuple)
| CXXStdInitializerListExpr of (cxx_std_initializer_list_expr_tuple)
| CXXThisExpr of (cxx_this_expr_tuple)
| CXXThrowExpr of (cxx_throw_expr_tuple)
| CXXTypeidExpr of (cxx_typeid_expr_tuple)
| CXXUnresolvedConstructExpr of (cxx_unresolved_construct_expr_tuple)
| CXXUuidofExpr of (cxx_uuidof_expr_tuple)
| CallExpr of (call_expr_tuple)
| CUDAKernelCallExpr of (cuda_kernel_call_expr_tuple)
| CXXMemberCallExpr of (cxx_member_call_expr_tuple)
| CXXOperatorCallExpr of (cxx_operator_call_expr_tuple)
| UserDefinedLiteral of (user_defined_literal_tuple)
| CStyleCastExpr of (c_style_cast_expr_tuple)
| CXXFunctionalCastExpr of (cxx_functional_cast_expr_tuple)
| CXXConstCastExpr of (cxx_const_cast_expr_tuple)
| CXXDynamicCastExpr of (cxx_dynamic_cast_expr_tuple)
| CXXReinterpretCastExpr of (cxx_reinterpret_cast_expr_tuple)
| CXXStaticCastExpr of (cxx_static_cast_expr_tuple)
| ObjCBridgedCastExpr of (obj_c_bridged_cast_expr_tuple)
| ImplicitCastExpr of (implicit_cast_expr_tuple)
| CharacterLiteral of (character_literal_tuple)
| ChooseExpr of (choose_expr_tuple)
| CompoundLiteralExpr of (compound_literal_expr_tuple)
| ConvertVectorExpr of (convert_vector_expr_tuple)
| CoawaitExpr of (coawait_expr_tuple)
| CoyieldExpr of (coyield_expr_tuple)
| DeclRefExpr of (decl_ref_expr_tuple)
| DependentScopeDeclRefExpr of (dependent_scope_decl_ref_expr_tuple)
| DesignatedInitExpr of (designated_init_expr_tuple)
| DesignatedInitUpdateExpr of (designated_init_update_expr_tuple)
| ExprWithCleanups of (expr_with_cleanups_tuple)
| ExpressionTraitExpr of (expression_trait_expr_tuple)
| ExtVectorElementExpr of (ext_vector_element_expr_tuple)
| FloatingLiteral of (floating_literal_tuple)
| FunctionParmPackExpr of (function_parm_pack_expr_tuple)
| GNUNullExpr of (gnu_null_expr_tuple)
| GenericSelectionExpr of (generic_selection_expr_tuple)
| ImaginaryLiteral of (imaginary_literal_tuple)
| ImplicitValueInitExpr of (implicit_value_init_expr_tuple)
| InitListExpr of (init_list_expr_tuple)
| IntegerLiteral of (integer_literal_tuple)
| LambdaExpr of (lambda_expr_tuple)
| MSPropertyRefExpr of (ms_property_ref_expr_tuple)
| MSPropertySubscriptExpr of (ms_property_subscript_expr_tuple)
| MaterializeTemporaryExpr of (materialize_temporary_expr_tuple)
| MemberExpr of (member_expr_tuple)
| NoInitExpr of (no_init_expr_tuple)
| OMPArraySectionExpr of (omp_array_section_expr_tuple)
| ObjCArrayLiteral of (obj_c_array_literal_tuple)
| ObjCAvailabilityCheckExpr of (obj_c_availability_check_expr_tuple)
| ObjCBoolLiteralExpr of (obj_c_bool_literal_expr_tuple)
| ObjCBoxedExpr of (obj_c_boxed_expr_tuple)
| ObjCDictionaryLiteral of (obj_c_dictionary_literal_tuple)
| ObjCEncodeExpr of (obj_c_encode_expr_tuple)
| ObjCIndirectCopyRestoreExpr of (obj_c_indirect_copy_restore_expr_tuple)
| ObjCIsaExpr of (obj_c_isa_expr_tuple)
| ObjCIvarRefExpr of (obj_c_ivar_ref_expr_tuple)
| ObjCMessageExpr of (obj_c_message_expr_tuple)
| ObjCPropertyRefExpr of (obj_c_property_ref_expr_tuple)
| ObjCProtocolExpr of (obj_c_protocol_expr_tuple)
| ObjCSelectorExpr of (obj_c_selector_expr_tuple)
| ObjCStringLiteral of (obj_c_string_literal_tuple)
| ObjCSubscriptRefExpr of (obj_c_subscript_ref_expr_tuple)
| OffsetOfExpr of (offset_of_expr_tuple)
| OpaqueValueExpr of (opaque_value_expr_tuple)
| UnresolvedLookupExpr of (unresolved_lookup_expr_tuple)
| UnresolvedMemberExpr of (unresolved_member_expr_tuple)
| PackExpansionExpr of (pack_expansion_expr_tuple)
| ParenExpr of (paren_expr_tuple)
| ParenListExpr of (paren_list_expr_tuple)
| PredefinedExpr of (predefined_expr_tuple)
| PseudoObjectExpr of (pseudo_object_expr_tuple)
| ShuffleVectorExpr of (shuffle_vector_expr_tuple)
| SizeOfPackExpr of (size_of_pack_expr_tuple)
| StmtExpr of (stmt_expr_tuple)
| StringLiteral of (string_literal_tuple)
| SubstNonTypeTemplateParmExpr of (subst_non_type_template_parm_expr_tuple)
| SubstNonTypeTemplateParmPackExpr of (subst_non_type_template_parm_pack_expr_tuple)
| TypeTraitExpr of (type_trait_expr_tuple)
| TypoExpr of (typo_expr_tuple)
| UnaryExprOrTypeTraitExpr of (unary_expr_or_type_trait_expr_tuple)
| UnaryOperator of (unary_operator_tuple)
| VAArgExpr of (va_arg_expr_tuple)
| ForStmt of (for_stmt_tuple)
| GotoStmt of (goto_stmt_tuple)
| IfStmt of (if_stmt_tuple)
| IndirectGotoStmt of (indirect_goto_stmt_tuple)
| LabelStmt of (label_stmt_tuple)
| MSDependentExistsStmt of (ms_dependent_exists_stmt_tuple)
| NullStmt of (null_stmt_tuple)
| OMPAtomicDirective of (omp_atomic_directive_tuple)
| OMPBarrierDirective of (omp_barrier_directive_tuple)
| OMPCancelDirective of (omp_cancel_directive_tuple)
| OMPCancellationPointDirective of (omp_cancellation_point_directive_tuple)
| OMPCriticalDirective of (omp_critical_directive_tuple)
| OMPFlushDirective of (omp_flush_directive_tuple)
| OMPDistributeDirective of (omp_distribute_directive_tuple)
| OMPDistributeParallelForDirective of (omp_distribute_parallel_for_directive_tuple)
| OMPDistributeParallelForSimdDirective of (omp_distribute_parallel_for_simd_directive_tuple)
| OMPDistributeSimdDirective of (omp_distribute_simd_directive_tuple)
| OMPForDirective of (omp_for_directive_tuple)
| OMPForSimdDirective of (omp_for_simd_directive_tuple)
| OMPParallelForDirective of (omp_parallel_for_directive_tuple)
| OMPParallelForSimdDirective of (omp_parallel_for_simd_directive_tuple)
| OMPSimdDirective of (omp_simd_directive_tuple)
| OMPTargetParallelForSimdDirective of (omp_target_parallel_for_simd_directive_tuple)
| OMPTargetSimdDirective of (omp_target_simd_directive_tuple)
| OMPTaskLoopDirective of (omp_task_loop_directive_tuple)
| OMPTaskLoopSimdDirective of (omp_task_loop_simd_directive_tuple)
| OMPMasterDirective of (omp_master_directive_tuple)
| OMPOrderedDirective of (omp_ordered_directive_tuple)
| OMPParallelDirective of (omp_parallel_directive_tuple)
| OMPParallelSectionsDirective of (omp_parallel_sections_directive_tuple)
| OMPSectionDirective of (omp_section_directive_tuple)
| OMPSectionsDirective of (omp_sections_directive_tuple)
| OMPSingleDirective of (omp_single_directive_tuple)
| OMPTargetDataDirective of (omp_target_data_directive_tuple)
| OMPTargetDirective of (omp_target_directive_tuple)
| OMPTargetEnterDataDirective of (omp_target_enter_data_directive_tuple)
| OMPTargetExitDataDirective of (omp_target_exit_data_directive_tuple)
| OMPTargetParallelDirective of (omp_target_parallel_directive_tuple)
| OMPTargetParallelForDirective of (omp_target_parallel_for_directive_tuple)
| OMPTargetUpdateDirective of (omp_target_update_directive_tuple)
| OMPTaskDirective of (omp_task_directive_tuple)
| OMPTaskgroupDirective of (omp_taskgroup_directive_tuple)
| OMPTaskwaitDirective of (omp_taskwait_directive_tuple)
| OMPTaskyieldDirective of (omp_taskyield_directive_tuple)
| OMPTeamsDirective of (omp_teams_directive_tuple)
| ObjCAtCatchStmt of (obj_c_at_catch_stmt_tuple)
| ObjCAtFinallyStmt of (obj_c_at_finally_stmt_tuple)
| ObjCAtSynchronizedStmt of (obj_c_at_synchronized_stmt_tuple)
| ObjCAtThrowStmt of (obj_c_at_throw_stmt_tuple)
| ObjCAtTryStmt of (obj_c_at_try_stmt_tuple)
| ObjCAutoreleasePoolStmt of (obj_c_autorelease_pool_stmt_tuple)
| ObjCForCollectionStmt of (obj_c_for_collection_stmt_tuple)
| ReturnStmt of (return_stmt_tuple)
| SEHExceptStmt of (seh_except_stmt_tuple)
| SEHFinallyStmt of (seh_finally_stmt_tuple)
| SEHLeaveStmt of (seh_leave_stmt_tuple)
| SEHTryStmt of (seh_try_stmt_tuple)
| CaseStmt of (case_stmt_tuple)
| DefaultStmt of (default_stmt_tuple)
| SwitchStmt of (switch_stmt_tuple)
| WhileStmt of (while_stmt_tuple)
] <ocaml repr="classic" validator="Clang_ast_visit.visit_stmt">
#define block_content_comment_tuple comment_tuple
#define block_command_comment_tuple block_content_comment_tuple
#define param_command_comment_tuple block_command_comment_tuple
#define t_param_command_comment_tuple block_command_comment_tuple
#define verbatim_block_comment_tuple block_command_comment_tuple
#define verbatim_line_comment_tuple block_command_comment_tuple
#define paragraph_comment_tuple block_content_comment_tuple
#define full_comment_tuple comment_tuple
#define inline_content_comment_tuple comment_tuple
#define html_tag_comment_tuple inline_content_comment_tuple
#define html_end_tag_comment_tuple html_tag_comment_tuple
#define html_start_tag_comment_tuple html_tag_comment_tuple
#define inline_command_comment_tuple inline_content_comment_tuple
#define text_comment_tuple inline_content_comment_tuple
#define verbatim_block_line_comment_tuple comment_tuple
#define comment_tuple comment_info * comment list
type comment_info = {
  parent_pointer : pointer;
  source_range : source_range;
} <ocaml field_prefix="ci_">
#define text_comment_tuple comment_tuple * string
type comment = [
| BlockCommandComment of (block_command_comment_tuple)
| ParamCommandComment of (param_command_comment_tuple)
| TParamCommandComment of (t_param_command_comment_tuple)
| VerbatimBlockComment of (verbatim_block_comment_tuple)
| VerbatimLineComment of (verbatim_line_comment_tuple)
| ParagraphComment of (paragraph_comment_tuple)
| FullComment of (full_comment_tuple)
| HTMLEndTagComment of (html_end_tag_comment_tuple)
| HTMLStartTagComment of (html_start_tag_comment_tuple)
| InlineCommandComment of (inline_command_comment_tuple)
| TextComment of (text_comment_tuple)
| VerbatimBlockLineComment of (verbatim_block_line_comment_tuple)
] <ocaml repr="classic">
#define none_type_tuple type_tuple
#define builtin_type_tuple type_tuple
#define complex_type_tuple type_tuple
#define pointer_type_tuple type_tuple
#define block_pointer_type_tuple type_tuple
#define reference_type_tuple type_tuple
#define l_value_reference_type_tuple reference_type_tuple
#define r_value_reference_type_tuple reference_type_tuple
#define member_pointer_type_tuple type_tuple
#define array_type_tuple type_tuple
#define constant_array_type_tuple array_type_tuple
#define incomplete_array_type_tuple array_type_tuple
#define variable_array_type_tuple array_type_tuple
#define dependent_sized_array_type_tuple array_type_tuple
#define dependent_sized_ext_vector_type_tuple type_tuple
#define vector_type_tuple type_tuple
#define ext_vector_type_tuple vector_type_tuple
#define function_type_tuple type_tuple
#define function_proto_type_tuple function_type_tuple
#define function_no_proto_type_tuple function_type_tuple
#define unresolved_using_type_tuple type_tuple
#define paren_type_tuple type_tuple
#define typedef_type_tuple type_tuple
#define adjusted_type_tuple type_tuple
#define decayed_type_tuple adjusted_type_tuple
#define type_of_expr_type_tuple type_tuple
#define type_of_type_tuple type_tuple
#define decltype_type_tuple type_tuple
#define unary_transform_type_tuple type_tuple
#define tag_type_tuple type_tuple
#define record_type_tuple tag_type_tuple
#define enum_type_tuple tag_type_tuple
#define elaborated_type_tuple type_tuple
#define attributed_type_tuple type_tuple
#define template_type_parm_type_tuple type_tuple
#define subst_template_type_parm_type_tuple type_tuple
#define subst_template_type_parm_pack_type_tuple type_tuple
#define template_specialization_type_tuple type_tuple
#define auto_type_tuple type_tuple
#define injected_class_name_type_tuple type_tuple
#define dependent_name_type_tuple type_tuple
#define dependent_template_specialization_type_tuple type_tuple
#define pack_expansion_type_tuple type_tuple
#define obj_c_object_type_tuple type_tuple
#define obj_c_interface_type_tuple obj_c_object_type_tuple
#define obj_c_object_pointer_type_tuple type_tuple
#define pipe_type_tuple type_tuple
#define atomic_type_tuple type_tuple
type type_ptr = int wrap <ocaml t="Clang_ast_types.t_ptr"
                             wrap="Clang_ast_types.pointer_to_type_ptr"
                             unwrap="Clang_ast_types.type_ptr_to_pointer">
#define type_tuple type_info
type type_info = {
  pointer : pointer;
  ?desugared_type : type_ptr option;
} <ocaml field_prefix="ti_">
#define type_with_child_info type_info * type_ptr
#define qual_type_with_child_info type_info * qual_type
#define adjusted_type_tuple type_with_child_info
#define array_type_tuple type_with_child_info
#define constant_array_type_tuple array_type_tuple * int
#define atomic_type_tuple type_with_child_info
type type_attribute_kind = [
  | AddressSpace
  | Regparm
  | VectorSize
  | NeonVectorSize
  | NeonPolyVectorSize
  | ObjcGc
  | ObjcOwnership
  | Pcs
  | PcsVfp
  | Noreturn
  | Cdecl
  | Fastcall
  | Stdcall
  | Thiscall
  | Pascal
  | Vectorcall
  | Inteloclbicc
  | MsAbi
  | SysvAbi
  | Ptr32
  | Ptr64
  | Sptr
  | Uptr
  | Nonnull
  | Nullable
  | NullUnspecified
  | ObjcKindof
  | ObjcInsertUnsafeUnretained
]
type objc_lifetime_attr = [
  | OCL_None
  | OCL_ExplicitNone
  | OCL_Strong
  | OCL_Weak
  | OCL_Autoreleasing
]
#define attributed_type_tuple type_tuple * attr_type_info
type attr_type_info = {
  attr_kind : type_attribute_kind;
  ~lifetime <ocaml default="`OCL_None"> : objc_lifetime_attr
} <ocaml field_prefix="ati_">
#define block_pointer_type_tuple type_with_child_info
#define builtin_type_tuple type_tuple * builtin_type_kind
type builtin_type_kind = [
| Void
| Bool
| Char_U
| UChar
| WChar_U
| Char16
| Char32
| UShort
| UInt
| ULong
| ULongLong
| UInt128
| Char_S
| SChar
| WChar_S
| Short
| Int
| Long
| LongLong
| Int128
| Half
| Float
| Double
| LongDouble
| Float128
| NullPtr
| ObjCId
| ObjCClass
| ObjCSel
| OCLSampler
| OCLEvent
| OCLClkEvent
| OCLQueue
| OCLNDRange
| OCLReserveID
| Dependent
| Overload
| BoundMember
| PseudoObject
| UnknownAny
| BuiltinFn
| ARCUnbridgedCast
| OMPArraySection
]
#define decltype_type_tuple type_with_child_info
#define function_type_tuple type_tuple * function_type_info
type function_type_info = {
  return_type : type_ptr
} <ocaml field_prefix="fti_">
#define function_proto_type_tuple function_type_tuple * params_type_info
type params_type_info = {
  ~params_type : type_ptr list
} <ocaml field_prefix="pti_">
#define member_pointer_type_tuple type_with_child_info
#define obj_c_object_pointer_type_tuple qual_type_with_child_info
#define obj_c_object_type_tuple type_tuple * objc_object_type_info
type objc_object_type_info = {
  base_type : type_ptr;
  ~protocol_decls_ptr : pointer list;
} <ocaml prefix="ooti_">
#define obj_c_interface_type_tuple type_tuple * pointer
#define paren_type_tuple type_with_child_info
#define pointer_type_tuple qual_type_with_child_info
#define reference_type_tuple qual_type_with_child_info
#define tag_type_tuple type_tuple * pointer
#define typedef_type_tuple type_tuple * typedef_type_info
type typedef_type_info = {
  child_type : type_ptr;
  decl_ptr : pointer;
} <ocaml field_prefix="tti_">
type c_type = [
| NoneType of (none_type_tuple)
| BuiltinType of (builtin_type_tuple)
| ComplexType of (complex_type_tuple)
| PointerType of (pointer_type_tuple)
| BlockPointerType of (block_pointer_type_tuple)
| LValueReferenceType of (l_value_reference_type_tuple)
| RValueReferenceType of (r_value_reference_type_tuple)
| MemberPointerType of (member_pointer_type_tuple)
| ConstantArrayType of (constant_array_type_tuple)
| IncompleteArrayType of (incomplete_array_type_tuple)
| VariableArrayType of (variable_array_type_tuple)
| DependentSizedArrayType of (dependent_sized_array_type_tuple)
| DependentSizedExtVectorType of (dependent_sized_ext_vector_type_tuple)
| VectorType of (vector_type_tuple)
| ExtVectorType of (ext_vector_type_tuple)
| FunctionProtoType of (function_proto_type_tuple)
| FunctionNoProtoType of (function_no_proto_type_tuple)
| UnresolvedUsingType of (unresolved_using_type_tuple)
| ParenType of (paren_type_tuple)
| TypedefType of (typedef_type_tuple)
| AdjustedType of (adjusted_type_tuple)
| DecayedType of (decayed_type_tuple)
| TypeOfExprType of (type_of_expr_type_tuple)
| TypeOfType of (type_of_type_tuple)
| DecltypeType of (decltype_type_tuple)
| UnaryTransformType of (unary_transform_type_tuple)
| RecordType of (record_type_tuple)
| EnumType of (enum_type_tuple)
| ElaboratedType of (elaborated_type_tuple)
| AttributedType of (attributed_type_tuple)
| TemplateTypeParmType of (template_type_parm_type_tuple)
| SubstTemplateTypeParmType of (subst_template_type_parm_type_tuple)
| SubstTemplateTypeParmPackType of (subst_template_type_parm_pack_type_tuple)
| TemplateSpecializationType of (template_specialization_type_tuple)
| AutoType of (auto_type_tuple)
| InjectedClassNameType of (injected_class_name_type_tuple)
| DependentNameType of (dependent_name_type_tuple)
| DependentTemplateSpecializationType of (dependent_template_specialization_type_tuple)
| PackExpansionType of (pack_expansion_type_tuple)
| ObjCObjectType of (obj_c_object_type_tuple)
| ObjCInterfaceType of (obj_c_interface_type_tuple)
| ObjCObjectPointerType of (obj_c_object_pointer_type_tuple)
| PipeType of (pipe_type_tuple)
| AtomicType of (atomic_type_tuple)
] <ocaml repr="classic" validator="Clang_ast_visit.visit_type">
