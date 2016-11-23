(* Auto-generated from "clang_ast.atd" *)


type binary_operator_kind = Clang_ast_t.binary_operator_kind

type binary_operator_info = Clang_ast_t.binary_operator_info = {
  boi_kind (*atd kind *): binary_operator_kind
}

type builtin_type_kind = Clang_ast_t.builtin_type_kind

type cast_kind = Clang_ast_t.cast_kind

type cxx_base_specifier = Clang_ast_t.cxx_base_specifier = {
  xbs_name (*atd name *): string;
  xbs_virtual (*atd virtual *): bool
}

type cast_expr_info = Clang_ast_t.cast_expr_info = {
  cei_cast_kind (*atd cast_kind *): cast_kind;
  cei_base_path (*atd base_path *): cxx_base_specifier list
}

type cxx_noexcept_expr_info = Clang_ast_t.cxx_noexcept_expr_info = {
  xnee_value (*atd value *): bool
}

type decl_context_info = Clang_ast_t.decl_context_info = {
  dci_has_external_lexical_storage (*atd has_external_lexical_storage *):
    bool;
  dci_has_external_visible_storage (*atd has_external_visible_storage *):
    bool
}

type decl_kind = Clang_ast_t.decl_kind

type declaration_name_kind = Clang_ast_t.declaration_name_kind

type declaration_name = Clang_ast_t.declaration_name = {
  dn_kind (*atd kind *): declaration_name_kind;
  dn_name (*atd name *): string
}

type enum_decl_scope = Clang_ast_t.enum_decl_scope

type enum_decl_info = Clang_ast_t.enum_decl_info = {
  edi_scope (*atd scope *): enum_decl_scope option;
  edi_is_module_private (*atd is_module_private *): bool
}

type input_kind = Clang_ast_t.input_kind

type integer_literal_info = Clang_ast_t.integer_literal_info = {
  ili_is_signed (*atd is_signed *): bool;
  ili_bitwidth (*atd bitwidth *): int;
  ili_value (*atd value *): string
}

type lambda_capture_kind = Clang_ast_t.lambda_capture_kind

type named_decl_info = Clang_ast_t.named_decl_info = {
  ni_name (*atd name *): string;
  ni_qual_name (*atd qual_name *): string list
}

type obj_c_access_control = Clang_ast_t.obj_c_access_control

type obj_c_ivar_decl_info = Clang_ast_t.obj_c_ivar_decl_info = {
  ovdi_is_synthesize (*atd is_synthesize *): bool;
  ovdi_access_control (*atd access_control *): obj_c_access_control
}

type obj_c_property_control = Clang_ast_t.obj_c_property_control

type obj_c_subscript_kind = Clang_ast_t.obj_c_subscript_kind

type objc_lifetime_attr = Clang_ast_t.objc_lifetime_attr

type object_kind = Clang_ast_t.object_kind

type opt_type = Clang_ast_t.opt_type

type pointer = Clang_ast_t.pointer

type addr_label_expr_info = Clang_ast_t.addr_label_expr_info = {
  alei_label (*atd label *): string;
  alei_pointer (*atd pointer *): pointer
}

type cxx_new_expr_info = Clang_ast_t.cxx_new_expr_info = {
  xnei_is_array (*atd is_array *): bool;
  xnei_array_size_expr (*atd array_size_expr *): pointer option;
  xnei_initializer_expr (*atd initializer_expr *): pointer option
}

type cxx_temporary = Clang_ast_t.cxx_temporary

type cxx_bind_temporary_expr_info =
  Clang_ast_t.cxx_bind_temporary_expr_info = {
  xbtei_cxx_temporary (*atd cxx_temporary *): cxx_temporary
}

type goto_stmt_info = Clang_ast_t.goto_stmt_info = {
  gsi_label (*atd label *): string;
  gsi_pointer (*atd pointer *): pointer
}

type predefined_expr_type = Clang_ast_t.predefined_expr_type

type previous_decl = Clang_ast_t.previous_decl

type property_attribute = Clang_ast_t.property_attribute

type property_implementation = Clang_ast_t.property_implementation

type record_decl_info = Clang_ast_t.record_decl_info = {
  rdi_is_module_private (*atd is_module_private *): bool;
  rdi_is_complete_definition (*atd is_complete_definition *): bool
}

type selector = Clang_ast_t.selector

type obj_c_method_ref_info = Clang_ast_t.obj_c_method_ref_info = {
  mri_getter (*atd getter *): selector option;
  mri_setter (*atd setter *): selector option
}

type obj_c_subscript_ref_expr_info =
  Clang_ast_t.obj_c_subscript_ref_expr_info = {
  osrei_kind (*atd kind *): obj_c_subscript_kind;
  osrei_getter (*atd getter *): selector option;
  osrei_setter (*atd setter *): selector option
}

type objc_boxed_expr_info = Clang_ast_t.objc_boxed_expr_info = {
  obei_boxing_method (*atd boxing_method *): selector option
}

type source_location = Clang_ast_t.source_location = {
  mutable sl_file (*atd file *): string option;
  mutable sl_line (*atd line *): int option;
  mutable sl_column (*atd column *): int option
}

type source_range = Clang_ast_t.source_range

type attribute_info = Clang_ast_t.attribute_info = {
  ai_pointer (*atd pointer *): pointer;
  ai_source_range (*atd source_range *): source_range;
  ai_parameters (*atd parameters *): string list;
  ai_is_inherited (*atd is_inherited *): bool;
  ai_is_implicit (*atd is_implicit *): bool
}

type attribute = Clang_ast_t.attribute = 
    FallThroughAttr of attribute_info
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


type comment_info = Clang_ast_t.comment_info = {
  ci_parent_pointer (*atd parent_pointer *): pointer;
  ci_source_range (*atd source_range *): source_range
}

type specifier_kind = Clang_ast_t.specifier_kind

type stmt_info = Clang_ast_t.stmt_info = {
  si_pointer (*atd pointer *): pointer;
  si_source_range (*atd source_range *): source_range
}

type tls_kind = Clang_ast_t.tls_kind

type type_attribute_kind = Clang_ast_t.type_attribute_kind

type attr_type_info = Clang_ast_t.attr_type_info = {
  ati_attr_kind (*atd attr_kind *): type_attribute_kind;
  ati_lifetime (*atd lifetime *): objc_lifetime_attr
}

type type_ptr = Clang_ast_t.type_ptr

type compound_assign_operator_info =
  Clang_ast_t.compound_assign_operator_info = {
  caoi_lhs_type (*atd lhs_type *): type_ptr;
  caoi_result_type (*atd result_type *): type_ptr
}

type cxx_delete_expr_info = Clang_ast_t.cxx_delete_expr_info = {
  xdei_is_array (*atd is_array *): bool;
  xdei_destroyed_type (*atd destroyed_type *): type_ptr
}

type decl_ref = Clang_ast_t.decl_ref = {
  dr_kind (*atd kind *): decl_kind;
  dr_decl_pointer (*atd decl_pointer *): pointer;
  dr_name (*atd name *): named_decl_info option;
  dr_is_hidden (*atd is_hidden *): bool;
  dr_type_ptr (*atd type_ptr *): type_ptr option
}

type cxx_construct_expr_info = Clang_ast_t.cxx_construct_expr_info = {
  xcei_decl_ref (*atd decl_ref *): decl_ref;
  xcei_is_elidable (*atd is_elidable *): bool;
  xcei_requires_zero_initialization (*atd requires_zero_initialization *):
    bool
}

type cxx_ctor_initializer_subject = Clang_ast_t.cxx_ctor_initializer_subject

type cxx_record_decl_info = Clang_ast_t.cxx_record_decl_info = {
  xrdi_bases (*atd bases *): type_ptr list;
  xrdi_vbases (*atd vbases *): type_ptr list;
  xrdi_is_pod (*atd is_pod *): bool;
  xrdi_destructor (*atd destructor *): decl_ref option;
  xrdi_lambda_call_operator (*atd lambda_call_operator *): decl_ref option
}

type decl_ref_expr_info = Clang_ast_t.decl_ref_expr_info = {
  drti_decl_ref (*atd decl_ref *): decl_ref option;
  drti_found_decl_ref (*atd found_decl_ref *): decl_ref option
}

type expr_with_cleanups_info = Clang_ast_t.expr_with_cleanups_info = {
  ewci_decl_refs (*atd decl_refs *): decl_ref list
}

type function_type_info = Clang_ast_t.function_type_info = {
  fti_return_type (*atd return_type *): type_ptr
}

type lambda_capture_info = Clang_ast_t.lambda_capture_info = {
  lci_capture_kind (*atd capture_kind *): lambda_capture_kind;
  lci_capture_this (*atd capture_this *): bool;
  lci_capture_variable (*atd capture_variable *): bool;
  lci_capture_VLAtype (*atd capture_VLAtype *): bool;
  lci_captured_var (*atd captured_var *): decl_ref option;
  lci_is_implicit (*atd is_implicit *): bool;
  lci_location (*atd location *): source_range;
  lci_is_pack_expansion (*atd is_pack_expansion *): bool
}

type materialize_temporary_expr_info =
  Clang_ast_t.materialize_temporary_expr_info = {
  mtei_decl_ref (*atd decl_ref *): decl_ref option
}

type member_expr_info = Clang_ast_t.member_expr_info = {
  mei_is_arrow (*atd is_arrow *): bool;
  mei_performs_virtual_dispatch (*atd performs_virtual_dispatch *): bool;
  mei_name (*atd name *): named_decl_info;
  mei_decl_ref (*atd decl_ref *): decl_ref
}

type namespace_decl_info = Clang_ast_t.namespace_decl_info = {
  ndi_is_inline (*atd is_inline *): bool;
  ndi_original_namespace (*atd original_namespace *): decl_ref option
}

type nested_name_specifier_loc = Clang_ast_t.nested_name_specifier_loc = {
  nnsl_kind (*atd kind *): specifier_kind;
  nnsl_ref (*atd ref *): decl_ref option
}

type namespace_alias_decl_info = Clang_ast_t.namespace_alias_decl_info = {
  nadi_namespace_loc (*atd namespace_loc *): source_location;
  nadi_target_name_loc (*atd target_name_loc *): source_location;
  nadi_nested_name_specifier_locs (*atd nested_name_specifier_locs *):
    nested_name_specifier_loc list;
  nadi_namespace (*atd namespace *): decl_ref
}

type obj_c_category_decl_info = Clang_ast_t.obj_c_category_decl_info = {
  odi_class_interface (*atd class_interface *): decl_ref option;
  odi_implementation (*atd implementation *): decl_ref option;
  odi_protocols (*atd protocols *): decl_ref list
}

type obj_c_category_impl_decl_info =
  Clang_ast_t.obj_c_category_impl_decl_info = {
  ocidi_class_interface (*atd class_interface *): decl_ref option;
  ocidi_category_decl (*atd category_decl *): decl_ref option
}

type obj_c_compatible_alias_decl_info =
  Clang_ast_t.obj_c_compatible_alias_decl_info = {
  ocadi_class_interface (*atd class_interface *): decl_ref option
}

type obj_c_interface_decl_info = Clang_ast_t.obj_c_interface_decl_info = {
  otdi_super (*atd super *): decl_ref option;
  otdi_implementation (*atd implementation *): decl_ref option;
  otdi_protocols (*atd protocols *): decl_ref list;
  otdi_known_categories (*atd known_categories *): decl_ref list
}

type obj_c_ivar_ref_expr_info = Clang_ast_t.obj_c_ivar_ref_expr_info = {
  ovrei_decl_ref (*atd decl_ref *): decl_ref;
  ovrei_pointer (*atd pointer *): pointer;
  ovrei_is_free_ivar (*atd is_free_ivar *): bool
}

type obj_c_property_decl_info = Clang_ast_t.obj_c_property_decl_info = {
  opdi_type_ptr (*atd type_ptr *): type_ptr;
  opdi_getter_method (*atd getter_method *): decl_ref option;
  opdi_setter_method (*atd setter_method *): decl_ref option;
  opdi_ivar_decl (*atd ivar_decl *): decl_ref option;
  opdi_property_control (*atd property_control *): obj_c_property_control;
  opdi_property_attributes (*atd property_attributes *):
    property_attribute list
}

type obj_c_property_impl_decl_info =
  Clang_ast_t.obj_c_property_impl_decl_info = {
  opidi_implementation (*atd implementation *): property_implementation;
  opidi_property_decl (*atd property_decl *): decl_ref option;
  opidi_ivar_decl (*atd ivar_decl *): decl_ref option
}

type obj_c_protocol_decl_info = Clang_ast_t.obj_c_protocol_decl_info = {
  opcdi_protocols (*atd protocols *): decl_ref list
}

type objc_encode_expr_info = Clang_ast_t.objc_encode_expr_info = {
  oeei_type_ptr (*atd type_ptr *): type_ptr;
  oeei_raw (*atd raw *): string
}

type objc_object_type_info = Clang_ast_t.objc_object_type_info = {
  base_type: type_ptr;
  protocol_decls_ptr: pointer list
}

type overload_expr_info = Clang_ast_t.overload_expr_info = {
  oei_decls (*atd decls *): decl_ref list;
  oei_name (*atd name *): declaration_name
}

type params_type_info = Clang_ast_t.params_type_info = {
  pti_params_type (*atd params_type *): type_ptr list
}

type property_ref_kind = Clang_ast_t.property_ref_kind

type obj_c_property_ref_expr_info =
  Clang_ast_t.obj_c_property_ref_expr_info = {
  oprei_kind (*atd kind *): property_ref_kind;
  oprei_is_super_receiver (*atd is_super_receiver *): bool;
  oprei_is_messaging_getter (*atd is_messaging_getter *): bool;
  oprei_is_messaging_setter (*atd is_messaging_setter *): bool
}

type qual_type = Clang_ast_t.qual_type = {
  qt_type_ptr (*atd type_ptr *): type_ptr;
  qt_is_const (*atd is_const *): bool
}

type receiver_kind = Clang_ast_t.receiver_kind

type obj_c_message_expr_info = Clang_ast_t.obj_c_message_expr_info = {
  omei_selector (*atd selector *): string;
  omei_is_definition_found (*atd is_definition_found *): bool;
  omei_decl_pointer (*atd decl_pointer *): pointer option;
  omei_receiver_kind (*atd receiver_kind *): receiver_kind
}

type template_instantiation_arg_info =
  Clang_ast_t.template_instantiation_arg_info

type type_info = Clang_ast_t.type_info = {
  ti_pointer (*atd pointer *): pointer;
  ti_desugared_type (*atd desugared_type *): type_ptr option
}

type type_trait_info = Clang_ast_t.type_trait_info = {
  xtti_value (*atd value *): bool
}

type typedef_decl_info = Clang_ast_t.typedef_decl_info = {
  tdi_is_module_private (*atd is_module_private *): bool
}

type typedef_type_info = Clang_ast_t.typedef_type_info = {
  tti_child_type (*atd child_type *): type_ptr;
  tti_decl_ptr (*atd decl_ptr *): pointer
}

type c_type = Clang_ast_t.c_type = 
    NoneType of (type_info)
  | BuiltinType of (type_info * builtin_type_kind)
  | ComplexType of (type_info)
  | PointerType of (type_info * qual_type)
  | BlockPointerType of (type_info * type_ptr)
  | LValueReferenceType of (type_info * qual_type)
  | RValueReferenceType of (type_info * qual_type)
  | MemberPointerType of (type_info * type_ptr)
  | ConstantArrayType of (type_info * type_ptr * int)
  | IncompleteArrayType of (type_info * type_ptr)
  | VariableArrayType of (type_info * type_ptr)
  | DependentSizedArrayType of (type_info * type_ptr)
  | DependentSizedExtVectorType of (type_info)
  | VectorType of (type_info)
  | ExtVectorType of (type_info)
  | FunctionProtoType of (type_info * function_type_info * params_type_info)
  | FunctionNoProtoType of (type_info * function_type_info)
  | UnresolvedUsingType of (type_info)
  | ParenType of (type_info * type_ptr)
  | TypedefType of (type_info * typedef_type_info)
  | AdjustedType of (type_info * type_ptr)
  | DecayedType of (type_info * type_ptr)
  | TypeOfExprType of (type_info)
  | TypeOfType of (type_info)
  | DecltypeType of (type_info * type_ptr)
  | UnaryTransformType of (type_info)
  | RecordType of (type_info * pointer)
  | EnumType of (type_info * pointer)
  | ElaboratedType of (type_info)
  | AttributedType of (type_info * attr_type_info)
  | TemplateTypeParmType of (type_info)
  | SubstTemplateTypeParmType of (type_info)
  | SubstTemplateTypeParmPackType of (type_info)
  | TemplateSpecializationType of (type_info)
  | AutoType of (type_info)
  | InjectedClassNameType of (type_info)
  | DependentNameType of (type_info)
  | DependentTemplateSpecializationType of (type_info)
  | PackExpansionType of (type_info)
  | ObjCObjectType of (type_info * objc_object_type_info)
  | ObjCInterfaceType of (type_info * pointer)
  | ObjCObjectPointerType of (type_info * qual_type)
  | PipeType of (type_info)
  | AtomicType of (type_info * type_ptr)


type translation_unit_decl_info = Clang_ast_t.translation_unit_decl_info = {
  tudi_input_path (*atd input_path *): string;
  tudi_input_kind (*atd input_kind *): input_kind;
  tudi_arc_enabled (*atd arc_enabled *): bool;
  tudi_types (*atd types *): c_type list
}

type unary_expr_or_type_trait_kind =
  Clang_ast_t.unary_expr_or_type_trait_kind

type unary_expr_or_type_trait_expr_info =
  Clang_ast_t.unary_expr_or_type_trait_expr_info = {
  uttei_kind (*atd kind *): unary_expr_or_type_trait_kind;
  uttei_type_ptr (*atd type_ptr *): type_ptr option
}

type unary_operator_kind = Clang_ast_t.unary_operator_kind

type unary_operator_info = Clang_ast_t.unary_operator_info = {
  uoi_kind (*atd kind *): unary_operator_kind;
  uoi_is_postfix (*atd is_postfix *): bool
}

type unresolved_lookup_expr_info = Clang_ast_t.unresolved_lookup_expr_info = {
  ulei_requires_ADL (*atd requires_ADL *): bool;
  ulei_is_overloaded (*atd is_overloaded *): bool;
  ulei_naming_class (*atd naming_class *): decl_ref option
}

type using_directive_decl_info = Clang_ast_t.using_directive_decl_info = {
  uddi_using_location (*atd using_location *): source_location;
  uddi_namespace_key_location (*atd namespace_key_location *):
    source_location;
  uddi_nested_name_specifier_locs (*atd nested_name_specifier_locs *):
    nested_name_specifier_loc list;
  uddi_nominated_namespace (*atd nominated_namespace *): decl_ref option
}

type value_kind = Clang_ast_t.value_kind

type expr_info = Clang_ast_t.expr_info = {
  ei_type_ptr (*atd type_ptr *): type_ptr;
  ei_value_kind (*atd value_kind *): value_kind;
  ei_object_kind (*atd object_kind *): object_kind
}

type comment = Clang_ast_t.comment = 
    BlockCommandComment of (comment_info * comment list)
  | ParamCommandComment of (comment_info * comment list)
  | TParamCommandComment of (comment_info * comment list)
  | VerbatimBlockComment of (comment_info * comment list)
  | VerbatimLineComment of (comment_info * comment list)
  | ParagraphComment of (comment_info * comment list)
  | FullComment of (comment_info * comment list)
  | HTMLEndTagComment of (comment_info * comment list)
  | HTMLStartTagComment of (comment_info * comment list)
  | InlineCommandComment of (comment_info * comment list)
  | TextComment of (comment_info * comment list * string)
  | VerbatimBlockLineComment of (comment_info * comment list)


type decl_info = Clang_ast_t.decl_info = {
  di_pointer (*atd pointer *): pointer;
  di_parent_pointer (*atd parent_pointer *): pointer option;
  di_previous_decl (*atd previous_decl *): previous_decl;
  di_source_range (*atd source_range *): source_range;
  di_owning_module (*atd owning_module *): string option;
  di_is_hidden (*atd is_hidden *): bool;
  di_is_implicit (*atd is_implicit *): bool;
  di_is_used (*atd is_used *): bool;
  di_is_this_declaration_referenced (*atd is_this_declaration_referenced *):
    bool;
  di_is_invalid_decl (*atd is_invalid_decl *): bool;
  di_attributes (*atd attributes *): attribute list;
  di_full_comment (*atd full_comment *): comment option
}

type block_captured_variable = Clang_ast_t.block_captured_variable = {
  bcv_is_by_ref (*atd is_by_ref *): bool;
  bcv_is_nested (*atd is_nested *): bool;
  bcv_variable (*atd variable *): decl_ref option;
  bcv_copy_expr (*atd copy_expr *): stmt option
}

and block_decl_info = Clang_ast_t.block_decl_info = {
  bdi_parameters (*atd parameters *): decl list;
  bdi_is_variadic (*atd is_variadic *): bool;
  bdi_captures_cxx_this (*atd captures_cxx_this *): bool;
  bdi_captured_variables (*atd captured_variables *):
    block_captured_variable list;
  bdi_body (*atd body *): stmt option
}

and cxx_catch_stmt_info = Clang_ast_t.cxx_catch_stmt_info = {
  xcsi_variable (*atd variable *): decl option
}

and cxx_ctor_initializer = Clang_ast_t.cxx_ctor_initializer = {
  xci_subject (*atd subject *): cxx_ctor_initializer_subject;
  xci_source_range (*atd source_range *): source_range;
  xci_init_expr (*atd init_expr *): stmt option
}

and cxx_default_expr_info = Clang_ast_t.cxx_default_expr_info = {
  xdaei_init_expr (*atd init_expr *): stmt option
}

and cxx_method_decl_info = Clang_ast_t.cxx_method_decl_info = {
  xmdi_is_virtual (*atd is_virtual *): bool;
  xmdi_is_static (*atd is_static *): bool;
  xmdi_cxx_ctor_initializers (*atd cxx_ctor_initializers *):
    cxx_ctor_initializer list;
  xmdi_overriden_methods (*atd overriden_methods *): decl_ref list
}

and decl = Clang_ast_t.decl = 
    AccessSpecDecl of (decl_info)
  | BlockDecl of (decl_info * block_decl_info)
  | CapturedDecl of (decl_info * decl list * decl_context_info)
  | ClassScopeFunctionSpecializationDecl of (decl_info)
  | EmptyDecl of (decl_info)
  | ExternCContextDecl of (decl_info)
  | FileScopeAsmDecl of (decl_info * string)
  | FriendDecl of (decl_info * friend_info)
  | FriendTemplateDecl of (decl_info)
  | ImportDecl of (decl_info * string)
  | LinkageSpecDecl of (decl_info * decl list * decl_context_info)
  | LabelDecl of (decl_info * named_decl_info)
  | NamespaceDecl
      of (
          decl_info
        * named_decl_info
        * decl list
        * decl_context_info
        * namespace_decl_info
      )
  | NamespaceAliasDecl
      of (decl_info * named_decl_info * namespace_alias_decl_info)
  | ObjCCompatibleAliasDecl
      of (decl_info * named_decl_info * obj_c_compatible_alias_decl_info)
  | ObjCCategoryDecl
      of (
          decl_info
        * named_decl_info
        * decl list
        * decl_context_info
        * obj_c_category_decl_info
      )
  | ObjCCategoryImplDecl
      of (
          decl_info
        * named_decl_info
        * decl list
        * decl_context_info
        * obj_c_category_impl_decl_info
      )
  | ObjCImplementationDecl
      of (
          decl_info
        * named_decl_info
        * decl list
        * decl_context_info
        * obj_c_implementation_decl_info
      )
  | ObjCInterfaceDecl
      of (
          decl_info
        * named_decl_info
        * decl list
        * decl_context_info
        * obj_c_interface_decl_info
      )
  | ObjCProtocolDecl
      of (
          decl_info
        * named_decl_info
        * decl list
        * decl_context_info
        * obj_c_protocol_decl_info
      )
  | ObjCMethodDecl of (decl_info * named_decl_info * obj_c_method_decl_info)
  | ObjCPropertyDecl
      of (decl_info * named_decl_info * obj_c_property_decl_info)
  | BuiltinTemplateDecl of (decl_info * named_decl_info)
  | ClassTemplateDecl of (decl_info * named_decl_info * template_decl_info)
  | FunctionTemplateDecl
      of (decl_info * named_decl_info * template_decl_info)
  | TypeAliasTemplateDecl of (decl_info * named_decl_info)
  | VarTemplateDecl of (decl_info * named_decl_info)
  | TemplateTemplateParmDecl of (decl_info * named_decl_info)
  | EnumDecl
      of (
          decl_info
        * named_decl_info
        * opt_type
        * type_ptr
        * decl list
        * decl_context_info
        * enum_decl_info
      )
  | RecordDecl
      of (
          decl_info
        * named_decl_info
        * opt_type
        * type_ptr
        * decl list
        * decl_context_info
        * record_decl_info
      )
  | CXXRecordDecl
      of (
          decl_info
        * named_decl_info
        * opt_type
        * type_ptr
        * decl list
        * decl_context_info
        * record_decl_info
        * cxx_record_decl_info
      )
  | ClassTemplateSpecializationDecl
      of (
          decl_info
        * named_decl_info
        * opt_type
        * type_ptr
        * decl list
        * decl_context_info
        * record_decl_info
        * cxx_record_decl_info
        * template_instantiation_arg_info list
      )
  | ClassTemplatePartialSpecializationDecl
      of (
          decl_info
        * named_decl_info
        * opt_type
        * type_ptr
        * decl list
        * decl_context_info
        * record_decl_info
        * cxx_record_decl_info
        * template_instantiation_arg_info list
      )
  | TemplateTypeParmDecl
      of (decl_info * named_decl_info * opt_type * type_ptr)
  | ObjCTypeParamDecl of (decl_info * named_decl_info * opt_type * type_ptr)
  | TypeAliasDecl of (decl_info * named_decl_info * opt_type * type_ptr)
  | TypedefDecl
      of (
          decl_info
        * named_decl_info
        * opt_type
        * type_ptr
        * typedef_decl_info
      )
  | UnresolvedUsingTypenameDecl
      of (decl_info * named_decl_info * opt_type * type_ptr)
  | UsingDecl of (decl_info * named_decl_info)
  | UsingDirectiveDecl
      of (decl_info * named_decl_info * using_directive_decl_info)
  | UsingShadowDecl of (decl_info * named_decl_info)
  | ConstructorUsingShadowDecl of (decl_info * named_decl_info)
  | BindingDecl of (decl_info * named_decl_info * qual_type)
  | FieldDecl of (decl_info * named_decl_info * qual_type * field_decl_info)
  | ObjCAtDefsFieldDecl
      of (decl_info * named_decl_info * qual_type * field_decl_info)
  | ObjCIvarDecl
      of (
          decl_info
        * named_decl_info
        * qual_type
        * field_decl_info
        * obj_c_ivar_decl_info
      )
  | FunctionDecl
      of (decl_info * named_decl_info * qual_type * function_decl_info)
  | CXXMethodDecl
      of (
          decl_info
        * named_decl_info
        * qual_type
        * function_decl_info
        * cxx_method_decl_info
      )
  | CXXConstructorDecl
      of (
          decl_info
        * named_decl_info
        * qual_type
        * function_decl_info
        * cxx_method_decl_info
      )
  | CXXConversionDecl
      of (
          decl_info
        * named_decl_info
        * qual_type
        * function_decl_info
        * cxx_method_decl_info
      )
  | CXXDestructorDecl
      of (
          decl_info
        * named_decl_info
        * qual_type
        * function_decl_info
        * cxx_method_decl_info
      )
  | MSPropertyDecl of (decl_info * named_decl_info * qual_type)
  | NonTypeTemplateParmDecl of (decl_info * named_decl_info * qual_type)
  | VarDecl of (decl_info * named_decl_info * qual_type * var_decl_info)
  | DecompositionDecl
      of (decl_info * named_decl_info * qual_type * var_decl_info)
  | ImplicitParamDecl
      of (decl_info * named_decl_info * qual_type * var_decl_info)
  | OMPCapturedExprDecl
      of (decl_info * named_decl_info * qual_type * var_decl_info)
  | ParmVarDecl of (decl_info * named_decl_info * qual_type * var_decl_info)
  | VarTemplateSpecializationDecl
      of (decl_info * named_decl_info * qual_type * var_decl_info)
  | VarTemplatePartialSpecializationDecl
      of (decl_info * named_decl_info * qual_type * var_decl_info)
  | EnumConstantDecl
      of (decl_info * named_decl_info * qual_type * enum_constant_decl_info)
  | IndirectFieldDecl
      of (decl_info * named_decl_info * qual_type * decl_ref list)
  | OMPDeclareReductionDecl of (decl_info * named_decl_info * qual_type)
  | UnresolvedUsingValueDecl of (decl_info * named_decl_info * qual_type)
  | OMPThreadPrivateDecl of (decl_info)
  | ObjCPropertyImplDecl of (decl_info * obj_c_property_impl_decl_info)
  | PragmaCommentDecl of (decl_info)
  | PragmaDetectMismatchDecl of (decl_info)
  | StaticAssertDecl of (decl_info)
  | TranslationUnitDecl
      of (
          decl_info
        * decl list
        * decl_context_info
        * translation_unit_decl_info
      )


and enum_constant_decl_info = Clang_ast_t.enum_constant_decl_info = {
  ecdi_init_expr (*atd init_expr *): stmt option
}

and field_decl_info = Clang_ast_t.field_decl_info = {
  fldi_is_mutable (*atd is_mutable *): bool;
  fldi_is_module_private (*atd is_module_private *): bool;
  fldi_init_expr (*atd init_expr *): stmt option;
  fldi_bit_width_expr (*atd bit_width_expr *): stmt option
}

and friend_info = Clang_ast_t.friend_info

and function_decl_info = Clang_ast_t.function_decl_info = {
  fdi_mangled_name (*atd mangled_name *): string option;
  fdi_storage_class (*atd storage_class *): string option;
  fdi_is_inline (*atd is_inline *): bool;
  fdi_is_module_private (*atd is_module_private *): bool;
  fdi_is_pure (*atd is_pure *): bool;
  fdi_is_delete_as_written (*atd is_delete_as_written *): bool;
  fdi_decls_in_prototype_scope (*atd decls_in_prototype_scope *): decl list;
  fdi_parameters (*atd parameters *): decl list;
  fdi_decl_ptr_with_body (*atd decl_ptr_with_body *): pointer option;
  fdi_body (*atd body *): stmt option
}

and lambda_expr_info = Clang_ast_t.lambda_expr_info = {
  lei_captures (*atd captures *): lambda_capture_info list;
  lei_lambda_decl (*atd lambda_decl *): decl
}

and obj_c_implementation_decl_info =
  Clang_ast_t.obj_c_implementation_decl_info = {
  oidi_super (*atd super *): decl_ref option;
  oidi_class_interface (*atd class_interface *): decl_ref option;
  oidi_ivar_initializers (*atd ivar_initializers *):
    cxx_ctor_initializer list
}

and obj_c_message_expr_kind = Clang_ast_t.obj_c_message_expr_kind

and obj_c_method_decl_info = Clang_ast_t.obj_c_method_decl_info = {
  omdi_is_instance_method (*atd is_instance_method *): bool;
  omdi_result_type (*atd result_type *): type_ptr;
  omdi_is_property_accessor (*atd is_property_accessor *): bool;
  omdi_property_decl (*atd property_decl *): decl_ref option;
  omdi_parameters (*atd parameters *): decl list;
  omdi_implicit_parameters (*atd implicit_parameters *): decl list;
  omdi_is_variadic (*atd is_variadic *): bool;
  omdi_body (*atd body *): stmt option
}

and opaque_value_expr_info = Clang_ast_t.opaque_value_expr_info = {
  ovei_source_expr (*atd source_expr *): stmt option
}

and stmt = Clang_ast_t.stmt = 
    GCCAsmStmt of (stmt_info * stmt list)
  | MSAsmStmt of (stmt_info * stmt list)
  | AttributedStmt of (stmt_info * stmt list * attribute list)
  | BreakStmt of (stmt_info * stmt list)
  | CXXCatchStmt of (stmt_info * stmt list * cxx_catch_stmt_info)
  | CXXForRangeStmt of (stmt_info * stmt list)
  | CXXTryStmt of (stmt_info * stmt list)
  | CapturedStmt of (stmt_info * stmt list)
  | CompoundStmt of (stmt_info * stmt list)
  | ContinueStmt of (stmt_info * stmt list)
  | CoreturnStmt of (stmt_info * stmt list)
  | CoroutineBodyStmt of (stmt_info * stmt list)
  | DeclStmt of (stmt_info * stmt list * decl list)
  | DoStmt of (stmt_info * stmt list)
  | BinaryConditionalOperator of (stmt_info * stmt list * expr_info)
  | ConditionalOperator of (stmt_info * stmt list * expr_info)
  | AddrLabelExpr
      of (stmt_info * stmt list * expr_info * addr_label_expr_info)
  | ArraySubscriptExpr of (stmt_info * stmt list * expr_info)
  | ArrayTypeTraitExpr of (stmt_info * stmt list * expr_info)
  | AsTypeExpr of (stmt_info * stmt list * expr_info)
  | AtomicExpr of (stmt_info * stmt list * expr_info)
  | BinaryOperator
      of (stmt_info * stmt list * expr_info * binary_operator_info)
  | CompoundAssignOperator
      of (
          stmt_info
        * stmt list
        * expr_info
        * binary_operator_info
        * compound_assign_operator_info
      )
  | BlockExpr of (stmt_info * stmt list * expr_info * decl)
  | CXXBindTemporaryExpr
      of (stmt_info * stmt list * expr_info * cxx_bind_temporary_expr_info)
  | CXXBoolLiteralExpr of (stmt_info * stmt list * expr_info * int)
  | CXXConstructExpr
      of (stmt_info * stmt list * expr_info * cxx_construct_expr_info)
  | CXXTemporaryObjectExpr
      of (stmt_info * stmt list * expr_info * cxx_construct_expr_info)
  | CXXDefaultArgExpr
      of (stmt_info * stmt list * expr_info * cxx_default_expr_info)
  | CXXDefaultInitExpr
      of (stmt_info * stmt list * expr_info * cxx_default_expr_info)
  | CXXDeleteExpr
      of (stmt_info * stmt list * expr_info * cxx_delete_expr_info)
  | CXXDependentScopeMemberExpr of (stmt_info * stmt list * expr_info)
  | CXXFoldExpr of (stmt_info * stmt list * expr_info)
  | CXXInheritedCtorInitExpr of (stmt_info * stmt list * expr_info)
  | CXXNewExpr of (stmt_info * stmt list * expr_info * cxx_new_expr_info)
  | CXXNoexceptExpr
      of (stmt_info * stmt list * expr_info * cxx_noexcept_expr_info)
  | CXXNullPtrLiteralExpr of (stmt_info * stmt list * expr_info)
  | CXXPseudoDestructorExpr of (stmt_info * stmt list * expr_info)
  | CXXScalarValueInitExpr of (stmt_info * stmt list * expr_info)
  | CXXStdInitializerListExpr of (stmt_info * stmt list * expr_info)
  | CXXThisExpr of (stmt_info * stmt list * expr_info)
  | CXXThrowExpr of (stmt_info * stmt list * expr_info)
  | CXXTypeidExpr of (stmt_info * stmt list * expr_info)
  | CXXUnresolvedConstructExpr of (stmt_info * stmt list * expr_info)
  | CXXUuidofExpr of (stmt_info * stmt list * expr_info)
  | CallExpr of (stmt_info * stmt list * expr_info)
  | CUDAKernelCallExpr of (stmt_info * stmt list * expr_info)
  | CXXMemberCallExpr of (stmt_info * stmt list * expr_info)
  | CXXOperatorCallExpr of (stmt_info * stmt list * expr_info)
  | UserDefinedLiteral of (stmt_info * stmt list * expr_info)
  | CStyleCastExpr
      of (stmt_info * stmt list * expr_info * cast_expr_info * type_ptr)
  | CXXFunctionalCastExpr
      of (stmt_info * stmt list * expr_info * cast_expr_info * type_ptr)
  | CXXConstCastExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * cast_expr_info
        * type_ptr
        * string
      )
  | CXXDynamicCastExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * cast_expr_info
        * type_ptr
        * string
      )
  | CXXReinterpretCastExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * cast_expr_info
        * type_ptr
        * string
      )
  | CXXStaticCastExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * cast_expr_info
        * type_ptr
        * string
      )
  | ObjCBridgedCastExpr
      of (stmt_info * stmt list * expr_info * cast_expr_info * type_ptr)
  | ImplicitCastExpr of (stmt_info * stmt list * expr_info * cast_expr_info)
  | CharacterLiteral of (stmt_info * stmt list * expr_info * int)
  | ChooseExpr of (stmt_info * stmt list * expr_info)
  | CompoundLiteralExpr of (stmt_info * stmt list * expr_info)
  | ConvertVectorExpr of (stmt_info * stmt list * expr_info)
  | CoawaitExpr of (stmt_info * stmt list * expr_info)
  | CoyieldExpr of (stmt_info * stmt list * expr_info)
  | DeclRefExpr of (stmt_info * stmt list * expr_info * decl_ref_expr_info)
  | DependentScopeDeclRefExpr of (stmt_info * stmt list * expr_info)
  | DesignatedInitExpr of (stmt_info * stmt list * expr_info)
  | DesignatedInitUpdateExpr of (stmt_info * stmt list * expr_info)
  | ExprWithCleanups
      of (stmt_info * stmt list * expr_info * expr_with_cleanups_info)
  | ExpressionTraitExpr of (stmt_info * stmt list * expr_info)
  | ExtVectorElementExpr of (stmt_info * stmt list * expr_info)
  | FloatingLiteral of (stmt_info * stmt list * expr_info * string)
  | FunctionParmPackExpr of (stmt_info * stmt list * expr_info)
  | GNUNullExpr of (stmt_info * stmt list * expr_info)
  | GenericSelectionExpr of (stmt_info * stmt list * expr_info)
  | ImaginaryLiteral of (stmt_info * stmt list * expr_info)
  | ImplicitValueInitExpr of (stmt_info * stmt list * expr_info)
  | InitListExpr of (stmt_info * stmt list * expr_info)
  | IntegerLiteral
      of (stmt_info * stmt list * expr_info * integer_literal_info)
  | LambdaExpr of (stmt_info * stmt list * expr_info * lambda_expr_info)
  | MSPropertyRefExpr of (stmt_info * stmt list * expr_info)
  | MSPropertySubscriptExpr of (stmt_info * stmt list * expr_info)
  | MaterializeTemporaryExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * materialize_temporary_expr_info
      )
  | MemberExpr of (stmt_info * stmt list * expr_info * member_expr_info)
  | NoInitExpr of (stmt_info * stmt list * expr_info)
  | OMPArraySectionExpr of (stmt_info * stmt list * expr_info)
  | ObjCArrayLiteral of (stmt_info * stmt list * expr_info)
  | ObjCAvailabilityCheckExpr of (stmt_info * stmt list * expr_info)
  | ObjCBoolLiteralExpr of (stmt_info * stmt list * expr_info * int)
  | ObjCBoxedExpr
      of (stmt_info * stmt list * expr_info * objc_boxed_expr_info)
  | ObjCDictionaryLiteral of (stmt_info * stmt list * expr_info)
  | ObjCEncodeExpr
      of (stmt_info * stmt list * expr_info * objc_encode_expr_info)
  | ObjCIndirectCopyRestoreExpr of (stmt_info * stmt list * expr_info)
  | ObjCIsaExpr of (stmt_info * stmt list * expr_info)
  | ObjCIvarRefExpr
      of (stmt_info * stmt list * expr_info * obj_c_ivar_ref_expr_info)
  | ObjCMessageExpr
      of (stmt_info * stmt list * expr_info * obj_c_message_expr_info)
  | ObjCPropertyRefExpr
      of (stmt_info * stmt list * expr_info * obj_c_property_ref_expr_info)
  | ObjCProtocolExpr of (stmt_info * stmt list * expr_info * decl_ref)
  | ObjCSelectorExpr of (stmt_info * stmt list * expr_info * selector)
  | ObjCStringLiteral of (stmt_info * stmt list * expr_info)
  | ObjCSubscriptRefExpr
      of (stmt_info * stmt list * expr_info * obj_c_subscript_ref_expr_info)
  | OffsetOfExpr of (stmt_info * stmt list * expr_info)
  | OpaqueValueExpr
      of (stmt_info * stmt list * expr_info * opaque_value_expr_info)
  | UnresolvedLookupExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * overload_expr_info
        * unresolved_lookup_expr_info
      )
  | UnresolvedMemberExpr
      of (stmt_info * stmt list * expr_info * overload_expr_info)
  | PackExpansionExpr of (stmt_info * stmt list * expr_info)
  | ParenExpr of (stmt_info * stmt list * expr_info)
  | ParenListExpr of (stmt_info * stmt list * expr_info)
  | PredefinedExpr
      of (stmt_info * stmt list * expr_info * predefined_expr_type)
  | PseudoObjectExpr of (stmt_info * stmt list * expr_info)
  | ShuffleVectorExpr of (stmt_info * stmt list * expr_info)
  | SizeOfPackExpr of (stmt_info * stmt list * expr_info)
  | StmtExpr of (stmt_info * stmt list * expr_info)
  | StringLiteral of (stmt_info * stmt list * expr_info * string)
  | SubstNonTypeTemplateParmExpr of (stmt_info * stmt list * expr_info)
  | SubstNonTypeTemplateParmPackExpr of (stmt_info * stmt list * expr_info)
  | TypeTraitExpr of (stmt_info * stmt list * expr_info * type_trait_info)
  | TypoExpr of (stmt_info * stmt list * expr_info)
  | UnaryExprOrTypeTraitExpr
      of (
          stmt_info
        * stmt list
        * expr_info
        * unary_expr_or_type_trait_expr_info
      )
  | UnaryOperator
      of (stmt_info * stmt list * expr_info * unary_operator_info)
  | VAArgExpr of (stmt_info * stmt list * expr_info)
  | ForStmt of (stmt_info * stmt list)
  | GotoStmt of (stmt_info * stmt list * goto_stmt_info)
  | IfStmt of (stmt_info * stmt list)
  | IndirectGotoStmt of (stmt_info * stmt list)
  | LabelStmt of (stmt_info * stmt list * string)
  | MSDependentExistsStmt of (stmt_info * stmt list)
  | NullStmt of (stmt_info * stmt list)
  | OMPAtomicDirective of (stmt_info * stmt list)
  | OMPBarrierDirective of (stmt_info * stmt list)
  | OMPCancelDirective of (stmt_info * stmt list)
  | OMPCancellationPointDirective of (stmt_info * stmt list)
  | OMPCriticalDirective of (stmt_info * stmt list)
  | OMPFlushDirective of (stmt_info * stmt list)
  | OMPDistributeDirective of (stmt_info * stmt list)
  | OMPDistributeParallelForDirective of (stmt_info * stmt list)
  | OMPDistributeParallelForSimdDirective of (stmt_info * stmt list)
  | OMPDistributeSimdDirective of (stmt_info * stmt list)
  | OMPForDirective of (stmt_info * stmt list)
  | OMPForSimdDirective of (stmt_info * stmt list)
  | OMPParallelForDirective of (stmt_info * stmt list)
  | OMPParallelForSimdDirective of (stmt_info * stmt list)
  | OMPSimdDirective of (stmt_info * stmt list)
  | OMPTargetParallelForSimdDirective of (stmt_info * stmt list)
  | OMPTargetSimdDirective of (stmt_info * stmt list)
  | OMPTaskLoopDirective of (stmt_info * stmt list)
  | OMPTaskLoopSimdDirective of (stmt_info * stmt list)
  | OMPMasterDirective of (stmt_info * stmt list)
  | OMPOrderedDirective of (stmt_info * stmt list)
  | OMPParallelDirective of (stmt_info * stmt list)
  | OMPParallelSectionsDirective of (stmt_info * stmt list)
  | OMPSectionDirective of (stmt_info * stmt list)
  | OMPSectionsDirective of (stmt_info * stmt list)
  | OMPSingleDirective of (stmt_info * stmt list)
  | OMPTargetDataDirective of (stmt_info * stmt list)
  | OMPTargetDirective of (stmt_info * stmt list)
  | OMPTargetEnterDataDirective of (stmt_info * stmt list)
  | OMPTargetExitDataDirective of (stmt_info * stmt list)
  | OMPTargetParallelDirective of (stmt_info * stmt list)
  | OMPTargetParallelForDirective of (stmt_info * stmt list)
  | OMPTargetUpdateDirective of (stmt_info * stmt list)
  | OMPTaskDirective of (stmt_info * stmt list)
  | OMPTaskgroupDirective of (stmt_info * stmt list)
  | OMPTaskwaitDirective of (stmt_info * stmt list)
  | OMPTaskyieldDirective of (stmt_info * stmt list)
  | OMPTeamsDirective of (stmt_info * stmt list)
  | ObjCAtCatchStmt of (stmt_info * stmt list * obj_c_message_expr_kind)
  | ObjCAtFinallyStmt of (stmt_info * stmt list)
  | ObjCAtSynchronizedStmt of (stmt_info * stmt list)
  | ObjCAtThrowStmt of (stmt_info * stmt list)
  | ObjCAtTryStmt of (stmt_info * stmt list)
  | ObjCAutoreleasePoolStmt of (stmt_info * stmt list)
  | ObjCForCollectionStmt of (stmt_info * stmt list)
  | ReturnStmt of (stmt_info * stmt list)
  | SEHExceptStmt of (stmt_info * stmt list)
  | SEHFinallyStmt of (stmt_info * stmt list)
  | SEHLeaveStmt of (stmt_info * stmt list)
  | SEHTryStmt of (stmt_info * stmt list)
  | CaseStmt of (stmt_info * stmt list)
  | DefaultStmt of (stmt_info * stmt list)
  | SwitchStmt of (stmt_info * stmt list)
  | WhileStmt of (stmt_info * stmt list)


and template_decl_info = Clang_ast_t.template_decl_info = {
  tdi_specializations (*atd specializations *): decl list
}

and var_decl_info = Clang_ast_t.var_decl_info = {
  vdi_storage_class (*atd storage_class *): string option;
  vdi_tls_kind (*atd tls_kind *): tls_kind;
  vdi_is_global (*atd is_global *): bool;
  vdi_is_static_local (*atd is_static_local *): bool;
  vdi_is_module_private (*atd is_module_private *): bool;
  vdi_is_nrvo_variable (*atd is_nrvo_variable *): bool;
  vdi_is_const_expr (*atd is_const_expr *): bool;
  vdi_init_expr (*atd init_expr *): stmt option;
  vdi_parm_index_in_function (*atd parm_index_in_function *): int option
}

type lookup = Clang_ast_t.lookup = {
  lup_decl_name (*atd decl_name *): string;
  lup_decl_refs (*atd decl_refs *): decl_ref list
}

type lookups = Clang_ast_t.lookups = {
  lups_decl_ref (*atd decl_ref *): decl_ref;
  lups_primary_context_pointer (*atd primary_context_pointer *):
    pointer option;
  lups_lookups (*atd lookups *): lookup list;
  lups_has_undeserialized_decls (*atd has_undeserialized_decls *): bool
}

type access_specifier = Clang_ast_t.access_specifier

val write_binary_operator_kind :
  Bi_outbuf.t -> binary_operator_kind -> unit
  (** Output a JSON value of type {!binary_operator_kind}. *)

val string_of_binary_operator_kind :
  ?len:int -> binary_operator_kind -> string
  (** Serialize a value of type {!binary_operator_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_binary_operator_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> binary_operator_kind
  (** Input JSON data of type {!binary_operator_kind}. *)

val binary_operator_kind_of_string :
  string -> binary_operator_kind
  (** Deserialize JSON data of type {!binary_operator_kind}. *)

val write_binary_operator_info :
  Bi_outbuf.t -> binary_operator_info -> unit
  (** Output a JSON value of type {!binary_operator_info}. *)

val string_of_binary_operator_info :
  ?len:int -> binary_operator_info -> string
  (** Serialize a value of type {!binary_operator_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_binary_operator_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> binary_operator_info
  (** Input JSON data of type {!binary_operator_info}. *)

val binary_operator_info_of_string :
  string -> binary_operator_info
  (** Deserialize JSON data of type {!binary_operator_info}. *)

val write_builtin_type_kind :
  Bi_outbuf.t -> builtin_type_kind -> unit
  (** Output a JSON value of type {!builtin_type_kind}. *)

val string_of_builtin_type_kind :
  ?len:int -> builtin_type_kind -> string
  (** Serialize a value of type {!builtin_type_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_builtin_type_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> builtin_type_kind
  (** Input JSON data of type {!builtin_type_kind}. *)

val builtin_type_kind_of_string :
  string -> builtin_type_kind
  (** Deserialize JSON data of type {!builtin_type_kind}. *)

val write_cast_kind :
  Bi_outbuf.t -> cast_kind -> unit
  (** Output a JSON value of type {!cast_kind}. *)

val string_of_cast_kind :
  ?len:int -> cast_kind -> string
  (** Serialize a value of type {!cast_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cast_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cast_kind
  (** Input JSON data of type {!cast_kind}. *)

val cast_kind_of_string :
  string -> cast_kind
  (** Deserialize JSON data of type {!cast_kind}. *)

val write_cxx_base_specifier :
  Bi_outbuf.t -> cxx_base_specifier -> unit
  (** Output a JSON value of type {!cxx_base_specifier}. *)

val string_of_cxx_base_specifier :
  ?len:int -> cxx_base_specifier -> string
  (** Serialize a value of type {!cxx_base_specifier}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_base_specifier :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_base_specifier
  (** Input JSON data of type {!cxx_base_specifier}. *)

val cxx_base_specifier_of_string :
  string -> cxx_base_specifier
  (** Deserialize JSON data of type {!cxx_base_specifier}. *)

val write_cast_expr_info :
  Bi_outbuf.t -> cast_expr_info -> unit
  (** Output a JSON value of type {!cast_expr_info}. *)

val string_of_cast_expr_info :
  ?len:int -> cast_expr_info -> string
  (** Serialize a value of type {!cast_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cast_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cast_expr_info
  (** Input JSON data of type {!cast_expr_info}. *)

val cast_expr_info_of_string :
  string -> cast_expr_info
  (** Deserialize JSON data of type {!cast_expr_info}. *)

val write_cxx_noexcept_expr_info :
  Bi_outbuf.t -> cxx_noexcept_expr_info -> unit
  (** Output a JSON value of type {!cxx_noexcept_expr_info}. *)

val string_of_cxx_noexcept_expr_info :
  ?len:int -> cxx_noexcept_expr_info -> string
  (** Serialize a value of type {!cxx_noexcept_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_noexcept_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_noexcept_expr_info
  (** Input JSON data of type {!cxx_noexcept_expr_info}. *)

val cxx_noexcept_expr_info_of_string :
  string -> cxx_noexcept_expr_info
  (** Deserialize JSON data of type {!cxx_noexcept_expr_info}. *)

val write_decl_context_info :
  Bi_outbuf.t -> decl_context_info -> unit
  (** Output a JSON value of type {!decl_context_info}. *)

val string_of_decl_context_info :
  ?len:int -> decl_context_info -> string
  (** Serialize a value of type {!decl_context_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decl_context_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decl_context_info
  (** Input JSON data of type {!decl_context_info}. *)

val decl_context_info_of_string :
  string -> decl_context_info
  (** Deserialize JSON data of type {!decl_context_info}. *)

val write_decl_kind :
  Bi_outbuf.t -> decl_kind -> unit
  (** Output a JSON value of type {!decl_kind}. *)

val string_of_decl_kind :
  ?len:int -> decl_kind -> string
  (** Serialize a value of type {!decl_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decl_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decl_kind
  (** Input JSON data of type {!decl_kind}. *)

val decl_kind_of_string :
  string -> decl_kind
  (** Deserialize JSON data of type {!decl_kind}. *)

val write_declaration_name_kind :
  Bi_outbuf.t -> declaration_name_kind -> unit
  (** Output a JSON value of type {!declaration_name_kind}. *)

val string_of_declaration_name_kind :
  ?len:int -> declaration_name_kind -> string
  (** Serialize a value of type {!declaration_name_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_declaration_name_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> declaration_name_kind
  (** Input JSON data of type {!declaration_name_kind}. *)

val declaration_name_kind_of_string :
  string -> declaration_name_kind
  (** Deserialize JSON data of type {!declaration_name_kind}. *)

val write_declaration_name :
  Bi_outbuf.t -> declaration_name -> unit
  (** Output a JSON value of type {!declaration_name}. *)

val string_of_declaration_name :
  ?len:int -> declaration_name -> string
  (** Serialize a value of type {!declaration_name}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_declaration_name :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> declaration_name
  (** Input JSON data of type {!declaration_name}. *)

val declaration_name_of_string :
  string -> declaration_name
  (** Deserialize JSON data of type {!declaration_name}. *)

val write_enum_decl_scope :
  Bi_outbuf.t -> enum_decl_scope -> unit
  (** Output a JSON value of type {!enum_decl_scope}. *)

val string_of_enum_decl_scope :
  ?len:int -> enum_decl_scope -> string
  (** Serialize a value of type {!enum_decl_scope}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_enum_decl_scope :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> enum_decl_scope
  (** Input JSON data of type {!enum_decl_scope}. *)

val enum_decl_scope_of_string :
  string -> enum_decl_scope
  (** Deserialize JSON data of type {!enum_decl_scope}. *)

val write_enum_decl_info :
  Bi_outbuf.t -> enum_decl_info -> unit
  (** Output a JSON value of type {!enum_decl_info}. *)

val string_of_enum_decl_info :
  ?len:int -> enum_decl_info -> string
  (** Serialize a value of type {!enum_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_enum_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> enum_decl_info
  (** Input JSON data of type {!enum_decl_info}. *)

val enum_decl_info_of_string :
  string -> enum_decl_info
  (** Deserialize JSON data of type {!enum_decl_info}. *)

val write_input_kind :
  Bi_outbuf.t -> input_kind -> unit
  (** Output a JSON value of type {!input_kind}. *)

val string_of_input_kind :
  ?len:int -> input_kind -> string
  (** Serialize a value of type {!input_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_input_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> input_kind
  (** Input JSON data of type {!input_kind}. *)

val input_kind_of_string :
  string -> input_kind
  (** Deserialize JSON data of type {!input_kind}. *)

val write_integer_literal_info :
  Bi_outbuf.t -> integer_literal_info -> unit
  (** Output a JSON value of type {!integer_literal_info}. *)

val string_of_integer_literal_info :
  ?len:int -> integer_literal_info -> string
  (** Serialize a value of type {!integer_literal_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_integer_literal_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> integer_literal_info
  (** Input JSON data of type {!integer_literal_info}. *)

val integer_literal_info_of_string :
  string -> integer_literal_info
  (** Deserialize JSON data of type {!integer_literal_info}. *)

val write_lambda_capture_kind :
  Bi_outbuf.t -> lambda_capture_kind -> unit
  (** Output a JSON value of type {!lambda_capture_kind}. *)

val string_of_lambda_capture_kind :
  ?len:int -> lambda_capture_kind -> string
  (** Serialize a value of type {!lambda_capture_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_lambda_capture_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> lambda_capture_kind
  (** Input JSON data of type {!lambda_capture_kind}. *)

val lambda_capture_kind_of_string :
  string -> lambda_capture_kind
  (** Deserialize JSON data of type {!lambda_capture_kind}. *)

val write_named_decl_info :
  Bi_outbuf.t -> named_decl_info -> unit
  (** Output a JSON value of type {!named_decl_info}. *)

val string_of_named_decl_info :
  ?len:int -> named_decl_info -> string
  (** Serialize a value of type {!named_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_named_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> named_decl_info
  (** Input JSON data of type {!named_decl_info}. *)

val named_decl_info_of_string :
  string -> named_decl_info
  (** Deserialize JSON data of type {!named_decl_info}. *)

val write_obj_c_access_control :
  Bi_outbuf.t -> obj_c_access_control -> unit
  (** Output a JSON value of type {!obj_c_access_control}. *)

val string_of_obj_c_access_control :
  ?len:int -> obj_c_access_control -> string
  (** Serialize a value of type {!obj_c_access_control}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_access_control :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_access_control
  (** Input JSON data of type {!obj_c_access_control}. *)

val obj_c_access_control_of_string :
  string -> obj_c_access_control
  (** Deserialize JSON data of type {!obj_c_access_control}. *)

val write_obj_c_ivar_decl_info :
  Bi_outbuf.t -> obj_c_ivar_decl_info -> unit
  (** Output a JSON value of type {!obj_c_ivar_decl_info}. *)

val string_of_obj_c_ivar_decl_info :
  ?len:int -> obj_c_ivar_decl_info -> string
  (** Serialize a value of type {!obj_c_ivar_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_ivar_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_ivar_decl_info
  (** Input JSON data of type {!obj_c_ivar_decl_info}. *)

val obj_c_ivar_decl_info_of_string :
  string -> obj_c_ivar_decl_info
  (** Deserialize JSON data of type {!obj_c_ivar_decl_info}. *)

val write_obj_c_property_control :
  Bi_outbuf.t -> obj_c_property_control -> unit
  (** Output a JSON value of type {!obj_c_property_control}. *)

val string_of_obj_c_property_control :
  ?len:int -> obj_c_property_control -> string
  (** Serialize a value of type {!obj_c_property_control}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_property_control :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_property_control
  (** Input JSON data of type {!obj_c_property_control}. *)

val obj_c_property_control_of_string :
  string -> obj_c_property_control
  (** Deserialize JSON data of type {!obj_c_property_control}. *)

val write_obj_c_subscript_kind :
  Bi_outbuf.t -> obj_c_subscript_kind -> unit
  (** Output a JSON value of type {!obj_c_subscript_kind}. *)

val string_of_obj_c_subscript_kind :
  ?len:int -> obj_c_subscript_kind -> string
  (** Serialize a value of type {!obj_c_subscript_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_subscript_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_subscript_kind
  (** Input JSON data of type {!obj_c_subscript_kind}. *)

val obj_c_subscript_kind_of_string :
  string -> obj_c_subscript_kind
  (** Deserialize JSON data of type {!obj_c_subscript_kind}. *)

val write_objc_lifetime_attr :
  Bi_outbuf.t -> objc_lifetime_attr -> unit
  (** Output a JSON value of type {!objc_lifetime_attr}. *)

val string_of_objc_lifetime_attr :
  ?len:int -> objc_lifetime_attr -> string
  (** Serialize a value of type {!objc_lifetime_attr}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_objc_lifetime_attr :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> objc_lifetime_attr
  (** Input JSON data of type {!objc_lifetime_attr}. *)

val objc_lifetime_attr_of_string :
  string -> objc_lifetime_attr
  (** Deserialize JSON data of type {!objc_lifetime_attr}. *)

val write_object_kind :
  Bi_outbuf.t -> object_kind -> unit
  (** Output a JSON value of type {!object_kind}. *)

val string_of_object_kind :
  ?len:int -> object_kind -> string
  (** Serialize a value of type {!object_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_object_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> object_kind
  (** Input JSON data of type {!object_kind}. *)

val object_kind_of_string :
  string -> object_kind
  (** Deserialize JSON data of type {!object_kind}. *)

val write_opt_type :
  Bi_outbuf.t -> opt_type -> unit
  (** Output a JSON value of type {!opt_type}. *)

val string_of_opt_type :
  ?len:int -> opt_type -> string
  (** Serialize a value of type {!opt_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_opt_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> opt_type
  (** Input JSON data of type {!opt_type}. *)

val opt_type_of_string :
  string -> opt_type
  (** Deserialize JSON data of type {!opt_type}. *)

val write_pointer :
  Bi_outbuf.t -> pointer -> unit
  (** Output a JSON value of type {!pointer}. *)

val string_of_pointer :
  ?len:int -> pointer -> string
  (** Serialize a value of type {!pointer}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_pointer :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> pointer
  (** Input JSON data of type {!pointer}. *)

val pointer_of_string :
  string -> pointer
  (** Deserialize JSON data of type {!pointer}. *)

val write_addr_label_expr_info :
  Bi_outbuf.t -> addr_label_expr_info -> unit
  (** Output a JSON value of type {!addr_label_expr_info}. *)

val string_of_addr_label_expr_info :
  ?len:int -> addr_label_expr_info -> string
  (** Serialize a value of type {!addr_label_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_addr_label_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> addr_label_expr_info
  (** Input JSON data of type {!addr_label_expr_info}. *)

val addr_label_expr_info_of_string :
  string -> addr_label_expr_info
  (** Deserialize JSON data of type {!addr_label_expr_info}. *)

val write_cxx_new_expr_info :
  Bi_outbuf.t -> cxx_new_expr_info -> unit
  (** Output a JSON value of type {!cxx_new_expr_info}. *)

val string_of_cxx_new_expr_info :
  ?len:int -> cxx_new_expr_info -> string
  (** Serialize a value of type {!cxx_new_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_new_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_new_expr_info
  (** Input JSON data of type {!cxx_new_expr_info}. *)

val cxx_new_expr_info_of_string :
  string -> cxx_new_expr_info
  (** Deserialize JSON data of type {!cxx_new_expr_info}. *)

val write_cxx_temporary :
  Bi_outbuf.t -> cxx_temporary -> unit
  (** Output a JSON value of type {!cxx_temporary}. *)

val string_of_cxx_temporary :
  ?len:int -> cxx_temporary -> string
  (** Serialize a value of type {!cxx_temporary}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_temporary :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_temporary
  (** Input JSON data of type {!cxx_temporary}. *)

val cxx_temporary_of_string :
  string -> cxx_temporary
  (** Deserialize JSON data of type {!cxx_temporary}. *)

val write_cxx_bind_temporary_expr_info :
  Bi_outbuf.t -> cxx_bind_temporary_expr_info -> unit
  (** Output a JSON value of type {!cxx_bind_temporary_expr_info}. *)

val string_of_cxx_bind_temporary_expr_info :
  ?len:int -> cxx_bind_temporary_expr_info -> string
  (** Serialize a value of type {!cxx_bind_temporary_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_bind_temporary_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_bind_temporary_expr_info
  (** Input JSON data of type {!cxx_bind_temporary_expr_info}. *)

val cxx_bind_temporary_expr_info_of_string :
  string -> cxx_bind_temporary_expr_info
  (** Deserialize JSON data of type {!cxx_bind_temporary_expr_info}. *)

val write_goto_stmt_info :
  Bi_outbuf.t -> goto_stmt_info -> unit
  (** Output a JSON value of type {!goto_stmt_info}. *)

val string_of_goto_stmt_info :
  ?len:int -> goto_stmt_info -> string
  (** Serialize a value of type {!goto_stmt_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_goto_stmt_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> goto_stmt_info
  (** Input JSON data of type {!goto_stmt_info}. *)

val goto_stmt_info_of_string :
  string -> goto_stmt_info
  (** Deserialize JSON data of type {!goto_stmt_info}. *)

val write_predefined_expr_type :
  Bi_outbuf.t -> predefined_expr_type -> unit
  (** Output a JSON value of type {!predefined_expr_type}. *)

val string_of_predefined_expr_type :
  ?len:int -> predefined_expr_type -> string
  (** Serialize a value of type {!predefined_expr_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_predefined_expr_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> predefined_expr_type
  (** Input JSON data of type {!predefined_expr_type}. *)

val predefined_expr_type_of_string :
  string -> predefined_expr_type
  (** Deserialize JSON data of type {!predefined_expr_type}. *)

val write_previous_decl :
  Bi_outbuf.t -> previous_decl -> unit
  (** Output a JSON value of type {!previous_decl}. *)

val string_of_previous_decl :
  ?len:int -> previous_decl -> string
  (** Serialize a value of type {!previous_decl}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_previous_decl :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> previous_decl
  (** Input JSON data of type {!previous_decl}. *)

val previous_decl_of_string :
  string -> previous_decl
  (** Deserialize JSON data of type {!previous_decl}. *)

val write_property_attribute :
  Bi_outbuf.t -> property_attribute -> unit
  (** Output a JSON value of type {!property_attribute}. *)

val string_of_property_attribute :
  ?len:int -> property_attribute -> string
  (** Serialize a value of type {!property_attribute}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_property_attribute :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> property_attribute
  (** Input JSON data of type {!property_attribute}. *)

val property_attribute_of_string :
  string -> property_attribute
  (** Deserialize JSON data of type {!property_attribute}. *)

val write_property_implementation :
  Bi_outbuf.t -> property_implementation -> unit
  (** Output a JSON value of type {!property_implementation}. *)

val string_of_property_implementation :
  ?len:int -> property_implementation -> string
  (** Serialize a value of type {!property_implementation}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_property_implementation :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> property_implementation
  (** Input JSON data of type {!property_implementation}. *)

val property_implementation_of_string :
  string -> property_implementation
  (** Deserialize JSON data of type {!property_implementation}. *)

val write_record_decl_info :
  Bi_outbuf.t -> record_decl_info -> unit
  (** Output a JSON value of type {!record_decl_info}. *)

val string_of_record_decl_info :
  ?len:int -> record_decl_info -> string
  (** Serialize a value of type {!record_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_record_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> record_decl_info
  (** Input JSON data of type {!record_decl_info}. *)

val record_decl_info_of_string :
  string -> record_decl_info
  (** Deserialize JSON data of type {!record_decl_info}. *)

val write_selector :
  Bi_outbuf.t -> selector -> unit
  (** Output a JSON value of type {!selector}. *)

val string_of_selector :
  ?len:int -> selector -> string
  (** Serialize a value of type {!selector}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_selector :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> selector
  (** Input JSON data of type {!selector}. *)

val selector_of_string :
  string -> selector
  (** Deserialize JSON data of type {!selector}. *)

val write_obj_c_method_ref_info :
  Bi_outbuf.t -> obj_c_method_ref_info -> unit
  (** Output a JSON value of type {!obj_c_method_ref_info}. *)

val string_of_obj_c_method_ref_info :
  ?len:int -> obj_c_method_ref_info -> string
  (** Serialize a value of type {!obj_c_method_ref_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_method_ref_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_method_ref_info
  (** Input JSON data of type {!obj_c_method_ref_info}. *)

val obj_c_method_ref_info_of_string :
  string -> obj_c_method_ref_info
  (** Deserialize JSON data of type {!obj_c_method_ref_info}. *)

val write_obj_c_subscript_ref_expr_info :
  Bi_outbuf.t -> obj_c_subscript_ref_expr_info -> unit
  (** Output a JSON value of type {!obj_c_subscript_ref_expr_info}. *)

val string_of_obj_c_subscript_ref_expr_info :
  ?len:int -> obj_c_subscript_ref_expr_info -> string
  (** Serialize a value of type {!obj_c_subscript_ref_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_subscript_ref_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_subscript_ref_expr_info
  (** Input JSON data of type {!obj_c_subscript_ref_expr_info}. *)

val obj_c_subscript_ref_expr_info_of_string :
  string -> obj_c_subscript_ref_expr_info
  (** Deserialize JSON data of type {!obj_c_subscript_ref_expr_info}. *)

val write_objc_boxed_expr_info :
  Bi_outbuf.t -> objc_boxed_expr_info -> unit
  (** Output a JSON value of type {!objc_boxed_expr_info}. *)

val string_of_objc_boxed_expr_info :
  ?len:int -> objc_boxed_expr_info -> string
  (** Serialize a value of type {!objc_boxed_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_objc_boxed_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> objc_boxed_expr_info
  (** Input JSON data of type {!objc_boxed_expr_info}. *)

val objc_boxed_expr_info_of_string :
  string -> objc_boxed_expr_info
  (** Deserialize JSON data of type {!objc_boxed_expr_info}. *)

val write_source_location :
  Bi_outbuf.t -> source_location -> unit
  (** Output a JSON value of type {!source_location}. *)

val string_of_source_location :
  ?len:int -> source_location -> string
  (** Serialize a value of type {!source_location}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_source_location :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> source_location
  (** Input JSON data of type {!source_location}. *)

val source_location_of_string :
  string -> source_location
  (** Deserialize JSON data of type {!source_location}. *)

val write_source_range :
  Bi_outbuf.t -> source_range -> unit
  (** Output a JSON value of type {!source_range}. *)

val string_of_source_range :
  ?len:int -> source_range -> string
  (** Serialize a value of type {!source_range}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_source_range :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> source_range
  (** Input JSON data of type {!source_range}. *)

val source_range_of_string :
  string -> source_range
  (** Deserialize JSON data of type {!source_range}. *)

val write_attribute_info :
  Bi_outbuf.t -> attribute_info -> unit
  (** Output a JSON value of type {!attribute_info}. *)

val string_of_attribute_info :
  ?len:int -> attribute_info -> string
  (** Serialize a value of type {!attribute_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_attribute_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> attribute_info
  (** Input JSON data of type {!attribute_info}. *)

val attribute_info_of_string :
  string -> attribute_info
  (** Deserialize JSON data of type {!attribute_info}. *)

val write_attribute :
  Bi_outbuf.t -> attribute -> unit
  (** Output a JSON value of type {!attribute}. *)

val string_of_attribute :
  ?len:int -> attribute -> string
  (** Serialize a value of type {!attribute}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_attribute :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> attribute
  (** Input JSON data of type {!attribute}. *)

val attribute_of_string :
  string -> attribute
  (** Deserialize JSON data of type {!attribute}. *)

val write_comment_info :
  Bi_outbuf.t -> comment_info -> unit
  (** Output a JSON value of type {!comment_info}. *)

val string_of_comment_info :
  ?len:int -> comment_info -> string
  (** Serialize a value of type {!comment_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_comment_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> comment_info
  (** Input JSON data of type {!comment_info}. *)

val comment_info_of_string :
  string -> comment_info
  (** Deserialize JSON data of type {!comment_info}. *)

val write_specifier_kind :
  Bi_outbuf.t -> specifier_kind -> unit
  (** Output a JSON value of type {!specifier_kind}. *)

val string_of_specifier_kind :
  ?len:int -> specifier_kind -> string
  (** Serialize a value of type {!specifier_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_specifier_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> specifier_kind
  (** Input JSON data of type {!specifier_kind}. *)

val specifier_kind_of_string :
  string -> specifier_kind
  (** Deserialize JSON data of type {!specifier_kind}. *)

val write_stmt_info :
  Bi_outbuf.t -> stmt_info -> unit
  (** Output a JSON value of type {!stmt_info}. *)

val string_of_stmt_info :
  ?len:int -> stmt_info -> string
  (** Serialize a value of type {!stmt_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_stmt_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> stmt_info
  (** Input JSON data of type {!stmt_info}. *)

val stmt_info_of_string :
  string -> stmt_info
  (** Deserialize JSON data of type {!stmt_info}. *)

val write_tls_kind :
  Bi_outbuf.t -> tls_kind -> unit
  (** Output a JSON value of type {!tls_kind}. *)

val string_of_tls_kind :
  ?len:int -> tls_kind -> string
  (** Serialize a value of type {!tls_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_tls_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> tls_kind
  (** Input JSON data of type {!tls_kind}. *)

val tls_kind_of_string :
  string -> tls_kind
  (** Deserialize JSON data of type {!tls_kind}. *)

val write_type_attribute_kind :
  Bi_outbuf.t -> type_attribute_kind -> unit
  (** Output a JSON value of type {!type_attribute_kind}. *)

val string_of_type_attribute_kind :
  ?len:int -> type_attribute_kind -> string
  (** Serialize a value of type {!type_attribute_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_type_attribute_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> type_attribute_kind
  (** Input JSON data of type {!type_attribute_kind}. *)

val type_attribute_kind_of_string :
  string -> type_attribute_kind
  (** Deserialize JSON data of type {!type_attribute_kind}. *)

val write_attr_type_info :
  Bi_outbuf.t -> attr_type_info -> unit
  (** Output a JSON value of type {!attr_type_info}. *)

val string_of_attr_type_info :
  ?len:int -> attr_type_info -> string
  (** Serialize a value of type {!attr_type_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_attr_type_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> attr_type_info
  (** Input JSON data of type {!attr_type_info}. *)

val attr_type_info_of_string :
  string -> attr_type_info
  (** Deserialize JSON data of type {!attr_type_info}. *)

val write_type_ptr :
  Bi_outbuf.t -> type_ptr -> unit
  (** Output a JSON value of type {!type_ptr}. *)

val string_of_type_ptr :
  ?len:int -> type_ptr -> string
  (** Serialize a value of type {!type_ptr}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_type_ptr :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> type_ptr
  (** Input JSON data of type {!type_ptr}. *)

val type_ptr_of_string :
  string -> type_ptr
  (** Deserialize JSON data of type {!type_ptr}. *)

val write_compound_assign_operator_info :
  Bi_outbuf.t -> compound_assign_operator_info -> unit
  (** Output a JSON value of type {!compound_assign_operator_info}. *)

val string_of_compound_assign_operator_info :
  ?len:int -> compound_assign_operator_info -> string
  (** Serialize a value of type {!compound_assign_operator_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_compound_assign_operator_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> compound_assign_operator_info
  (** Input JSON data of type {!compound_assign_operator_info}. *)

val compound_assign_operator_info_of_string :
  string -> compound_assign_operator_info
  (** Deserialize JSON data of type {!compound_assign_operator_info}. *)

val write_cxx_delete_expr_info :
  Bi_outbuf.t -> cxx_delete_expr_info -> unit
  (** Output a JSON value of type {!cxx_delete_expr_info}. *)

val string_of_cxx_delete_expr_info :
  ?len:int -> cxx_delete_expr_info -> string
  (** Serialize a value of type {!cxx_delete_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_delete_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_delete_expr_info
  (** Input JSON data of type {!cxx_delete_expr_info}. *)

val cxx_delete_expr_info_of_string :
  string -> cxx_delete_expr_info
  (** Deserialize JSON data of type {!cxx_delete_expr_info}. *)

val write_decl_ref :
  Bi_outbuf.t -> decl_ref -> unit
  (** Output a JSON value of type {!decl_ref}. *)

val string_of_decl_ref :
  ?len:int -> decl_ref -> string
  (** Serialize a value of type {!decl_ref}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decl_ref :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decl_ref
  (** Input JSON data of type {!decl_ref}. *)

val decl_ref_of_string :
  string -> decl_ref
  (** Deserialize JSON data of type {!decl_ref}. *)

val write_cxx_construct_expr_info :
  Bi_outbuf.t -> cxx_construct_expr_info -> unit
  (** Output a JSON value of type {!cxx_construct_expr_info}. *)

val string_of_cxx_construct_expr_info :
  ?len:int -> cxx_construct_expr_info -> string
  (** Serialize a value of type {!cxx_construct_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_construct_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_construct_expr_info
  (** Input JSON data of type {!cxx_construct_expr_info}. *)

val cxx_construct_expr_info_of_string :
  string -> cxx_construct_expr_info
  (** Deserialize JSON data of type {!cxx_construct_expr_info}. *)

val write_cxx_ctor_initializer_subject :
  Bi_outbuf.t -> cxx_ctor_initializer_subject -> unit
  (** Output a JSON value of type {!cxx_ctor_initializer_subject}. *)

val string_of_cxx_ctor_initializer_subject :
  ?len:int -> cxx_ctor_initializer_subject -> string
  (** Serialize a value of type {!cxx_ctor_initializer_subject}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_ctor_initializer_subject :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_ctor_initializer_subject
  (** Input JSON data of type {!cxx_ctor_initializer_subject}. *)

val cxx_ctor_initializer_subject_of_string :
  string -> cxx_ctor_initializer_subject
  (** Deserialize JSON data of type {!cxx_ctor_initializer_subject}. *)

val write_cxx_record_decl_info :
  Bi_outbuf.t -> cxx_record_decl_info -> unit
  (** Output a JSON value of type {!cxx_record_decl_info}. *)

val string_of_cxx_record_decl_info :
  ?len:int -> cxx_record_decl_info -> string
  (** Serialize a value of type {!cxx_record_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_record_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_record_decl_info
  (** Input JSON data of type {!cxx_record_decl_info}. *)

val cxx_record_decl_info_of_string :
  string -> cxx_record_decl_info
  (** Deserialize JSON data of type {!cxx_record_decl_info}. *)

val write_decl_ref_expr_info :
  Bi_outbuf.t -> decl_ref_expr_info -> unit
  (** Output a JSON value of type {!decl_ref_expr_info}. *)

val string_of_decl_ref_expr_info :
  ?len:int -> decl_ref_expr_info -> string
  (** Serialize a value of type {!decl_ref_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decl_ref_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decl_ref_expr_info
  (** Input JSON data of type {!decl_ref_expr_info}. *)

val decl_ref_expr_info_of_string :
  string -> decl_ref_expr_info
  (** Deserialize JSON data of type {!decl_ref_expr_info}. *)

val write_expr_with_cleanups_info :
  Bi_outbuf.t -> expr_with_cleanups_info -> unit
  (** Output a JSON value of type {!expr_with_cleanups_info}. *)

val string_of_expr_with_cleanups_info :
  ?len:int -> expr_with_cleanups_info -> string
  (** Serialize a value of type {!expr_with_cleanups_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_expr_with_cleanups_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> expr_with_cleanups_info
  (** Input JSON data of type {!expr_with_cleanups_info}. *)

val expr_with_cleanups_info_of_string :
  string -> expr_with_cleanups_info
  (** Deserialize JSON data of type {!expr_with_cleanups_info}. *)

val write_function_type_info :
  Bi_outbuf.t -> function_type_info -> unit
  (** Output a JSON value of type {!function_type_info}. *)

val string_of_function_type_info :
  ?len:int -> function_type_info -> string
  (** Serialize a value of type {!function_type_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_function_type_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> function_type_info
  (** Input JSON data of type {!function_type_info}. *)

val function_type_info_of_string :
  string -> function_type_info
  (** Deserialize JSON data of type {!function_type_info}. *)

val write_lambda_capture_info :
  Bi_outbuf.t -> lambda_capture_info -> unit
  (** Output a JSON value of type {!lambda_capture_info}. *)

val string_of_lambda_capture_info :
  ?len:int -> lambda_capture_info -> string
  (** Serialize a value of type {!lambda_capture_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_lambda_capture_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> lambda_capture_info
  (** Input JSON data of type {!lambda_capture_info}. *)

val lambda_capture_info_of_string :
  string -> lambda_capture_info
  (** Deserialize JSON data of type {!lambda_capture_info}. *)

val write_materialize_temporary_expr_info :
  Bi_outbuf.t -> materialize_temporary_expr_info -> unit
  (** Output a JSON value of type {!materialize_temporary_expr_info}. *)

val string_of_materialize_temporary_expr_info :
  ?len:int -> materialize_temporary_expr_info -> string
  (** Serialize a value of type {!materialize_temporary_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_materialize_temporary_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> materialize_temporary_expr_info
  (** Input JSON data of type {!materialize_temporary_expr_info}. *)

val materialize_temporary_expr_info_of_string :
  string -> materialize_temporary_expr_info
  (** Deserialize JSON data of type {!materialize_temporary_expr_info}. *)

val write_member_expr_info :
  Bi_outbuf.t -> member_expr_info -> unit
  (** Output a JSON value of type {!member_expr_info}. *)

val string_of_member_expr_info :
  ?len:int -> member_expr_info -> string
  (** Serialize a value of type {!member_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_member_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> member_expr_info
  (** Input JSON data of type {!member_expr_info}. *)

val member_expr_info_of_string :
  string -> member_expr_info
  (** Deserialize JSON data of type {!member_expr_info}. *)

val write_namespace_decl_info :
  Bi_outbuf.t -> namespace_decl_info -> unit
  (** Output a JSON value of type {!namespace_decl_info}. *)

val string_of_namespace_decl_info :
  ?len:int -> namespace_decl_info -> string
  (** Serialize a value of type {!namespace_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_namespace_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> namespace_decl_info
  (** Input JSON data of type {!namespace_decl_info}. *)

val namespace_decl_info_of_string :
  string -> namespace_decl_info
  (** Deserialize JSON data of type {!namespace_decl_info}. *)

val write_nested_name_specifier_loc :
  Bi_outbuf.t -> nested_name_specifier_loc -> unit
  (** Output a JSON value of type {!nested_name_specifier_loc}. *)

val string_of_nested_name_specifier_loc :
  ?len:int -> nested_name_specifier_loc -> string
  (** Serialize a value of type {!nested_name_specifier_loc}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_nested_name_specifier_loc :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> nested_name_specifier_loc
  (** Input JSON data of type {!nested_name_specifier_loc}. *)

val nested_name_specifier_loc_of_string :
  string -> nested_name_specifier_loc
  (** Deserialize JSON data of type {!nested_name_specifier_loc}. *)

val write_namespace_alias_decl_info :
  Bi_outbuf.t -> namespace_alias_decl_info -> unit
  (** Output a JSON value of type {!namespace_alias_decl_info}. *)

val string_of_namespace_alias_decl_info :
  ?len:int -> namespace_alias_decl_info -> string
  (** Serialize a value of type {!namespace_alias_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_namespace_alias_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> namespace_alias_decl_info
  (** Input JSON data of type {!namespace_alias_decl_info}. *)

val namespace_alias_decl_info_of_string :
  string -> namespace_alias_decl_info
  (** Deserialize JSON data of type {!namespace_alias_decl_info}. *)

val write_obj_c_category_decl_info :
  Bi_outbuf.t -> obj_c_category_decl_info -> unit
  (** Output a JSON value of type {!obj_c_category_decl_info}. *)

val string_of_obj_c_category_decl_info :
  ?len:int -> obj_c_category_decl_info -> string
  (** Serialize a value of type {!obj_c_category_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_category_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_category_decl_info
  (** Input JSON data of type {!obj_c_category_decl_info}. *)

val obj_c_category_decl_info_of_string :
  string -> obj_c_category_decl_info
  (** Deserialize JSON data of type {!obj_c_category_decl_info}. *)

val write_obj_c_category_impl_decl_info :
  Bi_outbuf.t -> obj_c_category_impl_decl_info -> unit
  (** Output a JSON value of type {!obj_c_category_impl_decl_info}. *)

val string_of_obj_c_category_impl_decl_info :
  ?len:int -> obj_c_category_impl_decl_info -> string
  (** Serialize a value of type {!obj_c_category_impl_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_category_impl_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_category_impl_decl_info
  (** Input JSON data of type {!obj_c_category_impl_decl_info}. *)

val obj_c_category_impl_decl_info_of_string :
  string -> obj_c_category_impl_decl_info
  (** Deserialize JSON data of type {!obj_c_category_impl_decl_info}. *)

val write_obj_c_compatible_alias_decl_info :
  Bi_outbuf.t -> obj_c_compatible_alias_decl_info -> unit
  (** Output a JSON value of type {!obj_c_compatible_alias_decl_info}. *)

val string_of_obj_c_compatible_alias_decl_info :
  ?len:int -> obj_c_compatible_alias_decl_info -> string
  (** Serialize a value of type {!obj_c_compatible_alias_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_compatible_alias_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_compatible_alias_decl_info
  (** Input JSON data of type {!obj_c_compatible_alias_decl_info}. *)

val obj_c_compatible_alias_decl_info_of_string :
  string -> obj_c_compatible_alias_decl_info
  (** Deserialize JSON data of type {!obj_c_compatible_alias_decl_info}. *)

val write_obj_c_interface_decl_info :
  Bi_outbuf.t -> obj_c_interface_decl_info -> unit
  (** Output a JSON value of type {!obj_c_interface_decl_info}. *)

val string_of_obj_c_interface_decl_info :
  ?len:int -> obj_c_interface_decl_info -> string
  (** Serialize a value of type {!obj_c_interface_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_interface_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_interface_decl_info
  (** Input JSON data of type {!obj_c_interface_decl_info}. *)

val obj_c_interface_decl_info_of_string :
  string -> obj_c_interface_decl_info
  (** Deserialize JSON data of type {!obj_c_interface_decl_info}. *)

val write_obj_c_ivar_ref_expr_info :
  Bi_outbuf.t -> obj_c_ivar_ref_expr_info -> unit
  (** Output a JSON value of type {!obj_c_ivar_ref_expr_info}. *)

val string_of_obj_c_ivar_ref_expr_info :
  ?len:int -> obj_c_ivar_ref_expr_info -> string
  (** Serialize a value of type {!obj_c_ivar_ref_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_ivar_ref_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_ivar_ref_expr_info
  (** Input JSON data of type {!obj_c_ivar_ref_expr_info}. *)

val obj_c_ivar_ref_expr_info_of_string :
  string -> obj_c_ivar_ref_expr_info
  (** Deserialize JSON data of type {!obj_c_ivar_ref_expr_info}. *)

val write_obj_c_property_decl_info :
  Bi_outbuf.t -> obj_c_property_decl_info -> unit
  (** Output a JSON value of type {!obj_c_property_decl_info}. *)

val string_of_obj_c_property_decl_info :
  ?len:int -> obj_c_property_decl_info -> string
  (** Serialize a value of type {!obj_c_property_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_property_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_property_decl_info
  (** Input JSON data of type {!obj_c_property_decl_info}. *)

val obj_c_property_decl_info_of_string :
  string -> obj_c_property_decl_info
  (** Deserialize JSON data of type {!obj_c_property_decl_info}. *)

val write_obj_c_property_impl_decl_info :
  Bi_outbuf.t -> obj_c_property_impl_decl_info -> unit
  (** Output a JSON value of type {!obj_c_property_impl_decl_info}. *)

val string_of_obj_c_property_impl_decl_info :
  ?len:int -> obj_c_property_impl_decl_info -> string
  (** Serialize a value of type {!obj_c_property_impl_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_property_impl_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_property_impl_decl_info
  (** Input JSON data of type {!obj_c_property_impl_decl_info}. *)

val obj_c_property_impl_decl_info_of_string :
  string -> obj_c_property_impl_decl_info
  (** Deserialize JSON data of type {!obj_c_property_impl_decl_info}. *)

val write_obj_c_protocol_decl_info :
  Bi_outbuf.t -> obj_c_protocol_decl_info -> unit
  (** Output a JSON value of type {!obj_c_protocol_decl_info}. *)

val string_of_obj_c_protocol_decl_info :
  ?len:int -> obj_c_protocol_decl_info -> string
  (** Serialize a value of type {!obj_c_protocol_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_protocol_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_protocol_decl_info
  (** Input JSON data of type {!obj_c_protocol_decl_info}. *)

val obj_c_protocol_decl_info_of_string :
  string -> obj_c_protocol_decl_info
  (** Deserialize JSON data of type {!obj_c_protocol_decl_info}. *)

val write_objc_encode_expr_info :
  Bi_outbuf.t -> objc_encode_expr_info -> unit
  (** Output a JSON value of type {!objc_encode_expr_info}. *)

val string_of_objc_encode_expr_info :
  ?len:int -> objc_encode_expr_info -> string
  (** Serialize a value of type {!objc_encode_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_objc_encode_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> objc_encode_expr_info
  (** Input JSON data of type {!objc_encode_expr_info}. *)

val objc_encode_expr_info_of_string :
  string -> objc_encode_expr_info
  (** Deserialize JSON data of type {!objc_encode_expr_info}. *)

val write_objc_object_type_info :
  Bi_outbuf.t -> objc_object_type_info -> unit
  (** Output a JSON value of type {!objc_object_type_info}. *)

val string_of_objc_object_type_info :
  ?len:int -> objc_object_type_info -> string
  (** Serialize a value of type {!objc_object_type_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_objc_object_type_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> objc_object_type_info
  (** Input JSON data of type {!objc_object_type_info}. *)

val objc_object_type_info_of_string :
  string -> objc_object_type_info
  (** Deserialize JSON data of type {!objc_object_type_info}. *)

val write_overload_expr_info :
  Bi_outbuf.t -> overload_expr_info -> unit
  (** Output a JSON value of type {!overload_expr_info}. *)

val string_of_overload_expr_info :
  ?len:int -> overload_expr_info -> string
  (** Serialize a value of type {!overload_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_overload_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> overload_expr_info
  (** Input JSON data of type {!overload_expr_info}. *)

val overload_expr_info_of_string :
  string -> overload_expr_info
  (** Deserialize JSON data of type {!overload_expr_info}. *)

val write_params_type_info :
  Bi_outbuf.t -> params_type_info -> unit
  (** Output a JSON value of type {!params_type_info}. *)

val string_of_params_type_info :
  ?len:int -> params_type_info -> string
  (** Serialize a value of type {!params_type_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_params_type_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> params_type_info
  (** Input JSON data of type {!params_type_info}. *)

val params_type_info_of_string :
  string -> params_type_info
  (** Deserialize JSON data of type {!params_type_info}. *)

val write_property_ref_kind :
  Bi_outbuf.t -> property_ref_kind -> unit
  (** Output a JSON value of type {!property_ref_kind}. *)

val string_of_property_ref_kind :
  ?len:int -> property_ref_kind -> string
  (** Serialize a value of type {!property_ref_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_property_ref_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> property_ref_kind
  (** Input JSON data of type {!property_ref_kind}. *)

val property_ref_kind_of_string :
  string -> property_ref_kind
  (** Deserialize JSON data of type {!property_ref_kind}. *)

val write_obj_c_property_ref_expr_info :
  Bi_outbuf.t -> obj_c_property_ref_expr_info -> unit
  (** Output a JSON value of type {!obj_c_property_ref_expr_info}. *)

val string_of_obj_c_property_ref_expr_info :
  ?len:int -> obj_c_property_ref_expr_info -> string
  (** Serialize a value of type {!obj_c_property_ref_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_property_ref_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_property_ref_expr_info
  (** Input JSON data of type {!obj_c_property_ref_expr_info}. *)

val obj_c_property_ref_expr_info_of_string :
  string -> obj_c_property_ref_expr_info
  (** Deserialize JSON data of type {!obj_c_property_ref_expr_info}. *)

val write_qual_type :
  Bi_outbuf.t -> qual_type -> unit
  (** Output a JSON value of type {!qual_type}. *)

val string_of_qual_type :
  ?len:int -> qual_type -> string
  (** Serialize a value of type {!qual_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_qual_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> qual_type
  (** Input JSON data of type {!qual_type}. *)

val qual_type_of_string :
  string -> qual_type
  (** Deserialize JSON data of type {!qual_type}. *)

val write_receiver_kind :
  Bi_outbuf.t -> receiver_kind -> unit
  (** Output a JSON value of type {!receiver_kind}. *)

val string_of_receiver_kind :
  ?len:int -> receiver_kind -> string
  (** Serialize a value of type {!receiver_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_receiver_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> receiver_kind
  (** Input JSON data of type {!receiver_kind}. *)

val receiver_kind_of_string :
  string -> receiver_kind
  (** Deserialize JSON data of type {!receiver_kind}. *)

val write_obj_c_message_expr_info :
  Bi_outbuf.t -> obj_c_message_expr_info -> unit
  (** Output a JSON value of type {!obj_c_message_expr_info}. *)

val string_of_obj_c_message_expr_info :
  ?len:int -> obj_c_message_expr_info -> string
  (** Serialize a value of type {!obj_c_message_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_message_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_message_expr_info
  (** Input JSON data of type {!obj_c_message_expr_info}. *)

val obj_c_message_expr_info_of_string :
  string -> obj_c_message_expr_info
  (** Deserialize JSON data of type {!obj_c_message_expr_info}. *)

val write_template_instantiation_arg_info :
  Bi_outbuf.t -> template_instantiation_arg_info -> unit
  (** Output a JSON value of type {!template_instantiation_arg_info}. *)

val string_of_template_instantiation_arg_info :
  ?len:int -> template_instantiation_arg_info -> string
  (** Serialize a value of type {!template_instantiation_arg_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_template_instantiation_arg_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> template_instantiation_arg_info
  (** Input JSON data of type {!template_instantiation_arg_info}. *)

val template_instantiation_arg_info_of_string :
  string -> template_instantiation_arg_info
  (** Deserialize JSON data of type {!template_instantiation_arg_info}. *)

val write_type_info :
  Bi_outbuf.t -> type_info -> unit
  (** Output a JSON value of type {!type_info}. *)

val string_of_type_info :
  ?len:int -> type_info -> string
  (** Serialize a value of type {!type_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_type_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> type_info
  (** Input JSON data of type {!type_info}. *)

val type_info_of_string :
  string -> type_info
  (** Deserialize JSON data of type {!type_info}. *)

val write_type_trait_info :
  Bi_outbuf.t -> type_trait_info -> unit
  (** Output a JSON value of type {!type_trait_info}. *)

val string_of_type_trait_info :
  ?len:int -> type_trait_info -> string
  (** Serialize a value of type {!type_trait_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_type_trait_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> type_trait_info
  (** Input JSON data of type {!type_trait_info}. *)

val type_trait_info_of_string :
  string -> type_trait_info
  (** Deserialize JSON data of type {!type_trait_info}. *)

val write_typedef_decl_info :
  Bi_outbuf.t -> typedef_decl_info -> unit
  (** Output a JSON value of type {!typedef_decl_info}. *)

val string_of_typedef_decl_info :
  ?len:int -> typedef_decl_info -> string
  (** Serialize a value of type {!typedef_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_typedef_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> typedef_decl_info
  (** Input JSON data of type {!typedef_decl_info}. *)

val typedef_decl_info_of_string :
  string -> typedef_decl_info
  (** Deserialize JSON data of type {!typedef_decl_info}. *)

val write_typedef_type_info :
  Bi_outbuf.t -> typedef_type_info -> unit
  (** Output a JSON value of type {!typedef_type_info}. *)

val string_of_typedef_type_info :
  ?len:int -> typedef_type_info -> string
  (** Serialize a value of type {!typedef_type_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_typedef_type_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> typedef_type_info
  (** Input JSON data of type {!typedef_type_info}. *)

val typedef_type_info_of_string :
  string -> typedef_type_info
  (** Deserialize JSON data of type {!typedef_type_info}. *)

val write_c_type :
  Bi_outbuf.t -> c_type -> unit
  (** Output a JSON value of type {!c_type}. *)

val string_of_c_type :
  ?len:int -> c_type -> string
  (** Serialize a value of type {!c_type}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_c_type :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> c_type
  (** Input JSON data of type {!c_type}. *)

val c_type_of_string :
  string -> c_type
  (** Deserialize JSON data of type {!c_type}. *)

val write_translation_unit_decl_info :
  Bi_outbuf.t -> translation_unit_decl_info -> unit
  (** Output a JSON value of type {!translation_unit_decl_info}. *)

val string_of_translation_unit_decl_info :
  ?len:int -> translation_unit_decl_info -> string
  (** Serialize a value of type {!translation_unit_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_translation_unit_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> translation_unit_decl_info
  (** Input JSON data of type {!translation_unit_decl_info}. *)

val translation_unit_decl_info_of_string :
  string -> translation_unit_decl_info
  (** Deserialize JSON data of type {!translation_unit_decl_info}. *)

val write_unary_expr_or_type_trait_kind :
  Bi_outbuf.t -> unary_expr_or_type_trait_kind -> unit
  (** Output a JSON value of type {!unary_expr_or_type_trait_kind}. *)

val string_of_unary_expr_or_type_trait_kind :
  ?len:int -> unary_expr_or_type_trait_kind -> string
  (** Serialize a value of type {!unary_expr_or_type_trait_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_unary_expr_or_type_trait_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> unary_expr_or_type_trait_kind
  (** Input JSON data of type {!unary_expr_or_type_trait_kind}. *)

val unary_expr_or_type_trait_kind_of_string :
  string -> unary_expr_or_type_trait_kind
  (** Deserialize JSON data of type {!unary_expr_or_type_trait_kind}. *)

val write_unary_expr_or_type_trait_expr_info :
  Bi_outbuf.t -> unary_expr_or_type_trait_expr_info -> unit
  (** Output a JSON value of type {!unary_expr_or_type_trait_expr_info}. *)

val string_of_unary_expr_or_type_trait_expr_info :
  ?len:int -> unary_expr_or_type_trait_expr_info -> string
  (** Serialize a value of type {!unary_expr_or_type_trait_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_unary_expr_or_type_trait_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> unary_expr_or_type_trait_expr_info
  (** Input JSON data of type {!unary_expr_or_type_trait_expr_info}. *)

val unary_expr_or_type_trait_expr_info_of_string :
  string -> unary_expr_or_type_trait_expr_info
  (** Deserialize JSON data of type {!unary_expr_or_type_trait_expr_info}. *)

val write_unary_operator_kind :
  Bi_outbuf.t -> unary_operator_kind -> unit
  (** Output a JSON value of type {!unary_operator_kind}. *)

val string_of_unary_operator_kind :
  ?len:int -> unary_operator_kind -> string
  (** Serialize a value of type {!unary_operator_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_unary_operator_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> unary_operator_kind
  (** Input JSON data of type {!unary_operator_kind}. *)

val unary_operator_kind_of_string :
  string -> unary_operator_kind
  (** Deserialize JSON data of type {!unary_operator_kind}. *)

val write_unary_operator_info :
  Bi_outbuf.t -> unary_operator_info -> unit
  (** Output a JSON value of type {!unary_operator_info}. *)

val string_of_unary_operator_info :
  ?len:int -> unary_operator_info -> string
  (** Serialize a value of type {!unary_operator_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_unary_operator_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> unary_operator_info
  (** Input JSON data of type {!unary_operator_info}. *)

val unary_operator_info_of_string :
  string -> unary_operator_info
  (** Deserialize JSON data of type {!unary_operator_info}. *)

val write_unresolved_lookup_expr_info :
  Bi_outbuf.t -> unresolved_lookup_expr_info -> unit
  (** Output a JSON value of type {!unresolved_lookup_expr_info}. *)

val string_of_unresolved_lookup_expr_info :
  ?len:int -> unresolved_lookup_expr_info -> string
  (** Serialize a value of type {!unresolved_lookup_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_unresolved_lookup_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> unresolved_lookup_expr_info
  (** Input JSON data of type {!unresolved_lookup_expr_info}. *)

val unresolved_lookup_expr_info_of_string :
  string -> unresolved_lookup_expr_info
  (** Deserialize JSON data of type {!unresolved_lookup_expr_info}. *)

val write_using_directive_decl_info :
  Bi_outbuf.t -> using_directive_decl_info -> unit
  (** Output a JSON value of type {!using_directive_decl_info}. *)

val string_of_using_directive_decl_info :
  ?len:int -> using_directive_decl_info -> string
  (** Serialize a value of type {!using_directive_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_using_directive_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> using_directive_decl_info
  (** Input JSON data of type {!using_directive_decl_info}. *)

val using_directive_decl_info_of_string :
  string -> using_directive_decl_info
  (** Deserialize JSON data of type {!using_directive_decl_info}. *)

val write_value_kind :
  Bi_outbuf.t -> value_kind -> unit
  (** Output a JSON value of type {!value_kind}. *)

val string_of_value_kind :
  ?len:int -> value_kind -> string
  (** Serialize a value of type {!value_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_value_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> value_kind
  (** Input JSON data of type {!value_kind}. *)

val value_kind_of_string :
  string -> value_kind
  (** Deserialize JSON data of type {!value_kind}. *)

val write_expr_info :
  Bi_outbuf.t -> expr_info -> unit
  (** Output a JSON value of type {!expr_info}. *)

val string_of_expr_info :
  ?len:int -> expr_info -> string
  (** Serialize a value of type {!expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> expr_info
  (** Input JSON data of type {!expr_info}. *)

val expr_info_of_string :
  string -> expr_info
  (** Deserialize JSON data of type {!expr_info}. *)

val write_comment :
  Bi_outbuf.t -> comment -> unit
  (** Output a JSON value of type {!comment}. *)

val string_of_comment :
  ?len:int -> comment -> string
  (** Serialize a value of type {!comment}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_comment :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> comment
  (** Input JSON data of type {!comment}. *)

val comment_of_string :
  string -> comment
  (** Deserialize JSON data of type {!comment}. *)

val write_decl_info :
  Bi_outbuf.t -> decl_info -> unit
  (** Output a JSON value of type {!decl_info}. *)

val string_of_decl_info :
  ?len:int -> decl_info -> string
  (** Serialize a value of type {!decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decl_info
  (** Input JSON data of type {!decl_info}. *)

val decl_info_of_string :
  string -> decl_info
  (** Deserialize JSON data of type {!decl_info}. *)

val write_block_captured_variable :
  Bi_outbuf.t -> block_captured_variable -> unit
  (** Output a JSON value of type {!block_captured_variable}. *)

val string_of_block_captured_variable :
  ?len:int -> block_captured_variable -> string
  (** Serialize a value of type {!block_captured_variable}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_block_captured_variable :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> block_captured_variable
  (** Input JSON data of type {!block_captured_variable}. *)

val block_captured_variable_of_string :
  string -> block_captured_variable
  (** Deserialize JSON data of type {!block_captured_variable}. *)

val write_block_decl_info :
  Bi_outbuf.t -> block_decl_info -> unit
  (** Output a JSON value of type {!block_decl_info}. *)

val string_of_block_decl_info :
  ?len:int -> block_decl_info -> string
  (** Serialize a value of type {!block_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_block_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> block_decl_info
  (** Input JSON data of type {!block_decl_info}. *)

val block_decl_info_of_string :
  string -> block_decl_info
  (** Deserialize JSON data of type {!block_decl_info}. *)

val write_cxx_catch_stmt_info :
  Bi_outbuf.t -> cxx_catch_stmt_info -> unit
  (** Output a JSON value of type {!cxx_catch_stmt_info}. *)

val string_of_cxx_catch_stmt_info :
  ?len:int -> cxx_catch_stmt_info -> string
  (** Serialize a value of type {!cxx_catch_stmt_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_catch_stmt_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_catch_stmt_info
  (** Input JSON data of type {!cxx_catch_stmt_info}. *)

val cxx_catch_stmt_info_of_string :
  string -> cxx_catch_stmt_info
  (** Deserialize JSON data of type {!cxx_catch_stmt_info}. *)

val write_cxx_ctor_initializer :
  Bi_outbuf.t -> cxx_ctor_initializer -> unit
  (** Output a JSON value of type {!cxx_ctor_initializer}. *)

val string_of_cxx_ctor_initializer :
  ?len:int -> cxx_ctor_initializer -> string
  (** Serialize a value of type {!cxx_ctor_initializer}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_ctor_initializer :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_ctor_initializer
  (** Input JSON data of type {!cxx_ctor_initializer}. *)

val cxx_ctor_initializer_of_string :
  string -> cxx_ctor_initializer
  (** Deserialize JSON data of type {!cxx_ctor_initializer}. *)

val write_cxx_default_expr_info :
  Bi_outbuf.t -> cxx_default_expr_info -> unit
  (** Output a JSON value of type {!cxx_default_expr_info}. *)

val string_of_cxx_default_expr_info :
  ?len:int -> cxx_default_expr_info -> string
  (** Serialize a value of type {!cxx_default_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_default_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_default_expr_info
  (** Input JSON data of type {!cxx_default_expr_info}. *)

val cxx_default_expr_info_of_string :
  string -> cxx_default_expr_info
  (** Deserialize JSON data of type {!cxx_default_expr_info}. *)

val write_cxx_method_decl_info :
  Bi_outbuf.t -> cxx_method_decl_info -> unit
  (** Output a JSON value of type {!cxx_method_decl_info}. *)

val string_of_cxx_method_decl_info :
  ?len:int -> cxx_method_decl_info -> string
  (** Serialize a value of type {!cxx_method_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_cxx_method_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> cxx_method_decl_info
  (** Input JSON data of type {!cxx_method_decl_info}. *)

val cxx_method_decl_info_of_string :
  string -> cxx_method_decl_info
  (** Deserialize JSON data of type {!cxx_method_decl_info}. *)

val write_decl :
  Bi_outbuf.t -> decl -> unit
  (** Output a JSON value of type {!decl}. *)

val string_of_decl :
  ?len:int -> decl -> string
  (** Serialize a value of type {!decl}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decl :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decl
  (** Input JSON data of type {!decl}. *)

val decl_of_string :
  string -> decl
  (** Deserialize JSON data of type {!decl}. *)

val write_enum_constant_decl_info :
  Bi_outbuf.t -> enum_constant_decl_info -> unit
  (** Output a JSON value of type {!enum_constant_decl_info}. *)

val string_of_enum_constant_decl_info :
  ?len:int -> enum_constant_decl_info -> string
  (** Serialize a value of type {!enum_constant_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_enum_constant_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> enum_constant_decl_info
  (** Input JSON data of type {!enum_constant_decl_info}. *)

val enum_constant_decl_info_of_string :
  string -> enum_constant_decl_info
  (** Deserialize JSON data of type {!enum_constant_decl_info}. *)

val write_field_decl_info :
  Bi_outbuf.t -> field_decl_info -> unit
  (** Output a JSON value of type {!field_decl_info}. *)

val string_of_field_decl_info :
  ?len:int -> field_decl_info -> string
  (** Serialize a value of type {!field_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_field_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> field_decl_info
  (** Input JSON data of type {!field_decl_info}. *)

val field_decl_info_of_string :
  string -> field_decl_info
  (** Deserialize JSON data of type {!field_decl_info}. *)

val write_friend_info :
  Bi_outbuf.t -> friend_info -> unit
  (** Output a JSON value of type {!friend_info}. *)

val string_of_friend_info :
  ?len:int -> friend_info -> string
  (** Serialize a value of type {!friend_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_friend_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> friend_info
  (** Input JSON data of type {!friend_info}. *)

val friend_info_of_string :
  string -> friend_info
  (** Deserialize JSON data of type {!friend_info}. *)

val write_function_decl_info :
  Bi_outbuf.t -> function_decl_info -> unit
  (** Output a JSON value of type {!function_decl_info}. *)

val string_of_function_decl_info :
  ?len:int -> function_decl_info -> string
  (** Serialize a value of type {!function_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_function_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> function_decl_info
  (** Input JSON data of type {!function_decl_info}. *)

val function_decl_info_of_string :
  string -> function_decl_info
  (** Deserialize JSON data of type {!function_decl_info}. *)

val write_lambda_expr_info :
  Bi_outbuf.t -> lambda_expr_info -> unit
  (** Output a JSON value of type {!lambda_expr_info}. *)

val string_of_lambda_expr_info :
  ?len:int -> lambda_expr_info -> string
  (** Serialize a value of type {!lambda_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_lambda_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> lambda_expr_info
  (** Input JSON data of type {!lambda_expr_info}. *)

val lambda_expr_info_of_string :
  string -> lambda_expr_info
  (** Deserialize JSON data of type {!lambda_expr_info}. *)

val write_obj_c_implementation_decl_info :
  Bi_outbuf.t -> obj_c_implementation_decl_info -> unit
  (** Output a JSON value of type {!obj_c_implementation_decl_info}. *)

val string_of_obj_c_implementation_decl_info :
  ?len:int -> obj_c_implementation_decl_info -> string
  (** Serialize a value of type {!obj_c_implementation_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_implementation_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_implementation_decl_info
  (** Input JSON data of type {!obj_c_implementation_decl_info}. *)

val obj_c_implementation_decl_info_of_string :
  string -> obj_c_implementation_decl_info
  (** Deserialize JSON data of type {!obj_c_implementation_decl_info}. *)

val write_obj_c_message_expr_kind :
  Bi_outbuf.t -> obj_c_message_expr_kind -> unit
  (** Output a JSON value of type {!obj_c_message_expr_kind}. *)

val string_of_obj_c_message_expr_kind :
  ?len:int -> obj_c_message_expr_kind -> string
  (** Serialize a value of type {!obj_c_message_expr_kind}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_message_expr_kind :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_message_expr_kind
  (** Input JSON data of type {!obj_c_message_expr_kind}. *)

val obj_c_message_expr_kind_of_string :
  string -> obj_c_message_expr_kind
  (** Deserialize JSON data of type {!obj_c_message_expr_kind}. *)

val write_obj_c_method_decl_info :
  Bi_outbuf.t -> obj_c_method_decl_info -> unit
  (** Output a JSON value of type {!obj_c_method_decl_info}. *)

val string_of_obj_c_method_decl_info :
  ?len:int -> obj_c_method_decl_info -> string
  (** Serialize a value of type {!obj_c_method_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_obj_c_method_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> obj_c_method_decl_info
  (** Input JSON data of type {!obj_c_method_decl_info}. *)

val obj_c_method_decl_info_of_string :
  string -> obj_c_method_decl_info
  (** Deserialize JSON data of type {!obj_c_method_decl_info}. *)

val write_opaque_value_expr_info :
  Bi_outbuf.t -> opaque_value_expr_info -> unit
  (** Output a JSON value of type {!opaque_value_expr_info}. *)

val string_of_opaque_value_expr_info :
  ?len:int -> opaque_value_expr_info -> string
  (** Serialize a value of type {!opaque_value_expr_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_opaque_value_expr_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> opaque_value_expr_info
  (** Input JSON data of type {!opaque_value_expr_info}. *)

val opaque_value_expr_info_of_string :
  string -> opaque_value_expr_info
  (** Deserialize JSON data of type {!opaque_value_expr_info}. *)

val write_stmt :
  Bi_outbuf.t -> stmt -> unit
  (** Output a JSON value of type {!stmt}. *)

val string_of_stmt :
  ?len:int -> stmt -> string
  (** Serialize a value of type {!stmt}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_stmt :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> stmt
  (** Input JSON data of type {!stmt}. *)

val stmt_of_string :
  string -> stmt
  (** Deserialize JSON data of type {!stmt}. *)

val write_template_decl_info :
  Bi_outbuf.t -> template_decl_info -> unit
  (** Output a JSON value of type {!template_decl_info}. *)

val string_of_template_decl_info :
  ?len:int -> template_decl_info -> string
  (** Serialize a value of type {!template_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_template_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> template_decl_info
  (** Input JSON data of type {!template_decl_info}. *)

val template_decl_info_of_string :
  string -> template_decl_info
  (** Deserialize JSON data of type {!template_decl_info}. *)

val write_var_decl_info :
  Bi_outbuf.t -> var_decl_info -> unit
  (** Output a JSON value of type {!var_decl_info}. *)

val string_of_var_decl_info :
  ?len:int -> var_decl_info -> string
  (** Serialize a value of type {!var_decl_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_var_decl_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> var_decl_info
  (** Input JSON data of type {!var_decl_info}. *)

val var_decl_info_of_string :
  string -> var_decl_info
  (** Deserialize JSON data of type {!var_decl_info}. *)

val write_lookup :
  Bi_outbuf.t -> lookup -> unit
  (** Output a JSON value of type {!lookup}. *)

val string_of_lookup :
  ?len:int -> lookup -> string
  (** Serialize a value of type {!lookup}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_lookup :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> lookup
  (** Input JSON data of type {!lookup}. *)

val lookup_of_string :
  string -> lookup
  (** Deserialize JSON data of type {!lookup}. *)

val write_lookups :
  Bi_outbuf.t -> lookups -> unit
  (** Output a JSON value of type {!lookups}. *)

val string_of_lookups :
  ?len:int -> lookups -> string
  (** Serialize a value of type {!lookups}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_lookups :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> lookups
  (** Input JSON data of type {!lookups}. *)

val lookups_of_string :
  string -> lookups
  (** Deserialize JSON data of type {!lookups}. *)

val write_access_specifier :
  Bi_outbuf.t -> access_specifier -> unit
  (** Output a JSON value of type {!access_specifier}. *)

val string_of_access_specifier :
  ?len:int -> access_specifier -> string
  (** Serialize a value of type {!access_specifier}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_access_specifier :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> access_specifier
  (** Input JSON data of type {!access_specifier}. *)

val access_specifier_of_string :
  string -> access_specifier
  (** Deserialize JSON data of type {!access_specifier}. *)

