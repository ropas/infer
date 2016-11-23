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

let validate__1 = (
  fun _ _ -> None
)
let validate__2 = (
  fun _ _ -> None
)
let validate__28 = (
  fun _ _ -> None
)
let validate__3 = (
  fun _ _ -> None
)
let validate_binary_operator_kind = (
  fun _ _ -> None
)
let validate_binary_operator_info : _ -> binary_operator_info -> _ = (
  fun _ _ -> None
)
let validate_builtin_type_kind = (
  fun _ _ -> None
)
let validate_cast_kind = (
  fun _ _ -> None
)
let validate_cxx_base_specifier : _ -> cxx_base_specifier -> _ = (
  fun _ _ -> None
)
let validate__23 = (
  fun _ _ -> None
)
let validate_cast_expr_info : _ -> cast_expr_info -> _ = (
  fun _ _ -> None
)
let validate_cxx_noexcept_expr_info : _ -> cxx_noexcept_expr_info -> _ = (
  fun _ _ -> None
)
let validate_decl_context_info : _ -> decl_context_info -> _ = (
  fun _ _ -> None
)
let validate_decl_kind = (
  fun _ _ -> None
)
let validate_declaration_name_kind = (
  fun _ _ -> None
)
let validate_declaration_name : _ -> declaration_name -> _ = (
  fun _ _ -> None
)
let validate_enum_decl_scope = (
  fun _ _ -> None
)
let validate__14 = (
  fun _ _ -> None
)
let validate_enum_decl_info : _ -> enum_decl_info -> _ = (
  fun _ _ -> None
)
let validate_input_kind = (
  fun _ _ -> None
)
let validate_integer_literal_info : _ -> integer_literal_info -> _ = (
  fun _ _ -> None
)
let validate_lambda_capture_kind = (
  fun _ _ -> None
)
let validate_named_decl_info : _ -> named_decl_info -> _ = (
  fun _ _ -> None
)
let validate__4 = (
  fun _ _ -> None
)
let validate_obj_c_access_control = (
  fun _ _ -> None
)
let validate_obj_c_ivar_decl_info : _ -> obj_c_ivar_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_property_control = (
  fun _ _ -> None
)
let validate_obj_c_subscript_kind = (
  fun _ _ -> None
)
let validate_objc_lifetime_attr = (
  fun _ _ -> None
)
let validate_object_kind = (
  fun _ _ -> None
)
let validate_opt_type = (
  fun _ _ -> None
)
let validate_pointer = (
  (fun _ _ -> None)
)
let validate__29 = (
  fun _ _ -> None
)
let validate__6 = (
  fun _ _ -> None
)
let validate_addr_label_expr_info : _ -> addr_label_expr_info -> _ = (
  fun _ _ -> None
)
let validate_cxx_new_expr_info : _ -> cxx_new_expr_info -> _ = (
  fun _ _ -> None
)
let validate_cxx_temporary = (
  validate_pointer
)
let validate_cxx_bind_temporary_expr_info : _ -> cxx_bind_temporary_expr_info -> _ = (
  fun _ _ -> None
)
let validate_goto_stmt_info : _ -> goto_stmt_info -> _ = (
  fun _ _ -> None
)
let validate_predefined_expr_type = (
  fun _ _ -> None
)
let validate_previous_decl = (
  fun _ _ -> None
)
let validate_property_attribute = (
  fun _ _ -> None
)
let validate__19 = (
  fun _ _ -> None
)
let validate_property_implementation = (
  fun _ _ -> None
)
let validate_record_decl_info : _ -> record_decl_info -> _ = (
  fun _ _ -> None
)
let validate_selector = (
  (fun _ _ -> None)
)
let validate__25 = (
  fun _ _ -> None
)
let validate_obj_c_method_ref_info : _ -> obj_c_method_ref_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_subscript_ref_expr_info : _ -> obj_c_subscript_ref_expr_info -> _ = (
  fun _ _ -> None
)
let validate_objc_boxed_expr_info : _ -> objc_boxed_expr_info -> _ = (
  fun _ _ -> None
)
let validate_source_location : _ -> source_location -> _ = (
  Clang_ast_visit.visit_source_loc
)
let validate_source_range = (
  fun path x ->
    match
      (let x, _ = x in
      (
        validate_source_location
      ) (`Index 0 :: path) x
      )
    with
      | Some _ as err -> err
      | None ->
        (let _, x = x in
        (
          validate_source_location
        ) (`Index 1 :: path) x
        )
)
let validate_attribute_info : _ -> attribute_info -> _ = (
  fun path x ->
    (
      validate_source_range
    ) (`Field "ai_source_range" :: path) x.ai_source_range
)
let validate_attribute : _ -> attribute -> _ = (
  fun path x ->
    match x with
      | FallThroughAttr x ->
        (
          validate_attribute_info
        ) path x
      | SwiftContextAttr x ->
        (
          validate_attribute_info
        ) path x
      | SwiftErrorResultAttr x ->
        (
          validate_attribute_info
        ) path x
      | SwiftIndirectResultAttr x ->
        (
          validate_attribute_info
        ) path x
      | AnnotateAttr x ->
        (
          validate_attribute_info
        ) path x
      | CFConsumedAttr x ->
        (
          validate_attribute_info
        ) path x
      | CarriesDependencyAttr x ->
        (
          validate_attribute_info
        ) path x
      | NSConsumedAttr x ->
        (
          validate_attribute_info
        ) path x
      | PassObjectSizeAttr x ->
        (
          validate_attribute_info
        ) path x
      | AMDGPUNumSGPRAttr x ->
        (
          validate_attribute_info
        ) path x
      | AMDGPUNumVGPRAttr x ->
        (
          validate_attribute_info
        ) path x
      | ARMInterruptAttr x ->
        (
          validate_attribute_info
        ) path x
      | AcquireCapabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | AcquiredAfterAttr x ->
        (
          validate_attribute_info
        ) path x
      | AcquiredBeforeAttr x ->
        (
          validate_attribute_info
        ) path x
      | AlignMac68kAttr x ->
        (
          validate_attribute_info
        ) path x
      | AlignedAttr x ->
        (
          validate_attribute_info
        ) path x
      | AlwaysInlineAttr x ->
        (
          validate_attribute_info
        ) path x
      | AnalyzerNoReturnAttr x ->
        (
          validate_attribute_info
        ) path x
      | AnyX86InterruptAttr x ->
        (
          validate_attribute_info
        ) path x
      | ArcWeakrefUnavailableAttr x ->
        (
          validate_attribute_info
        ) path x
      | ArgumentWithTypeTagAttr x ->
        (
          validate_attribute_info
        ) path x
      | AsmLabelAttr x ->
        (
          validate_attribute_info
        ) path x
      | AssertCapabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | AssertExclusiveLockAttr x ->
        (
          validate_attribute_info
        ) path x
      | AssertSharedLockAttr x ->
        (
          validate_attribute_info
        ) path x
      | AssumeAlignedAttr x ->
        (
          validate_attribute_info
        ) path x
      | AvailabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | BlocksAttr x ->
        (
          validate_attribute_info
        ) path x
      | C11NoReturnAttr x ->
        (
          validate_attribute_info
        ) path x
      | CDeclAttr x ->
        (
          validate_attribute_info
        ) path x
      | CFAuditedTransferAttr x ->
        (
          validate_attribute_info
        ) path x
      | CFReturnsNotRetainedAttr x ->
        (
          validate_attribute_info
        ) path x
      | CFReturnsRetainedAttr x ->
        (
          validate_attribute_info
        ) path x
      | CFUnknownTransferAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDAConstantAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDADeviceAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDAGlobalAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDAHostAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDAInvalidTargetAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDALaunchBoundsAttr x ->
        (
          validate_attribute_info
        ) path x
      | CUDASharedAttr x ->
        (
          validate_attribute_info
        ) path x
      | CXX11NoReturnAttr x ->
        (
          validate_attribute_info
        ) path x
      | CallableWhenAttr x ->
        (
          validate_attribute_info
        ) path x
      | CapabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | CapturedRecordAttr x ->
        (
          validate_attribute_info
        ) path x
      | CleanupAttr x ->
        (
          validate_attribute_info
        ) path x
      | ColdAttr x ->
        (
          validate_attribute_info
        ) path x
      | CommonAttr x ->
        (
          validate_attribute_info
        ) path x
      | ConstAttr x ->
        (
          validate_attribute_info
        ) path x
      | ConstructorAttr x ->
        (
          validate_attribute_info
        ) path x
      | ConsumableAttr x ->
        (
          validate_attribute_info
        ) path x
      | ConsumableAutoCastAttr x ->
        (
          validate_attribute_info
        ) path x
      | ConsumableSetOnReadAttr x ->
        (
          validate_attribute_info
        ) path x
      | DLLExportAttr x ->
        (
          validate_attribute_info
        ) path x
      | DLLImportAttr x ->
        (
          validate_attribute_info
        ) path x
      | DeprecatedAttr x ->
        (
          validate_attribute_info
        ) path x
      | DestructorAttr x ->
        (
          validate_attribute_info
        ) path x
      | DisableTailCallsAttr x ->
        (
          validate_attribute_info
        ) path x
      | EmptyBasesAttr x ->
        (
          validate_attribute_info
        ) path x
      | EnableIfAttr x ->
        (
          validate_attribute_info
        ) path x
      | ExclusiveTrylockFunctionAttr x ->
        (
          validate_attribute_info
        ) path x
      | FastCallAttr x ->
        (
          validate_attribute_info
        ) path x
      | FinalAttr x ->
        (
          validate_attribute_info
        ) path x
      | FlagEnumAttr x ->
        (
          validate_attribute_info
        ) path x
      | FlattenAttr x ->
        (
          validate_attribute_info
        ) path x
      | FormatAttr x ->
        (
          validate_attribute_info
        ) path x
      | FormatArgAttr x ->
        (
          validate_attribute_info
        ) path x
      | GNUInlineAttr x ->
        (
          validate_attribute_info
        ) path x
      | GuardedByAttr x ->
        (
          validate_attribute_info
        ) path x
      | GuardedVarAttr x ->
        (
          validate_attribute_info
        ) path x
      | HotAttr x ->
        (
          validate_attribute_info
        ) path x
      | IBActionAttr x ->
        (
          validate_attribute_info
        ) path x
      | IBOutletAttr x ->
        (
          validate_attribute_info
        ) path x
      | IBOutletCollectionAttr x ->
        (
          validate_attribute_info
        ) path x
      | InitPriorityAttr x ->
        (
          validate_attribute_info
        ) path x
      | IntelOclBiccAttr x ->
        (
          validate_attribute_info
        ) path x
      | InternalLinkageAttr x ->
        (
          validate_attribute_info
        ) path x
      | LTOVisibilityPublicAttr x ->
        (
          validate_attribute_info
        ) path x
      | LayoutVersionAttr x ->
        (
          validate_attribute_info
        ) path x
      | LockReturnedAttr x ->
        (
          validate_attribute_info
        ) path x
      | LocksExcludedAttr x ->
        (
          validate_attribute_info
        ) path x
      | MSABIAttr x ->
        (
          validate_attribute_info
        ) path x
      | MSInheritanceAttr x ->
        (
          validate_attribute_info
        ) path x
      | MSNoVTableAttr x ->
        (
          validate_attribute_info
        ) path x
      | MSP430InterruptAttr x ->
        (
          validate_attribute_info
        ) path x
      | MSStructAttr x ->
        (
          validate_attribute_info
        ) path x
      | MSVtorDispAttr x ->
        (
          validate_attribute_info
        ) path x
      | MaxFieldAlignmentAttr x ->
        (
          validate_attribute_info
        ) path x
      | MayAliasAttr x ->
        (
          validate_attribute_info
        ) path x
      | MinSizeAttr x ->
        (
          validate_attribute_info
        ) path x
      | Mips16Attr x ->
        (
          validate_attribute_info
        ) path x
      | MipsInterruptAttr x ->
        (
          validate_attribute_info
        ) path x
      | NSConsumesSelfAttr x ->
        (
          validate_attribute_info
        ) path x
      | NSReturnsAutoreleasedAttr x ->
        (
          validate_attribute_info
        ) path x
      | NSReturnsNotRetainedAttr x ->
        (
          validate_attribute_info
        ) path x
      | NSReturnsRetainedAttr x ->
        (
          validate_attribute_info
        ) path x
      | NakedAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoAliasAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoCommonAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoDebugAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoDuplicateAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoInlineAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoInstrumentFunctionAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoMips16Attr x ->
        (
          validate_attribute_info
        ) path x
      | NoReturnAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoSanitizeAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoSplitStackAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoThreadSafetyAnalysisAttr x ->
        (
          validate_attribute_info
        ) path x
      | NoThrowAttr x ->
        (
          validate_attribute_info
        ) path x
      | NonNullAttr x ->
        (
          validate_attribute_info
        ) path x
      | NotTailCalledAttr x ->
        (
          validate_attribute_info
        ) path x
      | OMPCaptureNoInitAttr x ->
        (
          validate_attribute_info
        ) path x
      | OMPThreadPrivateDeclAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCBridgeAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCBridgeMutableAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCBridgeRelatedAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCExceptionAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCExplicitProtocolImplAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCIndependentClassAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCMethodFamilyAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCNSObjectAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCPreciseLifetimeAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCRequiresPropertyDefsAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCRequiresSuperAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCReturnsInnerPointerAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCRootClassAttr x ->
        (
          validate_attribute_info
        ) path x
      | OpenCLKernelAttr x ->
        (
          validate_attribute_info
        ) path x
      | OpenCLUnrollHintAttr x ->
        (
          validate_attribute_info
        ) path x
      | OptimizeNoneAttr x ->
        (
          validate_attribute_info
        ) path x
      | OverrideAttr x ->
        (
          validate_attribute_info
        ) path x
      | OwnershipAttr x ->
        (
          validate_attribute_info
        ) path x
      | PackedAttr x ->
        (
          validate_attribute_info
        ) path x
      | ParamTypestateAttr x ->
        (
          validate_attribute_info
        ) path x
      | PascalAttr x ->
        (
          validate_attribute_info
        ) path x
      | PcsAttr x ->
        (
          validate_attribute_info
        ) path x
      | PreserveAllAttr x ->
        (
          validate_attribute_info
        ) path x
      | PreserveMostAttr x ->
        (
          validate_attribute_info
        ) path x
      | PtGuardedByAttr x ->
        (
          validate_attribute_info
        ) path x
      | PtGuardedVarAttr x ->
        (
          validate_attribute_info
        ) path x
      | PureAttr x ->
        (
          validate_attribute_info
        ) path x
      | ReleaseCapabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | ReqdWorkGroupSizeAttr x ->
        (
          validate_attribute_info
        ) path x
      | RequiresCapabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | RestrictAttr x ->
        (
          validate_attribute_info
        ) path x
      | ReturnTypestateAttr x ->
        (
          validate_attribute_info
        ) path x
      | ReturnsNonNullAttr x ->
        (
          validate_attribute_info
        ) path x
      | ReturnsTwiceAttr x ->
        (
          validate_attribute_info
        ) path x
      | ScopedLockableAttr x ->
        (
          validate_attribute_info
        ) path x
      | SectionAttr x ->
        (
          validate_attribute_info
        ) path x
      | SelectAnyAttr x ->
        (
          validate_attribute_info
        ) path x
      | SentinelAttr x ->
        (
          validate_attribute_info
        ) path x
      | SetTypestateAttr x ->
        (
          validate_attribute_info
        ) path x
      | SharedTrylockFunctionAttr x ->
        (
          validate_attribute_info
        ) path x
      | StdCallAttr x ->
        (
          validate_attribute_info
        ) path x
      | SwiftCallAttr x ->
        (
          validate_attribute_info
        ) path x
      | SysVABIAttr x ->
        (
          validate_attribute_info
        ) path x
      | TLSModelAttr x ->
        (
          validate_attribute_info
        ) path x
      | TargetAttr x ->
        (
          validate_attribute_info
        ) path x
      | TestTypestateAttr x ->
        (
          validate_attribute_info
        ) path x
      | ThisCallAttr x ->
        (
          validate_attribute_info
        ) path x
      | TransparentUnionAttr x ->
        (
          validate_attribute_info
        ) path x
      | TryAcquireCapabilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | TypeTagForDatatypeAttr x ->
        (
          validate_attribute_info
        ) path x
      | TypeVisibilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | UnavailableAttr x ->
        (
          validate_attribute_info
        ) path x
      | UnusedAttr x ->
        (
          validate_attribute_info
        ) path x
      | UsedAttr x ->
        (
          validate_attribute_info
        ) path x
      | UuidAttr x ->
        (
          validate_attribute_info
        ) path x
      | VecReturnAttr x ->
        (
          validate_attribute_info
        ) path x
      | VecTypeHintAttr x ->
        (
          validate_attribute_info
        ) path x
      | VectorCallAttr x ->
        (
          validate_attribute_info
        ) path x
      | VisibilityAttr x ->
        (
          validate_attribute_info
        ) path x
      | WarnUnusedAttr x ->
        (
          validate_attribute_info
        ) path x
      | WarnUnusedResultAttr x ->
        (
          validate_attribute_info
        ) path x
      | WeakAttr x ->
        (
          validate_attribute_info
        ) path x
      | WeakImportAttr x ->
        (
          validate_attribute_info
        ) path x
      | WeakRefAttr x ->
        (
          validate_attribute_info
        ) path x
      | WorkGroupSizeHintAttr x ->
        (
          validate_attribute_info
        ) path x
      | X86ForceAlignArgPointerAttr x ->
        (
          validate_attribute_info
        ) path x
      | XRayInstrumentAttr x ->
        (
          validate_attribute_info
        ) path x
      | AbiTagAttr x ->
        (
          validate_attribute_info
        ) path x
      | AliasAttr x ->
        (
          validate_attribute_info
        ) path x
      | AlignValueAttr x ->
        (
          validate_attribute_info
        ) path x
      | IFuncAttr x ->
        (
          validate_attribute_info
        ) path x
      | InitSegAttr x ->
        (
          validate_attribute_info
        ) path x
      | LoopHintAttr x ->
        (
          validate_attribute_info
        ) path x
      | ModeAttr x ->
        (
          validate_attribute_info
        ) path x
      | OMPDeclareSimdDeclAttr x ->
        (
          validate_attribute_info
        ) path x
      | OMPDeclareTargetDeclAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCBoxableAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCDesignatedInitializerAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCRuntimeNameAttr x ->
        (
          validate_attribute_info
        ) path x
      | ObjCRuntimeVisibleAttr x ->
        (
          validate_attribute_info
        ) path x
      | OpenCLAccessAttr x ->
        (
          validate_attribute_info
        ) path x
      | OverloadableAttr x ->
        (
          validate_attribute_info
        ) path x
      | RenderScriptKernelAttr x ->
        (
          validate_attribute_info
        ) path x
      | ThreadAttr x ->
        (
          validate_attribute_info
        ) path x
)
let validate__11 = (
  Ag_ov_run.validate_list (
    validate_attribute
  )
)
let validate_comment_info : _ -> comment_info -> _ = (
  fun path x ->
    (
      validate_source_range
    ) (`Field "ci_source_range" :: path) x.ci_source_range
)
let validate_specifier_kind = (
  fun _ _ -> None
)
let validate_stmt_info : _ -> stmt_info -> _ = (
  fun path x ->
    (
      validate_source_range
    ) (`Field "si_source_range" :: path) x.si_source_range
)
let validate_tls_kind = (
  fun _ _ -> None
)
let validate_type_attribute_kind = (
  fun _ _ -> None
)
let validate_attr_type_info : _ -> attr_type_info -> _ = (
  fun _ _ -> None
)
let validate_type_ptr = (
  validate__28
)
let validate__17 = (
  fun _ _ -> None
)
let validate__5 = (
  fun _ _ -> None
)
let validate_compound_assign_operator_info : _ -> compound_assign_operator_info -> _ = (
  fun _ _ -> None
)
let validate_cxx_delete_expr_info : _ -> cxx_delete_expr_info -> _ = (
  fun _ _ -> None
)
let validate_decl_ref : _ -> decl_ref -> _ = (
  fun _ _ -> None
)
let validate__10 = (
  fun _ _ -> None
)
let validate__8 = (
  fun _ _ -> None
)
let validate_cxx_construct_expr_info : _ -> cxx_construct_expr_info -> _ = (
  fun _ _ -> None
)
let validate_cxx_ctor_initializer_subject = (
  fun _ _ -> None
)
let validate_cxx_record_decl_info : _ -> cxx_record_decl_info -> _ = (
  fun _ _ -> None
)
let validate_decl_ref_expr_info : _ -> decl_ref_expr_info -> _ = (
  fun _ _ -> None
)
let validate_expr_with_cleanups_info : _ -> expr_with_cleanups_info -> _ = (
  fun _ _ -> None
)
let validate_function_type_info : _ -> function_type_info -> _ = (
  fun _ _ -> None
)
let validate_lambda_capture_info : _ -> lambda_capture_info -> _ = (
  fun path x ->
    (
      validate_source_range
    ) (`Field "lci_location" :: path) x.lci_location
)
let validate__24 = (
  Ag_ov_run.validate_list (
    validate_lambda_capture_info
  )
)
let validate_materialize_temporary_expr_info : _ -> materialize_temporary_expr_info -> _ = (
  fun _ _ -> None
)
let validate_member_expr_info : _ -> member_expr_info -> _ = (
  fun _ _ -> None
)
let validate_namespace_decl_info : _ -> namespace_decl_info -> _ = (
  fun _ _ -> None
)
let validate_nested_name_specifier_loc : _ -> nested_name_specifier_loc -> _ = (
  fun _ _ -> None
)
let validate__16 = (
  fun _ _ -> None
)
let validate_namespace_alias_decl_info : _ -> namespace_alias_decl_info -> _ = (
  fun path x ->
    match
      (
        validate_source_location
      ) (`Field "nadi_namespace_loc" :: path) x.nadi_namespace_loc
    with
      | Some _ as err -> err
      | None ->
        (
          validate_source_location
        ) (`Field "nadi_target_name_loc" :: path) x.nadi_target_name_loc
)
let validate_obj_c_category_decl_info : _ -> obj_c_category_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_category_impl_decl_info : _ -> obj_c_category_impl_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_compatible_alias_decl_info : _ -> obj_c_compatible_alias_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_interface_decl_info : _ -> obj_c_interface_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_ivar_ref_expr_info : _ -> obj_c_ivar_ref_expr_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_property_decl_info : _ -> obj_c_property_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_property_impl_decl_info : _ -> obj_c_property_impl_decl_info -> _ = (
  fun _ _ -> None
)
let validate_obj_c_protocol_decl_info : _ -> obj_c_protocol_decl_info -> _ = (
  fun _ _ -> None
)
let validate_objc_encode_expr_info : _ -> objc_encode_expr_info -> _ = (
  fun _ _ -> None
)
let validate_objc_object_type_info : _ -> objc_object_type_info -> _ = (
  fun _ _ -> None
)
let validate_overload_expr_info : _ -> overload_expr_info -> _ = (
  fun _ _ -> None
)
let validate_params_type_info : _ -> params_type_info -> _ = (
  fun _ _ -> None
)
let validate_property_ref_kind = (
  fun _ _ -> None
)
let validate_obj_c_property_ref_expr_info : _ -> obj_c_property_ref_expr_info -> _ = (
  fun _ _ -> None
)
let validate_qual_type : _ -> qual_type -> _ = (
  fun _ _ -> None
)
let validate_receiver_kind = (
  fun _ _ -> None
)
let validate_obj_c_message_expr_info : _ -> obj_c_message_expr_info -> _ = (
  fun _ _ -> None
)
let validate_template_instantiation_arg_info = (
  fun _ _ -> None
)
let validate__21 = (
  fun _ _ -> None
)
let validate_type_info : _ -> type_info -> _ = (
  fun _ _ -> None
)
let validate_type_trait_info : _ -> type_trait_info -> _ = (
  fun _ _ -> None
)
let validate_typedef_decl_info : _ -> typedef_decl_info -> _ = (
  fun _ _ -> None
)
let validate_typedef_type_info : _ -> typedef_type_info -> _ = (
  fun _ _ -> None
)
let validate_c_type : _ -> c_type -> _ = (
  Clang_ast_visit.visit_type
)
let validate__13 = (
  Ag_ov_run.validate_list (
    validate_c_type
  )
)
let validate_translation_unit_decl_info : _ -> translation_unit_decl_info -> _ = (
  fun path x ->
    (
      validate__13
    ) (`Field "tudi_types" :: path) x.tudi_types
)
let validate_unary_expr_or_type_trait_kind = (
  fun _ _ -> None
)
let validate_unary_expr_or_type_trait_expr_info : _ -> unary_expr_or_type_trait_expr_info -> _ = (
  fun _ _ -> None
)
let validate_unary_operator_kind = (
  fun _ _ -> None
)
let validate_unary_operator_info : _ -> unary_operator_info -> _ = (
  fun _ _ -> None
)
let validate_unresolved_lookup_expr_info : _ -> unresolved_lookup_expr_info -> _ = (
  fun _ _ -> None
)
let validate_using_directive_decl_info : _ -> using_directive_decl_info -> _ = (
  fun path x ->
    match
      (
        validate_source_location
      ) (`Field "uddi_using_location" :: path) x.uddi_using_location
    with
      | Some _ as err -> err
      | None ->
        (
          validate_source_location
        ) (`Field "uddi_namespace_key_location" :: path) x.uddi_namespace_key_location
)
let validate_value_kind = (
  fun _ _ -> None
)
let validate_expr_info : _ -> expr_info -> _ = (
  fun _ _ -> None
)
let rec validate__27 path x = (
  Ag_ov_run.validate_list (
    validate_comment
  )
) path x
and validate_comment : _ -> comment -> _ = (
  fun path x ->
    match x with
      | BlockCommandComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | ParamCommandComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | TParamCommandComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | VerbatimBlockComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | VerbatimLineComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | ParagraphComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | FullComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | HTMLEndTagComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | HTMLStartTagComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | InlineCommandComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | TextComment x ->
        (
          fun path x ->
            match
              (let x, _, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x, _ = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
      | VerbatimBlockLineComment x ->
        (
          fun path x ->
            match
              (let x, _ = x in
              (
                validate_comment_info
              ) (`Index 0 :: path) x
              )
            with
              | Some _ as err -> err
              | None ->
                (let _, x = x in
                (
                  validate__27
                ) (`Index 1 :: path) x
                )
        ) path x
)
let validate__12 = (
  Ag_ov_run.validate_option (
    validate_comment
  )
)
let validate_decl_info : _ -> decl_info -> _ = (
  fun path x ->
    match
      (
        validate_source_range
      ) (`Field "di_source_range" :: path) x.di_source_range
    with
      | Some _ as err -> err
      | None ->
        match
          (
            validate__11
          ) (`Field "di_attributes" :: path) x.di_attributes
        with
          | Some _ as err -> err
          | None ->
            (
              validate__12
            ) (`Field "di_full_comment" :: path) x.di_full_comment
)
let rec validate__15 path x = (
  Ag_ov_run.validate_list (
    validate_decl
  )
) path x
and validate__18 path x = (
  Ag_ov_run.validate_list (
    validate_cxx_ctor_initializer
  )
) path x
and validate__20 path x = (
  Ag_ov_run.validate_list (
    validate_block_captured_variable
  )
) path x
and validate__22 path x = (
  Ag_ov_run.validate_option (
    validate_decl
  )
) path x
and validate__26 path x = (
  Ag_ov_run.validate_list (
    validate_stmt
  )
) path x
and validate__9 path x = (
  Ag_ov_run.validate_option (
    validate_stmt
  )
) path x
and validate_block_captured_variable : _ -> block_captured_variable -> _ = (
  fun path x ->
    (
      validate__9
    ) (`Field "bcv_copy_expr" :: path) x.bcv_copy_expr
)
and validate_block_decl_info : _ -> block_decl_info -> _ = (
  fun path x ->
    match
      (
        validate__15
      ) (`Field "bdi_parameters" :: path) x.bdi_parameters
    with
      | Some _ as err -> err
      | None ->
        match
          (
            validate__20
          ) (`Field "bdi_captured_variables" :: path) x.bdi_captured_variables
        with
          | Some _ as err -> err
          | None ->
            (
              validate__9
            ) (`Field "bdi_body" :: path) x.bdi_body
)
and validate_cxx_catch_stmt_info : _ -> cxx_catch_stmt_info -> _ = (
  fun path x ->
    (
      validate__22
    ) (`Field "xcsi_variable" :: path) x.xcsi_variable
)
and validate_cxx_ctor_initializer : _ -> cxx_ctor_initializer -> _ = (
  fun path x ->
    match
      (
        validate_source_range
      ) (`Field "xci_source_range" :: path) x.xci_source_range
    with
      | Some _ as err -> err
      | None ->
        (
          validate__9
        ) (`Field "xci_init_expr" :: path) x.xci_init_expr
)
and validate_cxx_default_expr_info : _ -> cxx_default_expr_info -> _ = (
  fun path x ->
    (
      validate__9
    ) (`Field "xdaei_init_expr" :: path) x.xdaei_init_expr
)
and validate_cxx_method_decl_info : _ -> cxx_method_decl_info -> _ = (
  fun path x ->
    (
      validate__18
    ) (`Field "xmdi_cxx_ctor_initializers" :: path) x.xmdi_cxx_ctor_initializers
)
and validate_decl : _ -> decl -> _ = (
  fun path x ->
    match ( Clang_ast_visit.visit_decl ) path x with
      | Some _ as err -> err
      | None ->
        match x with
          | AccessSpecDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | BlockDecl x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate_block_decl_info
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CapturedDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__15
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ClassScopeFunctionSpecializationDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | EmptyDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ExternCContextDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | FileScopeAsmDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | FriendDecl x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate_friend_info
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | FriendTemplateDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ImportDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | LinkageSpecDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__15
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | LabelDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | NamespaceDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | NamespaceAliasDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x = x in
                    (
                      validate_namespace_alias_decl_info
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | ObjCCompatibleAliasDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ObjCCategoryDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | ObjCCategoryImplDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | ObjCImplementationDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, _, x, _, _ = x in
                      (
                        validate__15
                      ) (`Index 2 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, _, x = x in
                        (
                          validate_obj_c_implementation_decl_info
                        ) (`Index 4 :: path) x
                        )
            ) path x
          | ObjCInterfaceDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | ObjCProtocolDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | ObjCMethodDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x = x in
                    (
                      validate_obj_c_method_decl_info
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | ObjCPropertyDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | BuiltinTemplateDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ClassTemplateDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x = x in
                    (
                      validate_template_decl_info
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | FunctionTemplateDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x = x in
                    (
                      validate_template_decl_info
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | TypeAliasTemplateDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | VarTemplateDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | TemplateTemplateParmDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | EnumDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 4 :: path) x
                    )
            ) path x
          | RecordDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, _, x, _, _ = x in
                    (
                      validate__15
                    ) (`Index 4 :: path) x
                    )
            ) path x
          | CXXRecordDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, _, x, _, _, _ = x in
                    (
                      validate__15
                    ) (`Index 4 :: path) x
                    )
            ) path x
          | ClassTemplateSpecializationDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, _, x, _, _, _, _ = x in
                    (
                      validate__15
                    ) (`Index 4 :: path) x
                    )
            ) path x
          | ClassTemplatePartialSpecializationDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, _, x, _, _, _, _ = x in
                    (
                      validate__15
                    ) (`Index 4 :: path) x
                    )
            ) path x
          | TemplateTypeParmDecl x ->
            (
              fun path x ->
                (let x, _, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ObjCTypeParamDecl x ->
            (
              fun path x ->
                (let x, _, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | TypeAliasDecl x ->
            (
              fun path x ->
                (let x, _, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | TypedefDecl x ->
            (
              fun path x ->
                (let x, _, _, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | UnresolvedUsingTypenameDecl x ->
            (
              fun path x ->
                (let x, _, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | UsingDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | UsingDirectiveDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, x = x in
                    (
                      validate_using_directive_decl_info
                    ) (`Index 2 :: path) x
                    )
            ) path x
          | UsingShadowDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ConstructorUsingShadowDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | BindingDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | FieldDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_field_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | ObjCAtDefsFieldDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_field_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | ObjCIvarDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x, _ = x in
                    (
                      validate_field_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | FunctionDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_function_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | CXXMethodDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, _, _, x, _ = x in
                      (
                        validate_function_decl_info
                      ) (`Index 3 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, _, x = x in
                        (
                          validate_cxx_method_decl_info
                        ) (`Index 4 :: path) x
                        )
            ) path x
          | CXXConstructorDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, _, _, x, _ = x in
                      (
                        validate_function_decl_info
                      ) (`Index 3 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, _, x = x in
                        (
                          validate_cxx_method_decl_info
                        ) (`Index 4 :: path) x
                        )
            ) path x
          | CXXConversionDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, _, _, x, _ = x in
                      (
                        validate_function_decl_info
                      ) (`Index 3 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, _, x = x in
                        (
                          validate_cxx_method_decl_info
                        ) (`Index 4 :: path) x
                        )
            ) path x
          | CXXDestructorDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, _, _, x, _ = x in
                      (
                        validate_function_decl_info
                      ) (`Index 3 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, _, x = x in
                        (
                          validate_cxx_method_decl_info
                        ) (`Index 4 :: path) x
                        )
            ) path x
          | MSPropertyDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | NonTypeTemplateParmDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | VarDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | DecompositionDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | ImplicitParamDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | OMPCapturedExprDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | ParmVarDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | VarTemplateSpecializationDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | VarTemplatePartialSpecializationDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_var_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | EnumConstantDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, _, _, x = x in
                    (
                      validate_enum_constant_decl_info
                    ) (`Index 3 :: path) x
                    )
            ) path x
          | IndirectFieldDecl x ->
            (
              fun path x ->
                (let x, _, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | OMPDeclareReductionDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | UnresolvedUsingValueDecl x ->
            (
              fun path x ->
                (let x, _, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | OMPThreadPrivateDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | ObjCPropertyImplDecl x ->
            (
              fun path x ->
                (let x, _ = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | PragmaCommentDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | PragmaDetectMismatchDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | StaticAssertDecl x ->
            (
              fun path x ->
                (let x = x in
                (
                  validate_decl_info
                ) (`Index 0 :: path) x
                )
            ) path x
          | TranslationUnitDecl x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_decl_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _, _ = x in
                      (
                        validate__15
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, x = x in
                        (
                          validate_translation_unit_decl_info
                        ) (`Index 3 :: path) x
                        )
            ) path x
)
and validate_enum_constant_decl_info : _ -> enum_constant_decl_info -> _ = (
  fun path x ->
    (
      validate__9
    ) (`Field "ecdi_init_expr" :: path) x.ecdi_init_expr
)
and validate_field_decl_info : _ -> field_decl_info -> _ = (
  fun path x ->
    match
      (
        validate__9
      ) (`Field "fldi_init_expr" :: path) x.fldi_init_expr
    with
      | Some _ as err -> err
      | None ->
        (
          validate__9
        ) (`Field "fldi_bit_width_expr" :: path) x.fldi_bit_width_expr
)
and validate_friend_info = (
  fun path x ->
    match x with
      | `Type x ->
        (
          validate_type_ptr
        ) path x
      | `Decl x ->
        (
          validate_decl
        ) path x
)
and validate_function_decl_info : _ -> function_decl_info -> _ = (
  fun path x ->
    match
      (
        validate__15
      ) (`Field "fdi_decls_in_prototype_scope" :: path) x.fdi_decls_in_prototype_scope
    with
      | Some _ as err -> err
      | None ->
        match
          (
            validate__15
          ) (`Field "fdi_parameters" :: path) x.fdi_parameters
        with
          | Some _ as err -> err
          | None ->
            (
              validate__9
            ) (`Field "fdi_body" :: path) x.fdi_body
)
and validate_lambda_expr_info : _ -> lambda_expr_info -> _ = (
  fun path x ->
    match
      (
        validate__24
      ) (`Field "lei_captures" :: path) x.lei_captures
    with
      | Some _ as err -> err
      | None ->
        (
          validate_decl
        ) (`Field "lei_lambda_decl" :: path) x.lei_lambda_decl
)
and validate_obj_c_implementation_decl_info : _ -> obj_c_implementation_decl_info -> _ = (
  fun path x ->
    (
      validate__18
    ) (`Field "oidi_ivar_initializers" :: path) x.oidi_ivar_initializers
)
and validate_obj_c_message_expr_kind = (
  fun path x ->
    match x with
      | `CatchParam x ->
        (
          validate_decl
        ) path x
      | `CatchAll -> None
)
and validate_obj_c_method_decl_info : _ -> obj_c_method_decl_info -> _ = (
  fun path x ->
    match
      (
        validate__15
      ) (`Field "omdi_parameters" :: path) x.omdi_parameters
    with
      | Some _ as err -> err
      | None ->
        match
          (
            validate__15
          ) (`Field "omdi_implicit_parameters" :: path) x.omdi_implicit_parameters
        with
          | Some _ as err -> err
          | None ->
            (
              validate__9
            ) (`Field "omdi_body" :: path) x.omdi_body
)
and validate_opaque_value_expr_info : _ -> opaque_value_expr_info -> _ = (
  fun path x ->
    (
      validate__9
    ) (`Field "ovei_source_expr" :: path) x.ovei_source_expr
)
and validate_stmt : _ -> stmt -> _ = (
  fun path x ->
    match ( Clang_ast_visit.visit_stmt ) path x with
      | Some _ as err -> err
      | None ->
        match x with
          | GCCAsmStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | MSAsmStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | AttributedStmt x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, x = x in
                        (
                          validate__11
                        ) (`Index 2 :: path) x
                        )
            ) path x
          | BreakStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXCatchStmt x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, x = x in
                        (
                          validate_cxx_catch_stmt_info
                        ) (`Index 2 :: path) x
                        )
            ) path x
          | CXXForRangeStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXTryStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CapturedStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CompoundStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ContinueStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CoreturnStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CoroutineBodyStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | DeclStmt x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, x = x in
                        (
                          validate__15
                        ) (`Index 2 :: path) x
                        )
            ) path x
          | DoStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | BinaryConditionalOperator x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ConditionalOperator x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | AddrLabelExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ArraySubscriptExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ArrayTypeTraitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | AsTypeExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | AtomicExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | BinaryOperator x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CompoundAssignOperator x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | BlockExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, x = x in
                        (
                          validate_decl
                        ) (`Index 3 :: path) x
                        )
            ) path x
          | CXXBindTemporaryExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXBoolLiteralExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXConstructExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXTemporaryObjectExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXDefaultArgExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, x = x in
                        (
                          validate_cxx_default_expr_info
                        ) (`Index 3 :: path) x
                        )
            ) path x
          | CXXDefaultInitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, x = x in
                        (
                          validate_cxx_default_expr_info
                        ) (`Index 3 :: path) x
                        )
            ) path x
          | CXXDeleteExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXDependentScopeMemberExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXFoldExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXInheritedCtorInitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXNewExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXNoexceptExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXNullPtrLiteralExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXPseudoDestructorExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXScalarValueInitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXStdInitializerListExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXThisExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXThrowExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXTypeidExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXUnresolvedConstructExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXUuidofExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CallExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CUDAKernelCallExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXMemberCallExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXOperatorCallExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | UserDefinedLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CStyleCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXFunctionalCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXConstCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXDynamicCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXReinterpretCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CXXStaticCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCBridgedCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ImplicitCastExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CharacterLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ChooseExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CompoundLiteralExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ConvertVectorExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CoawaitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CoyieldExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | DeclRefExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | DependentScopeDeclRefExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | DesignatedInitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | DesignatedInitUpdateExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ExprWithCleanups x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ExpressionTraitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ExtVectorElementExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | FloatingLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | FunctionParmPackExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | GNUNullExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | GenericSelectionExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ImaginaryLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ImplicitValueInitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | InitListExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | IntegerLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | LambdaExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, x = x in
                        (
                          validate_lambda_expr_info
                        ) (`Index 3 :: path) x
                        )
            ) path x
          | MSPropertyRefExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | MSPropertySubscriptExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | MaterializeTemporaryExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | MemberExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | NoInitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPArraySectionExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCArrayLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCAvailabilityCheckExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCBoolLiteralExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCBoxedExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCDictionaryLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCEncodeExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCIndirectCopyRestoreExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCIsaExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCIvarRefExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCMessageExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCPropertyRefExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCProtocolExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCSelectorExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCStringLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCSubscriptRefExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OffsetOfExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OpaqueValueExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, _, x = x in
                        (
                          validate_opaque_value_expr_info
                        ) (`Index 3 :: path) x
                        )
            ) path x
          | UnresolvedLookupExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | UnresolvedMemberExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | PackExpansionExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ParenExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ParenListExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | PredefinedExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | PseudoObjectExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ShuffleVectorExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SizeOfPackExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | StmtExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | StringLiteral x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SubstNonTypeTemplateParmExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SubstNonTypeTemplateParmPackExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | TypeTraitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | TypoExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | UnaryExprOrTypeTraitExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | UnaryOperator x ->
            (
              fun path x ->
                match
                  (let x, _, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | VAArgExpr x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ForStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | GotoStmt x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | IfStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | IndirectGotoStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | LabelStmt x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x, _ = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | MSDependentExistsStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | NullStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPAtomicDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPBarrierDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPCancelDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPCancellationPointDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPCriticalDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPFlushDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPDistributeDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPDistributeParallelForDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPDistributeParallelForSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPDistributeSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPForDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPForSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPParallelForDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPParallelForSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetParallelForSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTaskLoopDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTaskLoopSimdDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPMasterDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPOrderedDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPParallelDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPParallelSectionsDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPSectionDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPSectionsDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPSingleDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetDataDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetEnterDataDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetExitDataDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetParallelDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetParallelForDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTargetUpdateDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTaskDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTaskgroupDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTaskwaitDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTaskyieldDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | OMPTeamsDirective x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCAtCatchStmt x ->
            (
              fun path x ->
                match
                  (let x, _, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    match
                      (let _, x, _ = x in
                      (
                        validate__26
                      ) (`Index 1 :: path) x
                      )
                    with
                      | Some _ as err -> err
                      | None ->
                        (let _, _, x = x in
                        (
                          validate_obj_c_message_expr_kind
                        ) (`Index 2 :: path) x
                        )
            ) path x
          | ObjCAtFinallyStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCAtSynchronizedStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCAtThrowStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCAtTryStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCAutoreleasePoolStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ObjCForCollectionStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | ReturnStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SEHExceptStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SEHFinallyStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SEHLeaveStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SEHTryStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | CaseStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | DefaultStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | SwitchStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
          | WhileStmt x ->
            (
              fun path x ->
                match
                  (let x, _ = x in
                  (
                    validate_stmt_info
                  ) (`Index 0 :: path) x
                  )
                with
                  | Some _ as err -> err
                  | None ->
                    (let _, x = x in
                    (
                      validate__26
                    ) (`Index 1 :: path) x
                    )
            ) path x
)
and validate_template_decl_info : _ -> template_decl_info -> _ = (
  fun path x ->
    (
      validate__15
    ) (`Field "tdi_specializations" :: path) x.tdi_specializations
)
and validate_var_decl_info : _ -> var_decl_info -> _ = (
  fun path x ->
    (
      validate__9
    ) (`Field "vdi_init_expr" :: path) x.vdi_init_expr
)
let validate_lookup : _ -> lookup -> _ = (
  fun _ _ -> None
)
let validate__7 = (
  fun _ _ -> None
)
let validate_lookups : _ -> lookups -> _ = (
  fun _ _ -> None
)
let validate_access_specifier = (
  fun _ _ -> None
)
let create_binary_operator_info 
  ~boi_kind
  () : binary_operator_info =
  {
    boi_kind = boi_kind;
  }
let create_cxx_base_specifier 
  ~xbs_name
  ?(xbs_virtual = false)
  () : cxx_base_specifier =
  {
    xbs_name = xbs_name;
    xbs_virtual = xbs_virtual;
  }
let create_cast_expr_info 
  ~cei_cast_kind
  ~cei_base_path
  () : cast_expr_info =
  {
    cei_cast_kind = cei_cast_kind;
    cei_base_path = cei_base_path;
  }
let create_cxx_noexcept_expr_info 
  ?(xnee_value = false)
  () : cxx_noexcept_expr_info =
  {
    xnee_value = xnee_value;
  }
let create_decl_context_info 
  ?(dci_has_external_lexical_storage = false)
  ?(dci_has_external_visible_storage = false)
  () : decl_context_info =
  {
    dci_has_external_lexical_storage = dci_has_external_lexical_storage;
    dci_has_external_visible_storage = dci_has_external_visible_storage;
  }
let create_declaration_name 
  ~dn_kind
  ~dn_name
  () : declaration_name =
  {
    dn_kind = dn_kind;
    dn_name = dn_name;
  }
let create_enum_decl_info 
  ?edi_scope
  ?(edi_is_module_private = false)
  () : enum_decl_info =
  {
    edi_scope = edi_scope;
    edi_is_module_private = edi_is_module_private;
  }
let create_integer_literal_info 
  ?(ili_is_signed = false)
  ~ili_bitwidth
  ~ili_value
  () : integer_literal_info =
  {
    ili_is_signed = ili_is_signed;
    ili_bitwidth = ili_bitwidth;
    ili_value = ili_value;
  }
let create_named_decl_info 
  ~ni_name
  ~ni_qual_name
  () : named_decl_info =
  {
    ni_name = ni_name;
    ni_qual_name = ni_qual_name;
  }
let create_obj_c_ivar_decl_info 
  ?(ovdi_is_synthesize = false)
  ?(ovdi_access_control = `None)
  () : obj_c_ivar_decl_info =
  {
    ovdi_is_synthesize = ovdi_is_synthesize;
    ovdi_access_control = ovdi_access_control;
  }
let create_addr_label_expr_info 
  ~alei_label
  ~alei_pointer
  () : addr_label_expr_info =
  {
    alei_label = alei_label;
    alei_pointer = alei_pointer;
  }
let create_cxx_new_expr_info 
  ?(xnei_is_array = false)
  ?xnei_array_size_expr
  ?xnei_initializer_expr
  () : cxx_new_expr_info =
  {
    xnei_is_array = xnei_is_array;
    xnei_array_size_expr = xnei_array_size_expr;
    xnei_initializer_expr = xnei_initializer_expr;
  }
let create_cxx_bind_temporary_expr_info 
  ~xbtei_cxx_temporary
  () : cxx_bind_temporary_expr_info =
  {
    xbtei_cxx_temporary = xbtei_cxx_temporary;
  }
let create_goto_stmt_info 
  ~gsi_label
  ~gsi_pointer
  () : goto_stmt_info =
  {
    gsi_label = gsi_label;
    gsi_pointer = gsi_pointer;
  }
let create_record_decl_info 
  ?(rdi_is_module_private = false)
  ?(rdi_is_complete_definition = false)
  () : record_decl_info =
  {
    rdi_is_module_private = rdi_is_module_private;
    rdi_is_complete_definition = rdi_is_complete_definition;
  }
let create_obj_c_method_ref_info 
  ?mri_getter
  ?mri_setter
  () : obj_c_method_ref_info =
  {
    mri_getter = mri_getter;
    mri_setter = mri_setter;
  }
let create_obj_c_subscript_ref_expr_info 
  ~osrei_kind
  ?osrei_getter
  ?osrei_setter
  () : obj_c_subscript_ref_expr_info =
  {
    osrei_kind = osrei_kind;
    osrei_getter = osrei_getter;
    osrei_setter = osrei_setter;
  }
let create_objc_boxed_expr_info 
  ?obei_boxing_method
  () : objc_boxed_expr_info =
  {
    obei_boxing_method = obei_boxing_method;
  }
let create_source_location 
  ?sl_file
  ?sl_line
  ?sl_column
  () : source_location =
  {
    sl_file = sl_file;
    sl_line = sl_line;
    sl_column = sl_column;
  }
let create_attribute_info 
  ~ai_pointer
  ~ai_source_range
  ~ai_parameters
  ?(ai_is_inherited = false)
  ?(ai_is_implicit = false)
  () : attribute_info =
  {
    ai_pointer = ai_pointer;
    ai_source_range = ai_source_range;
    ai_parameters = ai_parameters;
    ai_is_inherited = ai_is_inherited;
    ai_is_implicit = ai_is_implicit;
  }
let create_comment_info 
  ~ci_parent_pointer
  ~ci_source_range
  () : comment_info =
  {
    ci_parent_pointer = ci_parent_pointer;
    ci_source_range = ci_source_range;
  }
let create_stmt_info 
  ~si_pointer
  ~si_source_range
  () : stmt_info =
  {
    si_pointer = si_pointer;
    si_source_range = si_source_range;
  }
let create_attr_type_info 
  ~ati_attr_kind
  ?(ati_lifetime = `OCL_None)
  () : attr_type_info =
  {
    ati_attr_kind = ati_attr_kind;
    ati_lifetime = ati_lifetime;
  }
let create_compound_assign_operator_info 
  ~caoi_lhs_type
  ~caoi_result_type
  () : compound_assign_operator_info =
  {
    caoi_lhs_type = caoi_lhs_type;
    caoi_result_type = caoi_result_type;
  }
let create_cxx_delete_expr_info 
  ?(xdei_is_array = false)
  ~xdei_destroyed_type
  () : cxx_delete_expr_info =
  {
    xdei_is_array = xdei_is_array;
    xdei_destroyed_type = xdei_destroyed_type;
  }
let create_decl_ref 
  ~dr_kind
  ~dr_decl_pointer
  ?dr_name
  ?(dr_is_hidden = false)
  ?dr_type_ptr
  () : decl_ref =
  {
    dr_kind = dr_kind;
    dr_decl_pointer = dr_decl_pointer;
    dr_name = dr_name;
    dr_is_hidden = dr_is_hidden;
    dr_type_ptr = dr_type_ptr;
  }
let create_cxx_construct_expr_info 
  ~xcei_decl_ref
  ?(xcei_is_elidable = false)
  ?(xcei_requires_zero_initialization = false)
  () : cxx_construct_expr_info =
  {
    xcei_decl_ref = xcei_decl_ref;
    xcei_is_elidable = xcei_is_elidable;
    xcei_requires_zero_initialization = xcei_requires_zero_initialization;
  }
let create_cxx_record_decl_info 
  ?(xrdi_bases = [])
  ?(xrdi_vbases = [])
  ?(xrdi_is_pod = false)
  ?xrdi_destructor
  ?xrdi_lambda_call_operator
  () : cxx_record_decl_info =
  {
    xrdi_bases = xrdi_bases;
    xrdi_vbases = xrdi_vbases;
    xrdi_is_pod = xrdi_is_pod;
    xrdi_destructor = xrdi_destructor;
    xrdi_lambda_call_operator = xrdi_lambda_call_operator;
  }
let create_decl_ref_expr_info 
  ?drti_decl_ref
  ?drti_found_decl_ref
  () : decl_ref_expr_info =
  {
    drti_decl_ref = drti_decl_ref;
    drti_found_decl_ref = drti_found_decl_ref;
  }
let create_expr_with_cleanups_info 
  ?(ewci_decl_refs = [])
  () : expr_with_cleanups_info =
  {
    ewci_decl_refs = ewci_decl_refs;
  }
let create_function_type_info 
  ~fti_return_type
  () : function_type_info =
  {
    fti_return_type = fti_return_type;
  }
let create_lambda_capture_info 
  ~lci_capture_kind
  ?(lci_capture_this = false)
  ?(lci_capture_variable = false)
  ?(lci_capture_VLAtype = false)
  ?lci_captured_var
  ?(lci_is_implicit = false)
  ~lci_location
  ?(lci_is_pack_expansion = false)
  () : lambda_capture_info =
  {
    lci_capture_kind = lci_capture_kind;
    lci_capture_this = lci_capture_this;
    lci_capture_variable = lci_capture_variable;
    lci_capture_VLAtype = lci_capture_VLAtype;
    lci_captured_var = lci_captured_var;
    lci_is_implicit = lci_is_implicit;
    lci_location = lci_location;
    lci_is_pack_expansion = lci_is_pack_expansion;
  }
let create_materialize_temporary_expr_info 
  ?mtei_decl_ref
  () : materialize_temporary_expr_info =
  {
    mtei_decl_ref = mtei_decl_ref;
  }
let create_member_expr_info 
  ?(mei_is_arrow = false)
  ?(mei_performs_virtual_dispatch = false)
  ~mei_name
  ~mei_decl_ref
  () : member_expr_info =
  {
    mei_is_arrow = mei_is_arrow;
    mei_performs_virtual_dispatch = mei_performs_virtual_dispatch;
    mei_name = mei_name;
    mei_decl_ref = mei_decl_ref;
  }
let create_namespace_decl_info 
  ?(ndi_is_inline = false)
  ?ndi_original_namespace
  () : namespace_decl_info =
  {
    ndi_is_inline = ndi_is_inline;
    ndi_original_namespace = ndi_original_namespace;
  }
let create_nested_name_specifier_loc 
  ~nnsl_kind
  ?nnsl_ref
  () : nested_name_specifier_loc =
  {
    nnsl_kind = nnsl_kind;
    nnsl_ref = nnsl_ref;
  }
let create_namespace_alias_decl_info 
  ~nadi_namespace_loc
  ~nadi_target_name_loc
  ~nadi_nested_name_specifier_locs
  ~nadi_namespace
  () : namespace_alias_decl_info =
  {
    nadi_namespace_loc = nadi_namespace_loc;
    nadi_target_name_loc = nadi_target_name_loc;
    nadi_nested_name_specifier_locs = nadi_nested_name_specifier_locs;
    nadi_namespace = nadi_namespace;
  }
let create_obj_c_category_decl_info 
  ?odi_class_interface
  ?odi_implementation
  ?(odi_protocols = [])
  () : obj_c_category_decl_info =
  {
    odi_class_interface = odi_class_interface;
    odi_implementation = odi_implementation;
    odi_protocols = odi_protocols;
  }
let create_obj_c_category_impl_decl_info 
  ?ocidi_class_interface
  ?ocidi_category_decl
  () : obj_c_category_impl_decl_info =
  {
    ocidi_class_interface = ocidi_class_interface;
    ocidi_category_decl = ocidi_category_decl;
  }
let create_obj_c_compatible_alias_decl_info 
  ?ocadi_class_interface
  () : obj_c_compatible_alias_decl_info =
  {
    ocadi_class_interface = ocadi_class_interface;
  }
let create_obj_c_interface_decl_info 
  ?otdi_super
  ?otdi_implementation
  ?(otdi_protocols = [])
  ?(otdi_known_categories = [])
  () : obj_c_interface_decl_info =
  {
    otdi_super = otdi_super;
    otdi_implementation = otdi_implementation;
    otdi_protocols = otdi_protocols;
    otdi_known_categories = otdi_known_categories;
  }
let create_obj_c_ivar_ref_expr_info 
  ~ovrei_decl_ref
  ~ovrei_pointer
  ?(ovrei_is_free_ivar = false)
  () : obj_c_ivar_ref_expr_info =
  {
    ovrei_decl_ref = ovrei_decl_ref;
    ovrei_pointer = ovrei_pointer;
    ovrei_is_free_ivar = ovrei_is_free_ivar;
  }
let create_obj_c_property_decl_info 
  ~opdi_type_ptr
  ?opdi_getter_method
  ?opdi_setter_method
  ?opdi_ivar_decl
  ?(opdi_property_control = `None)
  ?(opdi_property_attributes = [])
  () : obj_c_property_decl_info =
  {
    opdi_type_ptr = opdi_type_ptr;
    opdi_getter_method = opdi_getter_method;
    opdi_setter_method = opdi_setter_method;
    opdi_ivar_decl = opdi_ivar_decl;
    opdi_property_control = opdi_property_control;
    opdi_property_attributes = opdi_property_attributes;
  }
let create_obj_c_property_impl_decl_info 
  ~opidi_implementation
  ?opidi_property_decl
  ?opidi_ivar_decl
  () : obj_c_property_impl_decl_info =
  {
    opidi_implementation = opidi_implementation;
    opidi_property_decl = opidi_property_decl;
    opidi_ivar_decl = opidi_ivar_decl;
  }
let create_obj_c_protocol_decl_info 
  ?(opcdi_protocols = [])
  () : obj_c_protocol_decl_info =
  {
    opcdi_protocols = opcdi_protocols;
  }
let create_objc_encode_expr_info 
  ~oeei_type_ptr
  ~oeei_raw
  () : objc_encode_expr_info =
  {
    oeei_type_ptr = oeei_type_ptr;
    oeei_raw = oeei_raw;
  }
let create_objc_object_type_info 
  ~base_type
  ?(protocol_decls_ptr = [])
  () : objc_object_type_info =
  {
    base_type = base_type;
    protocol_decls_ptr = protocol_decls_ptr;
  }
let create_overload_expr_info 
  ?(oei_decls = [])
  ~oei_name
  () : overload_expr_info =
  {
    oei_decls = oei_decls;
    oei_name = oei_name;
  }
let create_params_type_info 
  ?(pti_params_type = [])
  () : params_type_info =
  {
    pti_params_type = pti_params_type;
  }
let create_obj_c_property_ref_expr_info 
  ~oprei_kind
  ?(oprei_is_super_receiver = false)
  ?(oprei_is_messaging_getter = false)
  ?(oprei_is_messaging_setter = false)
  () : obj_c_property_ref_expr_info =
  {
    oprei_kind = oprei_kind;
    oprei_is_super_receiver = oprei_is_super_receiver;
    oprei_is_messaging_getter = oprei_is_messaging_getter;
    oprei_is_messaging_setter = oprei_is_messaging_setter;
  }
let create_qual_type 
  ~qt_type_ptr
  ?(qt_is_const = false)
  () : qual_type =
  {
    qt_type_ptr = qt_type_ptr;
    qt_is_const = qt_is_const;
  }
let create_obj_c_message_expr_info 
  ~omei_selector
  ?(omei_is_definition_found = false)
  ?omei_decl_pointer
  ?(omei_receiver_kind = `Instance)
  () : obj_c_message_expr_info =
  {
    omei_selector = omei_selector;
    omei_is_definition_found = omei_is_definition_found;
    omei_decl_pointer = omei_decl_pointer;
    omei_receiver_kind = omei_receiver_kind;
  }
let create_type_info 
  ~ti_pointer
  ?ti_desugared_type
  () : type_info =
  {
    ti_pointer = ti_pointer;
    ti_desugared_type = ti_desugared_type;
  }
let create_type_trait_info 
  ?(xtti_value = false)
  () : type_trait_info =
  {
    xtti_value = xtti_value;
  }
let create_typedef_decl_info 
  ?(tdi_is_module_private = false)
  () : typedef_decl_info =
  {
    tdi_is_module_private = tdi_is_module_private;
  }
let create_typedef_type_info 
  ~tti_child_type
  ~tti_decl_ptr
  () : typedef_type_info =
  {
    tti_child_type = tti_child_type;
    tti_decl_ptr = tti_decl_ptr;
  }
let create_translation_unit_decl_info 
  ~tudi_input_path
  ~tudi_input_kind
  ?(tudi_arc_enabled = false)
  ~tudi_types
  () : translation_unit_decl_info =
  {
    tudi_input_path = tudi_input_path;
    tudi_input_kind = tudi_input_kind;
    tudi_arc_enabled = tudi_arc_enabled;
    tudi_types = tudi_types;
  }
let create_unary_expr_or_type_trait_expr_info 
  ~uttei_kind
  ?uttei_type_ptr
  () : unary_expr_or_type_trait_expr_info =
  {
    uttei_kind = uttei_kind;
    uttei_type_ptr = uttei_type_ptr;
  }
let create_unary_operator_info 
  ~uoi_kind
  ?(uoi_is_postfix = false)
  () : unary_operator_info =
  {
    uoi_kind = uoi_kind;
    uoi_is_postfix = uoi_is_postfix;
  }
let create_unresolved_lookup_expr_info 
  ?(ulei_requires_ADL = false)
  ?(ulei_is_overloaded = false)
  ?ulei_naming_class
  () : unresolved_lookup_expr_info =
  {
    ulei_requires_ADL = ulei_requires_ADL;
    ulei_is_overloaded = ulei_is_overloaded;
    ulei_naming_class = ulei_naming_class;
  }
let create_using_directive_decl_info 
  ~uddi_using_location
  ~uddi_namespace_key_location
  ~uddi_nested_name_specifier_locs
  ?uddi_nominated_namespace
  () : using_directive_decl_info =
  {
    uddi_using_location = uddi_using_location;
    uddi_namespace_key_location = uddi_namespace_key_location;
    uddi_nested_name_specifier_locs = uddi_nested_name_specifier_locs;
    uddi_nominated_namespace = uddi_nominated_namespace;
  }
let create_expr_info 
  ~ei_type_ptr
  ?(ei_value_kind = `RValue)
  ?(ei_object_kind = `Ordinary)
  () : expr_info =
  {
    ei_type_ptr = ei_type_ptr;
    ei_value_kind = ei_value_kind;
    ei_object_kind = ei_object_kind;
  }
let create_decl_info 
  ~di_pointer
  ?di_parent_pointer
  ?(di_previous_decl = `None)
  ~di_source_range
  ?di_owning_module
  ?(di_is_hidden = false)
  ?(di_is_implicit = false)
  ?(di_is_used = false)
  ?(di_is_this_declaration_referenced = false)
  ?(di_is_invalid_decl = false)
  ?(di_attributes = [])
  ?di_full_comment
  () : decl_info =
  {
    di_pointer = di_pointer;
    di_parent_pointer = di_parent_pointer;
    di_previous_decl = di_previous_decl;
    di_source_range = di_source_range;
    di_owning_module = di_owning_module;
    di_is_hidden = di_is_hidden;
    di_is_implicit = di_is_implicit;
    di_is_used = di_is_used;
    di_is_this_declaration_referenced = di_is_this_declaration_referenced;
    di_is_invalid_decl = di_is_invalid_decl;
    di_attributes = di_attributes;
    di_full_comment = di_full_comment;
  }
let create_block_captured_variable 
  ?(bcv_is_by_ref = false)
  ?(bcv_is_nested = false)
  ?bcv_variable
  ?bcv_copy_expr
  () : block_captured_variable =
  {
    bcv_is_by_ref = bcv_is_by_ref;
    bcv_is_nested = bcv_is_nested;
    bcv_variable = bcv_variable;
    bcv_copy_expr = bcv_copy_expr;
  }
let create_block_decl_info 
  ?(bdi_parameters = [])
  ?(bdi_is_variadic = false)
  ?(bdi_captures_cxx_this = false)
  ?(bdi_captured_variables = [])
  ?bdi_body
  () : block_decl_info =
  {
    bdi_parameters = bdi_parameters;
    bdi_is_variadic = bdi_is_variadic;
    bdi_captures_cxx_this = bdi_captures_cxx_this;
    bdi_captured_variables = bdi_captured_variables;
    bdi_body = bdi_body;
  }
let create_cxx_catch_stmt_info 
  ?xcsi_variable
  () : cxx_catch_stmt_info =
  {
    xcsi_variable = xcsi_variable;
  }
let create_cxx_ctor_initializer 
  ~xci_subject
  ~xci_source_range
  ?xci_init_expr
  () : cxx_ctor_initializer =
  {
    xci_subject = xci_subject;
    xci_source_range = xci_source_range;
    xci_init_expr = xci_init_expr;
  }
let create_cxx_default_expr_info 
  ?xdaei_init_expr
  () : cxx_default_expr_info =
  {
    xdaei_init_expr = xdaei_init_expr;
  }
let create_cxx_method_decl_info 
  ?(xmdi_is_virtual = false)
  ?(xmdi_is_static = false)
  ?(xmdi_cxx_ctor_initializers = [])
  ?(xmdi_overriden_methods = [])
  () : cxx_method_decl_info =
  {
    xmdi_is_virtual = xmdi_is_virtual;
    xmdi_is_static = xmdi_is_static;
    xmdi_cxx_ctor_initializers = xmdi_cxx_ctor_initializers;
    xmdi_overriden_methods = xmdi_overriden_methods;
  }
let create_enum_constant_decl_info 
  ?ecdi_init_expr
  () : enum_constant_decl_info =
  {
    ecdi_init_expr = ecdi_init_expr;
  }
let create_field_decl_info 
  ?(fldi_is_mutable = false)
  ?(fldi_is_module_private = false)
  ?fldi_init_expr
  ?fldi_bit_width_expr
  () : field_decl_info =
  {
    fldi_is_mutable = fldi_is_mutable;
    fldi_is_module_private = fldi_is_module_private;
    fldi_init_expr = fldi_init_expr;
    fldi_bit_width_expr = fldi_bit_width_expr;
  }
let create_function_decl_info 
  ?fdi_mangled_name
  ?fdi_storage_class
  ?(fdi_is_inline = false)
  ?(fdi_is_module_private = false)
  ?(fdi_is_pure = false)
  ?(fdi_is_delete_as_written = false)
  ?(fdi_decls_in_prototype_scope = [])
  ?(fdi_parameters = [])
  ?fdi_decl_ptr_with_body
  ?fdi_body
  () : function_decl_info =
  {
    fdi_mangled_name = fdi_mangled_name;
    fdi_storage_class = fdi_storage_class;
    fdi_is_inline = fdi_is_inline;
    fdi_is_module_private = fdi_is_module_private;
    fdi_is_pure = fdi_is_pure;
    fdi_is_delete_as_written = fdi_is_delete_as_written;
    fdi_decls_in_prototype_scope = fdi_decls_in_prototype_scope;
    fdi_parameters = fdi_parameters;
    fdi_decl_ptr_with_body = fdi_decl_ptr_with_body;
    fdi_body = fdi_body;
  }
let create_lambda_expr_info 
  ?(lei_captures = [])
  ~lei_lambda_decl
  () : lambda_expr_info =
  {
    lei_captures = lei_captures;
    lei_lambda_decl = lei_lambda_decl;
  }
let create_obj_c_implementation_decl_info 
  ?oidi_super
  ?oidi_class_interface
  ?(oidi_ivar_initializers = [])
  () : obj_c_implementation_decl_info =
  {
    oidi_super = oidi_super;
    oidi_class_interface = oidi_class_interface;
    oidi_ivar_initializers = oidi_ivar_initializers;
  }
let create_obj_c_method_decl_info 
  ?(omdi_is_instance_method = false)
  ~omdi_result_type
  ?(omdi_is_property_accessor = false)
  ?omdi_property_decl
  ?(omdi_parameters = [])
  ?(omdi_implicit_parameters = [])
  ?(omdi_is_variadic = false)
  ?omdi_body
  () : obj_c_method_decl_info =
  {
    omdi_is_instance_method = omdi_is_instance_method;
    omdi_result_type = omdi_result_type;
    omdi_is_property_accessor = omdi_is_property_accessor;
    omdi_property_decl = omdi_property_decl;
    omdi_parameters = omdi_parameters;
    omdi_implicit_parameters = omdi_implicit_parameters;
    omdi_is_variadic = omdi_is_variadic;
    omdi_body = omdi_body;
  }
let create_opaque_value_expr_info 
  ?ovei_source_expr
  () : opaque_value_expr_info =
  {
    ovei_source_expr = ovei_source_expr;
  }
let create_template_decl_info 
  ?(tdi_specializations = [])
  () : template_decl_info =
  {
    tdi_specializations = tdi_specializations;
  }
let create_var_decl_info 
  ?vdi_storage_class
  ?(vdi_tls_kind = `Tls_none)
  ?(vdi_is_global = false)
  ?(vdi_is_static_local = false)
  ?(vdi_is_module_private = false)
  ?(vdi_is_nrvo_variable = false)
  ?(vdi_is_const_expr = false)
  ?vdi_init_expr
  ?vdi_parm_index_in_function
  () : var_decl_info =
  {
    vdi_storage_class = vdi_storage_class;
    vdi_tls_kind = vdi_tls_kind;
    vdi_is_global = vdi_is_global;
    vdi_is_static_local = vdi_is_static_local;
    vdi_is_module_private = vdi_is_module_private;
    vdi_is_nrvo_variable = vdi_is_nrvo_variable;
    vdi_is_const_expr = vdi_is_const_expr;
    vdi_init_expr = vdi_init_expr;
    vdi_parm_index_in_function = vdi_parm_index_in_function;
  }
let create_lookup 
  ~lup_decl_name
  ~lup_decl_refs
  () : lookup =
  {
    lup_decl_name = lup_decl_name;
    lup_decl_refs = lup_decl_refs;
  }
let create_lookups 
  ~lups_decl_ref
  ?lups_primary_context_pointer
  ~lups_lookups
  ?(lups_has_undeserialized_decls = false)
  () : lookups =
  {
    lups_decl_ref = lups_decl_ref;
    lups_primary_context_pointer = lups_primary_context_pointer;
    lups_lookups = lups_lookups;
    lups_has_undeserialized_decls = lups_has_undeserialized_decls;
  }
