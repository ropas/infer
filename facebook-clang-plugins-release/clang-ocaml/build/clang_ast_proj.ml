(*
 * Copyright (c) 2014, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 *)
open Clang_ast_t
let get_decl_kind_string = function
| AccessSpecDecl (decl_info) -> "AccessSpec" ^ "Decl"
| BlockDecl (decl_info , block_decl_info) -> "Block" ^ "Decl"
| CapturedDecl (decl_info , decl_list , decl_context_info) -> "Captured" ^ "Decl"
| ClassScopeFunctionSpecializationDecl (decl_info) -> "ClassScopeFunctionSpecialization" ^ "Decl"
| EmptyDecl (decl_info) -> "Empty" ^ "Decl"
| ExternCContextDecl (decl_info) -> "ExternCContext" ^ "Decl"
| FileScopeAsmDecl (decl_info , string) -> "FileScopeAsm" ^ "Decl"
| FriendDecl (decl_info , friend_info) -> "Friend" ^ "Decl"
| FriendTemplateDecl (decl_info) -> "FriendTemplate" ^ "Decl"
| ImportDecl (decl_info , string) -> "Import" ^ "Decl"
| LinkageSpecDecl (decl_info , decl_list , decl_context_info) -> "LinkageSpec" ^ "Decl"
| LabelDecl (decl_info , named_decl_info) -> "Label" ^ "Decl"
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> "Namespace" ^ "Decl"
| NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info) -> "NamespaceAlias" ^ "Decl"
| ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info) -> "ObjCCompatibleAlias" ^ "Decl"
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> "ObjCCategory" ^ "Decl"
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> "ObjCCategoryImpl" ^ "Decl"
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> "ObjCImplementation" ^ "Decl"
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> "ObjCInterface" ^ "Decl"
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> "ObjCProtocol" ^ "Decl"
| ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info) -> "ObjCMethod" ^ "Decl"
| ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info) -> "ObjCProperty" ^ "Decl"
| BuiltinTemplateDecl (decl_info , named_decl_info) -> "BuiltinTemplate" ^ "Decl"
| ClassTemplateDecl (decl_info , named_decl_info , template_decl_info) -> "ClassTemplate" ^ "Decl"
| FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info) -> "FunctionTemplate" ^ "Decl"
| TypeAliasTemplateDecl (decl_info , named_decl_info) -> "TypeAliasTemplate" ^ "Decl"
| VarTemplateDecl (decl_info , named_decl_info) -> "VarTemplate" ^ "Decl"
| TemplateTemplateParmDecl (decl_info , named_decl_info) -> "TemplateTemplateParm" ^ "Decl"
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> "Enum" ^ "Decl"
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> "Record" ^ "Decl"
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> "CXXRecord" ^ "Decl"
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> "ClassTemplateSpecialization" ^ "Decl"
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> "ClassTemplatePartialSpecialization" ^ "Decl"
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> "TemplateTypeParm" ^ "Decl"
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> "ObjCTypeParam" ^ "Decl"
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> "TypeAlias" ^ "Decl"
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> "Typedef" ^ "Decl"
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> "UnresolvedUsingTypename" ^ "Decl"
| UsingDecl (decl_info , named_decl_info) -> "Using" ^ "Decl"
| UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info) -> "UsingDirective" ^ "Decl"
| UsingShadowDecl (decl_info , named_decl_info) -> "UsingShadow" ^ "Decl"
| ConstructorUsingShadowDecl (decl_info , named_decl_info) -> "ConstructorUsingShadow" ^ "Decl"
| BindingDecl (decl_info , named_decl_info , qual_type) -> "Binding" ^ "Decl"
| FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> "Field" ^ "Decl"
| ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> "ObjCAtDefsField" ^ "Decl"
| ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info) -> "ObjCIvar" ^ "Decl"
| FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info) -> "Function" ^ "Decl"
| CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> "CXXMethod" ^ "Decl"
| CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> "CXXConstructor" ^ "Decl"
| CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> "CXXConversion" ^ "Decl"
| CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> "CXXDestructor" ^ "Decl"
| MSPropertyDecl (decl_info , named_decl_info , qual_type) -> "MSProperty" ^ "Decl"
| NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type) -> "NonTypeTemplateParm" ^ "Decl"
| VarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "Var" ^ "Decl"
| DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "Decomposition" ^ "Decl"
| ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "ImplicitParam" ^ "Decl"
| OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "OMPCapturedExpr" ^ "Decl"
| ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "ParmVar" ^ "Decl"
| VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "VarTemplateSpecialization" ^ "Decl"
| VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> "VarTemplatePartialSpecialization" ^ "Decl"
| EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info) -> "EnumConstant" ^ "Decl"
| IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list) -> "IndirectField" ^ "Decl"
| OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type) -> "OMPDeclareReduction" ^ "Decl"
| UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type) -> "UnresolvedUsingValue" ^ "Decl"
| OMPThreadPrivateDecl (decl_info) -> "OMPThreadPrivate" ^ "Decl"
| ObjCPropertyImplDecl (decl_info , obj_c_property_impl_decl_info) -> "ObjCPropertyImpl" ^ "Decl"
| PragmaCommentDecl (decl_info) -> "PragmaComment" ^ "Decl"
| PragmaDetectMismatchDecl (decl_info) -> "PragmaDetectMismatch" ^ "Decl"
| StaticAssertDecl (decl_info) -> "StaticAssert" ^ "Decl"
| TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info) -> "TranslationUnit" ^ "Decl"
let get_decl_tuple = function
| AccessSpecDecl (decl_info) -> (decl_info)
| BlockDecl (decl_info , block_decl_info) -> (decl_info)
| CapturedDecl (decl_info , decl_list , decl_context_info) -> (decl_info)
| ClassScopeFunctionSpecializationDecl (decl_info) -> (decl_info)
| EmptyDecl (decl_info) -> (decl_info)
| ExternCContextDecl (decl_info) -> (decl_info)
| FileScopeAsmDecl (decl_info , string) -> (decl_info)
| FriendDecl (decl_info , friend_info) -> (decl_info)
| FriendTemplateDecl (decl_info) -> (decl_info)
| ImportDecl (decl_info , string) -> (decl_info)
| LinkageSpecDecl (decl_info , decl_list , decl_context_info) -> (decl_info)
| LabelDecl (decl_info , named_decl_info) -> (decl_info)
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> (decl_info)
| NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info) -> (decl_info)
| ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info) -> (decl_info)
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> (decl_info)
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> (decl_info)
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> (decl_info)
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> (decl_info)
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> (decl_info)
| ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info) -> (decl_info)
| ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info) -> (decl_info)
| BuiltinTemplateDecl (decl_info , named_decl_info) -> (decl_info)
| ClassTemplateDecl (decl_info , named_decl_info , template_decl_info) -> (decl_info)
| FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info) -> (decl_info)
| TypeAliasTemplateDecl (decl_info , named_decl_info) -> (decl_info)
| VarTemplateDecl (decl_info , named_decl_info) -> (decl_info)
| TemplateTemplateParmDecl (decl_info , named_decl_info) -> (decl_info)
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> (decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> (decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> (decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> (decl_info)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> (decl_info)
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> (decl_info)
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> (decl_info)
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> (decl_info)
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> (decl_info)
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> (decl_info)
| UsingDecl (decl_info , named_decl_info) -> (decl_info)
| UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info) -> (decl_info)
| UsingShadowDecl (decl_info , named_decl_info) -> (decl_info)
| ConstructorUsingShadowDecl (decl_info , named_decl_info) -> (decl_info)
| BindingDecl (decl_info , named_decl_info , qual_type) -> (decl_info)
| FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> (decl_info)
| ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> (decl_info)
| ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info) -> (decl_info)
| FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info) -> (decl_info)
| CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> (decl_info)
| CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> (decl_info)
| CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> (decl_info)
| CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> (decl_info)
| MSPropertyDecl (decl_info , named_decl_info , qual_type) -> (decl_info)
| NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type) -> (decl_info)
| VarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> (decl_info)
| EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info) -> (decl_info)
| IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list) -> (decl_info)
| OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type) -> (decl_info)
| UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type) -> (decl_info)
| OMPThreadPrivateDecl (decl_info) -> (decl_info)
| ObjCPropertyImplDecl (decl_info , obj_c_property_impl_decl_info) -> (decl_info)
| PragmaCommentDecl (decl_info) -> (decl_info)
| PragmaDetectMismatchDecl (decl_info) -> (decl_info)
| StaticAssertDecl (decl_info) -> (decl_info)
| TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info) -> (decl_info)
let update_decl_tuple __f = function
| AccessSpecDecl (decl_info) -> let (decl_info) = __f (decl_info) in AccessSpecDecl (decl_info)
| BlockDecl (decl_info , block_decl_info) -> let (decl_info) = __f (decl_info) in BlockDecl (decl_info , block_decl_info)
| CapturedDecl (decl_info , decl_list , decl_context_info) -> let (decl_info) = __f (decl_info) in CapturedDecl (decl_info , decl_list , decl_context_info)
| ClassScopeFunctionSpecializationDecl (decl_info) -> let (decl_info) = __f (decl_info) in ClassScopeFunctionSpecializationDecl (decl_info)
| EmptyDecl (decl_info) -> let (decl_info) = __f (decl_info) in EmptyDecl (decl_info)
| ExternCContextDecl (decl_info) -> let (decl_info) = __f (decl_info) in ExternCContextDecl (decl_info)
| FileScopeAsmDecl (decl_info , string) -> let (decl_info) = __f (decl_info) in FileScopeAsmDecl (decl_info , string)
| FriendDecl (decl_info , friend_info) -> let (decl_info) = __f (decl_info) in FriendDecl (decl_info , friend_info)
| FriendTemplateDecl (decl_info) -> let (decl_info) = __f (decl_info) in FriendTemplateDecl (decl_info)
| ImportDecl (decl_info , string) -> let (decl_info) = __f (decl_info) in ImportDecl (decl_info , string)
| LinkageSpecDecl (decl_info , decl_list , decl_context_info) -> let (decl_info) = __f (decl_info) in LinkageSpecDecl (decl_info , decl_list , decl_context_info)
| LabelDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in LabelDecl (decl_info , named_decl_info)
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> let (decl_info) = __f (decl_info) in NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info)
| NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info) -> let (decl_info) = __f (decl_info) in NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info)
| ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info) -> let (decl_info) = __f (decl_info) in ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info)
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> let (decl_info) = __f (decl_info) in ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info)
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> let (decl_info) = __f (decl_info) in ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info)
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> let (decl_info) = __f (decl_info) in ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info)
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> let (decl_info) = __f (decl_info) in ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info)
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> let (decl_info) = __f (decl_info) in ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info)
| ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info) -> let (decl_info) = __f (decl_info) in ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info)
| ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info) -> let (decl_info) = __f (decl_info) in ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info)
| BuiltinTemplateDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in BuiltinTemplateDecl (decl_info , named_decl_info)
| ClassTemplateDecl (decl_info , named_decl_info , template_decl_info) -> let (decl_info) = __f (decl_info) in ClassTemplateDecl (decl_info , named_decl_info , template_decl_info)
| FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info) -> let (decl_info) = __f (decl_info) in FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info)
| TypeAliasTemplateDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in TypeAliasTemplateDecl (decl_info , named_decl_info)
| VarTemplateDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in VarTemplateDecl (decl_info , named_decl_info)
| TemplateTemplateParmDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in TemplateTemplateParmDecl (decl_info , named_decl_info)
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> let (decl_info) = __f (decl_info) in EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> let (decl_info) = __f (decl_info) in RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> let (decl_info) = __f (decl_info) in CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info) = __f (decl_info) in ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info) = __f (decl_info) in ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info) = __f (decl_info) in TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr)
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info) = __f (decl_info) in ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr)
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info) = __f (decl_info) in TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr)
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> let (decl_info) = __f (decl_info) in TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info)
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info) = __f (decl_info) in UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr)
| UsingDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in UsingDecl (decl_info , named_decl_info)
| UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info) -> let (decl_info) = __f (decl_info) in UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info)
| UsingShadowDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in UsingShadowDecl (decl_info , named_decl_info)
| ConstructorUsingShadowDecl (decl_info , named_decl_info) -> let (decl_info) = __f (decl_info) in ConstructorUsingShadowDecl (decl_info , named_decl_info)
| BindingDecl (decl_info , named_decl_info , qual_type) -> let (decl_info) = __f (decl_info) in BindingDecl (decl_info , named_decl_info , qual_type)
| FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> let (decl_info) = __f (decl_info) in FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info)
| ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> let (decl_info) = __f (decl_info) in ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info)
| ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info) -> let (decl_info) = __f (decl_info) in ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info)
| FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info) -> let (decl_info) = __f (decl_info) in FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info)
| CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info) = __f (decl_info) in CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info) = __f (decl_info) in CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info) = __f (decl_info) in CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info) = __f (decl_info) in CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| MSPropertyDecl (decl_info , named_decl_info , qual_type) -> let (decl_info) = __f (decl_info) in MSPropertyDecl (decl_info , named_decl_info , qual_type)
| NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type) -> let (decl_info) = __f (decl_info) in NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type)
| VarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in VarDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info) = __f (decl_info) in VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info) -> let (decl_info) = __f (decl_info) in EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info)
| IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list) -> let (decl_info) = __f (decl_info) in IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list)
| OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type) -> let (decl_info) = __f (decl_info) in OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type)
| UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type) -> let (decl_info) = __f (decl_info) in UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type)
| OMPThreadPrivateDecl (decl_info) -> let (decl_info) = __f (decl_info) in OMPThreadPrivateDecl (decl_info)
| ObjCPropertyImplDecl (decl_info , obj_c_property_impl_decl_info) -> let (decl_info) = __f (decl_info) in ObjCPropertyImplDecl (decl_info , obj_c_property_impl_decl_info)
| PragmaCommentDecl (decl_info) -> let (decl_info) = __f (decl_info) in PragmaCommentDecl (decl_info)
| PragmaDetectMismatchDecl (decl_info) -> let (decl_info) = __f (decl_info) in PragmaDetectMismatchDecl (decl_info)
| StaticAssertDecl (decl_info) -> let (decl_info) = __f (decl_info) in StaticAssertDecl (decl_info)
| TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info) -> let (decl_info) = __f (decl_info) in TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info)
let get_decl_context_tuple = function
(* skipping Function and ObjCMethod *)
| CapturedDecl (decl_info , decl_list , decl_context_info) -> Some (decl_list , decl_context_info)
| LinkageSpecDecl (decl_info , decl_list , decl_context_info) -> Some (decl_list , decl_context_info)
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> Some (decl_list , decl_context_info)
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> Some (decl_list , decl_context_info)
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> Some (decl_list , decl_context_info)
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> Some (decl_list , decl_context_info)
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> Some (decl_list , decl_context_info)
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> Some (decl_list , decl_context_info)
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> Some (decl_list , decl_context_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> Some (decl_list , decl_context_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> Some (decl_list , decl_context_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_list , decl_context_info)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_list , decl_context_info)
| TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info) -> Some (decl_list , decl_context_info)
| _ -> None
let update_decl_context_tuple __f = function
(* skipping Function and ObjCMethod *)
| CapturedDecl (decl_info , decl_list , decl_context_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in CapturedDecl (decl_info , decl_list , decl_context_info)
| LinkageSpecDecl (decl_info , decl_list , decl_context_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in LinkageSpecDecl (decl_info , decl_list , decl_context_info)
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info)
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info)
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info)
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info)
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info)
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info)
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info) -> let (decl_list , decl_context_info) = __f (decl_list , decl_context_info) in TranslationUnitDecl (decl_info , decl_list , decl_context_info , translation_unit_decl_info)
| x -> x
let get_named_decl_tuple = function
| LabelDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> Some (decl_info , named_decl_info)
| NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info) -> Some (decl_info , named_decl_info)
| ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info) -> Some (decl_info , named_decl_info)
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> Some (decl_info , named_decl_info)
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> Some (decl_info , named_decl_info)
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> Some (decl_info , named_decl_info)
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> Some (decl_info , named_decl_info)
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> Some (decl_info , named_decl_info)
| ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info) -> Some (decl_info , named_decl_info)
| ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info) -> Some (decl_info , named_decl_info)
| BuiltinTemplateDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| ClassTemplateDecl (decl_info , named_decl_info , template_decl_info) -> Some (decl_info , named_decl_info)
| FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info) -> Some (decl_info , named_decl_info)
| TypeAliasTemplateDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| VarTemplateDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| TemplateTemplateParmDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> Some (decl_info , named_decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> Some (decl_info , named_decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> Some (decl_info , named_decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_info , named_decl_info)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_info , named_decl_info)
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info)
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info)
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info)
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> Some (decl_info , named_decl_info)
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info)
| UsingDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info) -> Some (decl_info , named_decl_info)
| UsingShadowDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| ConstructorUsingShadowDecl (decl_info , named_decl_info) -> Some (decl_info , named_decl_info)
| BindingDecl (decl_info , named_decl_info , qual_type) -> Some (decl_info , named_decl_info)
| FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> Some (decl_info , named_decl_info)
| ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> Some (decl_info , named_decl_info)
| ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info) -> Some (decl_info , named_decl_info)
| FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info) -> Some (decl_info , named_decl_info)
| CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> Some (decl_info , named_decl_info)
| CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> Some (decl_info , named_decl_info)
| CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> Some (decl_info , named_decl_info)
| CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> Some (decl_info , named_decl_info)
| MSPropertyDecl (decl_info , named_decl_info , qual_type) -> Some (decl_info , named_decl_info)
| NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type) -> Some (decl_info , named_decl_info)
| VarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> Some (decl_info , named_decl_info)
| EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info) -> Some (decl_info , named_decl_info)
| IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list) -> Some (decl_info , named_decl_info)
| OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type) -> Some (decl_info , named_decl_info)
| UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type) -> Some (decl_info , named_decl_info)
| _ -> None
let update_named_decl_tuple __f = function
| LabelDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in LabelDecl (decl_info , named_decl_info)
| NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in NamespaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , namespace_decl_info)
| NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in NamespaceAliasDecl (decl_info , named_decl_info , namespace_alias_decl_info)
| ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCCompatibleAliasDecl (decl_info , named_decl_info , obj_c_compatible_alias_decl_info)
| ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCCategoryDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_decl_info)
| ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCCategoryImplDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_category_impl_decl_info)
| ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCImplementationDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_implementation_decl_info)
| ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCInterfaceDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_interface_decl_info)
| ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCProtocolDecl (decl_info , named_decl_info , decl_list , decl_context_info , obj_c_protocol_decl_info)
| ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCMethodDecl (decl_info , named_decl_info , obj_c_method_decl_info)
| ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCPropertyDecl (decl_info , named_decl_info , obj_c_property_decl_info)
| BuiltinTemplateDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in BuiltinTemplateDecl (decl_info , named_decl_info)
| ClassTemplateDecl (decl_info , named_decl_info , template_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ClassTemplateDecl (decl_info , named_decl_info , template_decl_info)
| FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in FunctionTemplateDecl (decl_info , named_decl_info , template_decl_info)
| TypeAliasTemplateDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in TypeAliasTemplateDecl (decl_info , named_decl_info)
| VarTemplateDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in VarTemplateDecl (decl_info , named_decl_info)
| TemplateTemplateParmDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in TemplateTemplateParmDecl (decl_info , named_decl_info)
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr)
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr)
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr)
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info)
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr)
| UsingDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in UsingDecl (decl_info , named_decl_info)
| UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in UsingDirectiveDecl (decl_info , named_decl_info , using_directive_decl_info)
| UsingShadowDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in UsingShadowDecl (decl_info , named_decl_info)
| ConstructorUsingShadowDecl (decl_info , named_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ConstructorUsingShadowDecl (decl_info , named_decl_info)
| BindingDecl (decl_info , named_decl_info , qual_type) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in BindingDecl (decl_info , named_decl_info , qual_type)
| FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in FieldDecl (decl_info , named_decl_info , qual_type , field_decl_info)
| ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCAtDefsFieldDecl (decl_info , named_decl_info , qual_type , field_decl_info)
| ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ObjCIvarDecl (decl_info , named_decl_info , qual_type , field_decl_info , obj_c_ivar_decl_info)
| FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in FunctionDecl (decl_info , named_decl_info , qual_type , function_decl_info)
| CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in CXXMethodDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in CXXConstructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in CXXConversionDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in CXXDestructorDecl (decl_info , named_decl_info , qual_type , function_decl_info , cxx_method_decl_info)
| MSPropertyDecl (decl_info , named_decl_info , qual_type) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in MSPropertyDecl (decl_info , named_decl_info , qual_type)
| NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in NonTypeTemplateParmDecl (decl_info , named_decl_info , qual_type)
| VarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in VarDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in DecompositionDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ImplicitParamDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in OMPCapturedExprDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in ParmVarDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in VarTemplateSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in VarTemplatePartialSpecializationDecl (decl_info , named_decl_info , qual_type , var_decl_info)
| EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in EnumConstantDecl (decl_info , named_decl_info , qual_type , enum_constant_decl_info)
| IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in IndirectFieldDecl (decl_info , named_decl_info , qual_type , decl_ref_list)
| OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in OMPDeclareReductionDecl (decl_info , named_decl_info , qual_type)
| UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type) -> let (decl_info , named_decl_info) = __f (decl_info , named_decl_info) in UnresolvedUsingValueDecl (decl_info , named_decl_info , qual_type)
| x -> x
let get_type_decl_tuple = function
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> Some (decl_info , named_decl_info , opt_type , type_ptr)
| _ -> None
let update_type_decl_tuple __f = function
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in TemplateTypeParmDecl (decl_info , named_decl_info , opt_type , type_ptr)
| ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in ObjCTypeParamDecl (decl_info , named_decl_info , opt_type , type_ptr)
| TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in TypeAliasDecl (decl_info , named_decl_info , opt_type , type_ptr)
| TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in TypedefDecl (decl_info , named_decl_info , opt_type , type_ptr , typedef_decl_info)
| UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr) -> let (decl_info , named_decl_info , opt_type , type_ptr) = __f (decl_info , named_decl_info , opt_type , type_ptr) in UnresolvedUsingTypenameDecl (decl_info , named_decl_info , opt_type , type_ptr)
| x -> x
let get_tag_decl_tuple = function
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> Some (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> Some (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info)
| _ -> None
let update_tag_decl_tuple __f = function
| EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) = __f (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) in EnumDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , enum_decl_info)
| RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) = __f (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) in RecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info)
| CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info) -> let (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) = __f (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) in CXXRecordDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info)
| ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) = __f (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) in ClassTemplateSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list) -> let (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) = __f (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info) in ClassTemplatePartialSpecializationDecl (decl_info , named_decl_info , opt_type , type_ptr , decl_list , decl_context_info , record_decl_info , cxx_record_decl_info , template_instantiation_arg_info_list)
| x -> x
let get_stmt_kind_string = function
| GCCAsmStmt (stmt_info , stmt_list) -> "GCCAsmStmt"
| MSAsmStmt (stmt_info , stmt_list) -> "MSAsmStmt"
| AttributedStmt (stmt_info , stmt_list , attribute_list) -> "AttributedStmt"
| BreakStmt (stmt_info , stmt_list) -> "BreakStmt"
| CXXCatchStmt (stmt_info , stmt_list , cxx_catch_stmt_info) -> "CXXCatchStmt"
| CXXForRangeStmt (stmt_info , stmt_list) -> "CXXForRangeStmt"
| CXXTryStmt (stmt_info , stmt_list) -> "CXXTryStmt"
| CapturedStmt (stmt_info , stmt_list) -> "CapturedStmt"
| CompoundStmt (stmt_info , stmt_list) -> "CompoundStmt"
| ContinueStmt (stmt_info , stmt_list) -> "ContinueStmt"
| CoreturnStmt (stmt_info , stmt_list) -> "CoreturnStmt"
| CoroutineBodyStmt (stmt_info , stmt_list) -> "CoroutineBodyStmt"
| DeclStmt (stmt_info , stmt_list , decl_list) -> "DeclStmt"
| DoStmt (stmt_info , stmt_list) -> "DoStmt"
| BinaryConditionalOperator (stmt_info , stmt_list , expr_info) -> "BinaryConditionalOperator"
| ConditionalOperator (stmt_info , stmt_list , expr_info) -> "ConditionalOperator"
| AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info) -> "AddrLabelExpr"
| ArraySubscriptExpr (stmt_info , stmt_list , expr_info) -> "ArraySubscriptExpr"
| ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info) -> "ArrayTypeTraitExpr"
| AsTypeExpr (stmt_info , stmt_list , expr_info) -> "AsTypeExpr"
| AtomicExpr (stmt_info , stmt_list , expr_info) -> "AtomicExpr"
| BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info) -> "BinaryOperator"
| CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info) -> "CompoundAssignOperator"
| BlockExpr (stmt_info , stmt_list , expr_info , decl) -> "BlockExpr"
| CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info) -> "CXXBindTemporaryExpr"
| CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> "CXXBoolLiteralExpr"
| CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> "CXXConstructExpr"
| CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> "CXXTemporaryObjectExpr"
| CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> "CXXDefaultArgExpr"
| CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> "CXXDefaultInitExpr"
| CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info) -> "CXXDeleteExpr"
| CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info) -> "CXXDependentScopeMemberExpr"
| CXXFoldExpr (stmt_info , stmt_list , expr_info) -> "CXXFoldExpr"
| CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info) -> "CXXInheritedCtorInitExpr"
| CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info) -> "CXXNewExpr"
| CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info) -> "CXXNoexceptExpr"
| CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info) -> "CXXNullPtrLiteralExpr"
| CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info) -> "CXXPseudoDestructorExpr"
| CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info) -> "CXXScalarValueInitExpr"
| CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info) -> "CXXStdInitializerListExpr"
| CXXThisExpr (stmt_info , stmt_list , expr_info) -> "CXXThisExpr"
| CXXThrowExpr (stmt_info , stmt_list , expr_info) -> "CXXThrowExpr"
| CXXTypeidExpr (stmt_info , stmt_list , expr_info) -> "CXXTypeidExpr"
| CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info) -> "CXXUnresolvedConstructExpr"
| CXXUuidofExpr (stmt_info , stmt_list , expr_info) -> "CXXUuidofExpr"
| CallExpr (stmt_info , stmt_list , expr_info) -> "CallExpr"
| CUDAKernelCallExpr (stmt_info , stmt_list , expr_info) -> "CUDAKernelCallExpr"
| CXXMemberCallExpr (stmt_info , stmt_list , expr_info) -> "CXXMemberCallExpr"
| CXXOperatorCallExpr (stmt_info , stmt_list , expr_info) -> "CXXOperatorCallExpr"
| UserDefinedLiteral (stmt_info , stmt_list , expr_info) -> "UserDefinedLiteral"
| CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> "CStyleCastExpr"
| CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> "CXXFunctionalCastExpr"
| CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> "CXXConstCastExpr"
| CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> "CXXDynamicCastExpr"
| CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> "CXXReinterpretCastExpr"
| CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> "CXXStaticCastExpr"
| ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> "ObjCBridgedCastExpr"
| ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info) -> "ImplicitCastExpr"
| CharacterLiteral (stmt_info , stmt_list , expr_info , int) -> "CharacterLiteral"
| ChooseExpr (stmt_info , stmt_list , expr_info) -> "ChooseExpr"
| CompoundLiteralExpr (stmt_info , stmt_list , expr_info) -> "CompoundLiteralExpr"
| ConvertVectorExpr (stmt_info , stmt_list , expr_info) -> "ConvertVectorExpr"
| CoawaitExpr (stmt_info , stmt_list , expr_info) -> "CoawaitExpr"
| CoyieldExpr (stmt_info , stmt_list , expr_info) -> "CoyieldExpr"
| DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info) -> "DeclRefExpr"
| DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info) -> "DependentScopeDeclRefExpr"
| DesignatedInitExpr (stmt_info , stmt_list , expr_info) -> "DesignatedInitExpr"
| DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info) -> "DesignatedInitUpdateExpr"
| ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info) -> "ExprWithCleanups"
| ExpressionTraitExpr (stmt_info , stmt_list , expr_info) -> "ExpressionTraitExpr"
| ExtVectorElementExpr (stmt_info , stmt_list , expr_info) -> "ExtVectorElementExpr"
| FloatingLiteral (stmt_info , stmt_list , expr_info , string) -> "FloatingLiteral"
| FunctionParmPackExpr (stmt_info , stmt_list , expr_info) -> "FunctionParmPackExpr"
| GNUNullExpr (stmt_info , stmt_list , expr_info) -> "GNUNullExpr"
| GenericSelectionExpr (stmt_info , stmt_list , expr_info) -> "GenericSelectionExpr"
| ImaginaryLiteral (stmt_info , stmt_list , expr_info) -> "ImaginaryLiteral"
| ImplicitValueInitExpr (stmt_info , stmt_list , expr_info) -> "ImplicitValueInitExpr"
| InitListExpr (stmt_info , stmt_list , expr_info) -> "InitListExpr"
| IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info) -> "IntegerLiteral"
| LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info) -> "LambdaExpr"
| MSPropertyRefExpr (stmt_info , stmt_list , expr_info) -> "MSPropertyRefExpr"
| MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info) -> "MSPropertySubscriptExpr"
| MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info) -> "MaterializeTemporaryExpr"
| MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info) -> "MemberExpr"
| NoInitExpr (stmt_info , stmt_list , expr_info) -> "NoInitExpr"
| OMPArraySectionExpr (stmt_info , stmt_list , expr_info) -> "OMPArraySectionExpr"
| ObjCArrayLiteral (stmt_info , stmt_list , expr_info) -> "ObjCArrayLiteral"
| ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info) -> "ObjCAvailabilityCheckExpr"
| ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> "ObjCBoolLiteralExpr"
| ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info) -> "ObjCBoxedExpr"
| ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info) -> "ObjCDictionaryLiteral"
| ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info) -> "ObjCEncodeExpr"
| ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info) -> "ObjCIndirectCopyRestoreExpr"
| ObjCIsaExpr (stmt_info , stmt_list , expr_info) -> "ObjCIsaExpr"
| ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info) -> "ObjCIvarRefExpr"
| ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info) -> "ObjCMessageExpr"
| ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info) -> "ObjCPropertyRefExpr"
| ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref) -> "ObjCProtocolExpr"
| ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector) -> "ObjCSelectorExpr"
| ObjCStringLiteral (stmt_info , stmt_list , expr_info) -> "ObjCStringLiteral"
| ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info) -> "ObjCSubscriptRefExpr"
| OffsetOfExpr (stmt_info , stmt_list , expr_info) -> "OffsetOfExpr"
| OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info) -> "OpaqueValueExpr"
| UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info) -> "UnresolvedLookupExpr"
| UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info) -> "UnresolvedMemberExpr"
| PackExpansionExpr (stmt_info , stmt_list , expr_info) -> "PackExpansionExpr"
| ParenExpr (stmt_info , stmt_list , expr_info) -> "ParenExpr"
| ParenListExpr (stmt_info , stmt_list , expr_info) -> "ParenListExpr"
| PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type) -> "PredefinedExpr"
| PseudoObjectExpr (stmt_info , stmt_list , expr_info) -> "PseudoObjectExpr"
| ShuffleVectorExpr (stmt_info , stmt_list , expr_info) -> "ShuffleVectorExpr"
| SizeOfPackExpr (stmt_info , stmt_list , expr_info) -> "SizeOfPackExpr"
| StmtExpr (stmt_info , stmt_list , expr_info) -> "StmtExpr"
| StringLiteral (stmt_info , stmt_list , expr_info , string) -> "StringLiteral"
| SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info) -> "SubstNonTypeTemplateParmExpr"
| SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info) -> "SubstNonTypeTemplateParmPackExpr"
| TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info) -> "TypeTraitExpr"
| TypoExpr (stmt_info , stmt_list , expr_info) -> "TypoExpr"
| UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info) -> "UnaryExprOrTypeTraitExpr"
| UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info) -> "UnaryOperator"
| VAArgExpr (stmt_info , stmt_list , expr_info) -> "VAArgExpr"
| ForStmt (stmt_info , stmt_list) -> "ForStmt"
| GotoStmt (stmt_info , stmt_list , goto_stmt_info) -> "GotoStmt"
| IfStmt (stmt_info , stmt_list) -> "IfStmt"
| IndirectGotoStmt (stmt_info , stmt_list) -> "IndirectGotoStmt"
| LabelStmt (stmt_info , stmt_list , string) -> "LabelStmt"
| MSDependentExistsStmt (stmt_info , stmt_list) -> "MSDependentExistsStmt"
| NullStmt (stmt_info , stmt_list) -> "NullStmt"
| OMPAtomicDirective (stmt_info , stmt_list) -> "OMPAtomicDirective"
| OMPBarrierDirective (stmt_info , stmt_list) -> "OMPBarrierDirective"
| OMPCancelDirective (stmt_info , stmt_list) -> "OMPCancelDirective"
| OMPCancellationPointDirective (stmt_info , stmt_list) -> "OMPCancellationPointDirective"
| OMPCriticalDirective (stmt_info , stmt_list) -> "OMPCriticalDirective"
| OMPFlushDirective (stmt_info , stmt_list) -> "OMPFlushDirective"
| OMPDistributeDirective (stmt_info , stmt_list) -> "OMPDistributeDirective"
| OMPDistributeParallelForDirective (stmt_info , stmt_list) -> "OMPDistributeParallelForDirective"
| OMPDistributeParallelForSimdDirective (stmt_info , stmt_list) -> "OMPDistributeParallelForSimdDirective"
| OMPDistributeSimdDirective (stmt_info , stmt_list) -> "OMPDistributeSimdDirective"
| OMPForDirective (stmt_info , stmt_list) -> "OMPForDirective"
| OMPForSimdDirective (stmt_info , stmt_list) -> "OMPForSimdDirective"
| OMPParallelForDirective (stmt_info , stmt_list) -> "OMPParallelForDirective"
| OMPParallelForSimdDirective (stmt_info , stmt_list) -> "OMPParallelForSimdDirective"
| OMPSimdDirective (stmt_info , stmt_list) -> "OMPSimdDirective"
| OMPTargetParallelForSimdDirective (stmt_info , stmt_list) -> "OMPTargetParallelForSimdDirective"
| OMPTargetSimdDirective (stmt_info , stmt_list) -> "OMPTargetSimdDirective"
| OMPTaskLoopDirective (stmt_info , stmt_list) -> "OMPTaskLoopDirective"
| OMPTaskLoopSimdDirective (stmt_info , stmt_list) -> "OMPTaskLoopSimdDirective"
| OMPMasterDirective (stmt_info , stmt_list) -> "OMPMasterDirective"
| OMPOrderedDirective (stmt_info , stmt_list) -> "OMPOrderedDirective"
| OMPParallelDirective (stmt_info , stmt_list) -> "OMPParallelDirective"
| OMPParallelSectionsDirective (stmt_info , stmt_list) -> "OMPParallelSectionsDirective"
| OMPSectionDirective (stmt_info , stmt_list) -> "OMPSectionDirective"
| OMPSectionsDirective (stmt_info , stmt_list) -> "OMPSectionsDirective"
| OMPSingleDirective (stmt_info , stmt_list) -> "OMPSingleDirective"
| OMPTargetDataDirective (stmt_info , stmt_list) -> "OMPTargetDataDirective"
| OMPTargetDirective (stmt_info , stmt_list) -> "OMPTargetDirective"
| OMPTargetEnterDataDirective (stmt_info , stmt_list) -> "OMPTargetEnterDataDirective"
| OMPTargetExitDataDirective (stmt_info , stmt_list) -> "OMPTargetExitDataDirective"
| OMPTargetParallelDirective (stmt_info , stmt_list) -> "OMPTargetParallelDirective"
| OMPTargetParallelForDirective (stmt_info , stmt_list) -> "OMPTargetParallelForDirective"
| OMPTargetUpdateDirective (stmt_info , stmt_list) -> "OMPTargetUpdateDirective"
| OMPTaskDirective (stmt_info , stmt_list) -> "OMPTaskDirective"
| OMPTaskgroupDirective (stmt_info , stmt_list) -> "OMPTaskgroupDirective"
| OMPTaskwaitDirective (stmt_info , stmt_list) -> "OMPTaskwaitDirective"
| OMPTaskyieldDirective (stmt_info , stmt_list) -> "OMPTaskyieldDirective"
| OMPTeamsDirective (stmt_info , stmt_list) -> "OMPTeamsDirective"
| ObjCAtCatchStmt (stmt_info , stmt_list , obj_c_message_expr_kind) -> "ObjCAtCatchStmt"
| ObjCAtFinallyStmt (stmt_info , stmt_list) -> "ObjCAtFinallyStmt"
| ObjCAtSynchronizedStmt (stmt_info , stmt_list) -> "ObjCAtSynchronizedStmt"
| ObjCAtThrowStmt (stmt_info , stmt_list) -> "ObjCAtThrowStmt"
| ObjCAtTryStmt (stmt_info , stmt_list) -> "ObjCAtTryStmt"
| ObjCAutoreleasePoolStmt (stmt_info , stmt_list) -> "ObjCAutoreleasePoolStmt"
| ObjCForCollectionStmt (stmt_info , stmt_list) -> "ObjCForCollectionStmt"
| ReturnStmt (stmt_info , stmt_list) -> "ReturnStmt"
| SEHExceptStmt (stmt_info , stmt_list) -> "SEHExceptStmt"
| SEHFinallyStmt (stmt_info , stmt_list) -> "SEHFinallyStmt"
| SEHLeaveStmt (stmt_info , stmt_list) -> "SEHLeaveStmt"
| SEHTryStmt (stmt_info , stmt_list) -> "SEHTryStmt"
| CaseStmt (stmt_info , stmt_list) -> "CaseStmt"
| DefaultStmt (stmt_info , stmt_list) -> "DefaultStmt"
| SwitchStmt (stmt_info , stmt_list) -> "SwitchStmt"
| WhileStmt (stmt_info , stmt_list) -> "WhileStmt"
let get_stmt_tuple = function
| GCCAsmStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| MSAsmStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| AttributedStmt (stmt_info , stmt_list , attribute_list) -> (stmt_info , stmt_list)
| BreakStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CXXCatchStmt (stmt_info , stmt_list , cxx_catch_stmt_info) -> (stmt_info , stmt_list)
| CXXForRangeStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CXXTryStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CapturedStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CompoundStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ContinueStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CoreturnStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CoroutineBodyStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| DeclStmt (stmt_info , stmt_list , decl_list) -> (stmt_info , stmt_list)
| DoStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| BinaryConditionalOperator (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ConditionalOperator (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info) -> (stmt_info , stmt_list)
| ArraySubscriptExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| AsTypeExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| AtomicExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info) -> (stmt_info , stmt_list)
| CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info) -> (stmt_info , stmt_list)
| BlockExpr (stmt_info , stmt_list , expr_info , decl) -> (stmt_info , stmt_list)
| CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info) -> (stmt_info , stmt_list)
| CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> (stmt_info , stmt_list)
| CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> (stmt_info , stmt_list)
| CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> (stmt_info , stmt_list)
| CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> (stmt_info , stmt_list)
| CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> (stmt_info , stmt_list)
| CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info) -> (stmt_info , stmt_list)
| CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXFoldExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info) -> (stmt_info , stmt_list)
| CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info) -> (stmt_info , stmt_list)
| CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXThisExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXThrowExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXTypeidExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXUuidofExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CallExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CUDAKernelCallExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXMemberCallExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CXXOperatorCallExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| UserDefinedLiteral (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> (stmt_info , stmt_list)
| CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> (stmt_info , stmt_list)
| CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> (stmt_info , stmt_list)
| CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> (stmt_info , stmt_list)
| CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> (stmt_info , stmt_list)
| CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> (stmt_info , stmt_list)
| ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> (stmt_info , stmt_list)
| ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info) -> (stmt_info , stmt_list)
| CharacterLiteral (stmt_info , stmt_list , expr_info , int) -> (stmt_info , stmt_list)
| ChooseExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CompoundLiteralExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ConvertVectorExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CoawaitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| CoyieldExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info) -> (stmt_info , stmt_list)
| DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| DesignatedInitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info) -> (stmt_info , stmt_list)
| ExpressionTraitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ExtVectorElementExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| FloatingLiteral (stmt_info , stmt_list , expr_info , string) -> (stmt_info , stmt_list)
| FunctionParmPackExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| GNUNullExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| GenericSelectionExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ImaginaryLiteral (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ImplicitValueInitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| InitListExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info) -> (stmt_info , stmt_list)
| LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info) -> (stmt_info , stmt_list)
| MSPropertyRefExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info) -> (stmt_info , stmt_list)
| MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info) -> (stmt_info , stmt_list)
| NoInitExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| OMPArraySectionExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCArrayLiteral (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> (stmt_info , stmt_list)
| ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info) -> (stmt_info , stmt_list)
| ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info) -> (stmt_info , stmt_list)
| ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCIsaExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info) -> (stmt_info , stmt_list)
| ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info) -> (stmt_info , stmt_list)
| ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info) -> (stmt_info , stmt_list)
| ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref) -> (stmt_info , stmt_list)
| ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector) -> (stmt_info , stmt_list)
| ObjCStringLiteral (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info) -> (stmt_info , stmt_list)
| OffsetOfExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info) -> (stmt_info , stmt_list)
| UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info) -> (stmt_info , stmt_list)
| UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info) -> (stmt_info , stmt_list)
| PackExpansionExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ParenExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ParenListExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type) -> (stmt_info , stmt_list)
| PseudoObjectExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ShuffleVectorExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| SizeOfPackExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| StmtExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| StringLiteral (stmt_info , stmt_list , expr_info , string) -> (stmt_info , stmt_list)
| SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info) -> (stmt_info , stmt_list)
| TypoExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info) -> (stmt_info , stmt_list)
| UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info) -> (stmt_info , stmt_list)
| VAArgExpr (stmt_info , stmt_list , expr_info) -> (stmt_info , stmt_list)
| ForStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| GotoStmt (stmt_info , stmt_list , goto_stmt_info) -> (stmt_info , stmt_list)
| IfStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| IndirectGotoStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| LabelStmt (stmt_info , stmt_list , string) -> (stmt_info , stmt_list)
| MSDependentExistsStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| NullStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPAtomicDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPBarrierDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPCancelDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPCancellationPointDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPCriticalDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPFlushDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPDistributeDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPDistributeParallelForDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPDistributeParallelForSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPDistributeSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPForDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPForSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPParallelForDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPParallelForSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetParallelForSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTaskLoopDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTaskLoopSimdDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPMasterDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPOrderedDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPParallelDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPParallelSectionsDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPSectionDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPSectionsDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPSingleDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetDataDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetEnterDataDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetExitDataDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetParallelDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetParallelForDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTargetUpdateDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTaskDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTaskgroupDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTaskwaitDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTaskyieldDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| OMPTeamsDirective (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ObjCAtCatchStmt (stmt_info , stmt_list , obj_c_message_expr_kind) -> (stmt_info , stmt_list)
| ObjCAtFinallyStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ObjCAtSynchronizedStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ObjCAtThrowStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ObjCAtTryStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ObjCAutoreleasePoolStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ObjCForCollectionStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| ReturnStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| SEHExceptStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| SEHFinallyStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| SEHLeaveStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| SEHTryStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| CaseStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| DefaultStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| SwitchStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
| WhileStmt (stmt_info , stmt_list) -> (stmt_info , stmt_list)
let update_stmt_tuple __f = function
| GCCAsmStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in GCCAsmStmt (stmt_info , stmt_list)
| MSAsmStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in MSAsmStmt (stmt_info , stmt_list)
| AttributedStmt (stmt_info , stmt_list , attribute_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in AttributedStmt (stmt_info , stmt_list , attribute_list)
| BreakStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in BreakStmt (stmt_info , stmt_list)
| CXXCatchStmt (stmt_info , stmt_list , cxx_catch_stmt_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXCatchStmt (stmt_info , stmt_list , cxx_catch_stmt_info)
| CXXForRangeStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXForRangeStmt (stmt_info , stmt_list)
| CXXTryStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXTryStmt (stmt_info , stmt_list)
| CapturedStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CapturedStmt (stmt_info , stmt_list)
| CompoundStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CompoundStmt (stmt_info , stmt_list)
| ContinueStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ContinueStmt (stmt_info , stmt_list)
| CoreturnStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CoreturnStmt (stmt_info , stmt_list)
| CoroutineBodyStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CoroutineBodyStmt (stmt_info , stmt_list)
| DeclStmt (stmt_info , stmt_list , decl_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DeclStmt (stmt_info , stmt_list , decl_list)
| DoStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DoStmt (stmt_info , stmt_list)
| BinaryConditionalOperator (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in BinaryConditionalOperator (stmt_info , stmt_list , expr_info)
| ConditionalOperator (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ConditionalOperator (stmt_info , stmt_list , expr_info)
| AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info)
| ArraySubscriptExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ArraySubscriptExpr (stmt_info , stmt_list , expr_info)
| ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info)
| AsTypeExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in AsTypeExpr (stmt_info , stmt_list , expr_info)
| AtomicExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in AtomicExpr (stmt_info , stmt_list , expr_info)
| BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info)
| CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info)
| BlockExpr (stmt_info , stmt_list , expr_info , decl) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in BlockExpr (stmt_info , stmt_list , expr_info , decl)
| CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info)
| CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int)
| CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info)
| CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info)
| CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info)
| CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info)
| CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info)
| CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info)
| CXXFoldExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXFoldExpr (stmt_info , stmt_list , expr_info)
| CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info)
| CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info)
| CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info)
| CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info)
| CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info)
| CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info)
| CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info)
| CXXThisExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXThisExpr (stmt_info , stmt_list , expr_info)
| CXXThrowExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXThrowExpr (stmt_info , stmt_list , expr_info)
| CXXTypeidExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXTypeidExpr (stmt_info , stmt_list , expr_info)
| CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info)
| CXXUuidofExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXUuidofExpr (stmt_info , stmt_list , expr_info)
| CallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CallExpr (stmt_info , stmt_list , expr_info)
| CUDAKernelCallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CUDAKernelCallExpr (stmt_info , stmt_list , expr_info)
| CXXMemberCallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXMemberCallExpr (stmt_info , stmt_list , expr_info)
| CXXOperatorCallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXOperatorCallExpr (stmt_info , stmt_list , expr_info)
| UserDefinedLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in UserDefinedLiteral (stmt_info , stmt_list , expr_info)
| CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr)
| CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr)
| CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr)
| ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info)
| CharacterLiteral (stmt_info , stmt_list , expr_info , int) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CharacterLiteral (stmt_info , stmt_list , expr_info , int)
| ChooseExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ChooseExpr (stmt_info , stmt_list , expr_info)
| CompoundLiteralExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CompoundLiteralExpr (stmt_info , stmt_list , expr_info)
| ConvertVectorExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ConvertVectorExpr (stmt_info , stmt_list , expr_info)
| CoawaitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CoawaitExpr (stmt_info , stmt_list , expr_info)
| CoyieldExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CoyieldExpr (stmt_info , stmt_list , expr_info)
| DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info)
| DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info)
| DesignatedInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DesignatedInitExpr (stmt_info , stmt_list , expr_info)
| DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info)
| ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info)
| ExpressionTraitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ExpressionTraitExpr (stmt_info , stmt_list , expr_info)
| ExtVectorElementExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ExtVectorElementExpr (stmt_info , stmt_list , expr_info)
| FloatingLiteral (stmt_info , stmt_list , expr_info , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in FloatingLiteral (stmt_info , stmt_list , expr_info , string)
| FunctionParmPackExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in FunctionParmPackExpr (stmt_info , stmt_list , expr_info)
| GNUNullExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in GNUNullExpr (stmt_info , stmt_list , expr_info)
| GenericSelectionExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in GenericSelectionExpr (stmt_info , stmt_list , expr_info)
| ImaginaryLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ImaginaryLiteral (stmt_info , stmt_list , expr_info)
| ImplicitValueInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ImplicitValueInitExpr (stmt_info , stmt_list , expr_info)
| InitListExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in InitListExpr (stmt_info , stmt_list , expr_info)
| IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info)
| LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info)
| MSPropertyRefExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in MSPropertyRefExpr (stmt_info , stmt_list , expr_info)
| MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info)
| MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info)
| MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info)
| NoInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in NoInitExpr (stmt_info , stmt_list , expr_info)
| OMPArraySectionExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPArraySectionExpr (stmt_info , stmt_list , expr_info)
| ObjCArrayLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCArrayLiteral (stmt_info , stmt_list , expr_info)
| ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info)
| ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int)
| ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info)
| ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info)
| ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info)
| ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info)
| ObjCIsaExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCIsaExpr (stmt_info , stmt_list , expr_info)
| ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info)
| ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info)
| ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info)
| ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref)
| ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector)
| ObjCStringLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCStringLiteral (stmt_info , stmt_list , expr_info)
| ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info)
| OffsetOfExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OffsetOfExpr (stmt_info , stmt_list , expr_info)
| OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info)
| UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info)
| UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info)
| PackExpansionExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in PackExpansionExpr (stmt_info , stmt_list , expr_info)
| ParenExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ParenExpr (stmt_info , stmt_list , expr_info)
| ParenListExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ParenListExpr (stmt_info , stmt_list , expr_info)
| PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type)
| PseudoObjectExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in PseudoObjectExpr (stmt_info , stmt_list , expr_info)
| ShuffleVectorExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ShuffleVectorExpr (stmt_info , stmt_list , expr_info)
| SizeOfPackExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SizeOfPackExpr (stmt_info , stmt_list , expr_info)
| StmtExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in StmtExpr (stmt_info , stmt_list , expr_info)
| StringLiteral (stmt_info , stmt_list , expr_info , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in StringLiteral (stmt_info , stmt_list , expr_info , string)
| SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info)
| SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info)
| TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info)
| TypoExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in TypoExpr (stmt_info , stmt_list , expr_info)
| UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info)
| UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info)
| VAArgExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in VAArgExpr (stmt_info , stmt_list , expr_info)
| ForStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ForStmt (stmt_info , stmt_list)
| GotoStmt (stmt_info , stmt_list , goto_stmt_info) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in GotoStmt (stmt_info , stmt_list , goto_stmt_info)
| IfStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in IfStmt (stmt_info , stmt_list)
| IndirectGotoStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in IndirectGotoStmt (stmt_info , stmt_list)
| LabelStmt (stmt_info , stmt_list , string) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in LabelStmt (stmt_info , stmt_list , string)
| MSDependentExistsStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in MSDependentExistsStmt (stmt_info , stmt_list)
| NullStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in NullStmt (stmt_info , stmt_list)
| OMPAtomicDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPAtomicDirective (stmt_info , stmt_list)
| OMPBarrierDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPBarrierDirective (stmt_info , stmt_list)
| OMPCancelDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPCancelDirective (stmt_info , stmt_list)
| OMPCancellationPointDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPCancellationPointDirective (stmt_info , stmt_list)
| OMPCriticalDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPCriticalDirective (stmt_info , stmt_list)
| OMPFlushDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPFlushDirective (stmt_info , stmt_list)
| OMPDistributeDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPDistributeDirective (stmt_info , stmt_list)
| OMPDistributeParallelForDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPDistributeParallelForDirective (stmt_info , stmt_list)
| OMPDistributeParallelForSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPDistributeParallelForSimdDirective (stmt_info , stmt_list)
| OMPDistributeSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPDistributeSimdDirective (stmt_info , stmt_list)
| OMPForDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPForDirective (stmt_info , stmt_list)
| OMPForSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPForSimdDirective (stmt_info , stmt_list)
| OMPParallelForDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPParallelForDirective (stmt_info , stmt_list)
| OMPParallelForSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPParallelForSimdDirective (stmt_info , stmt_list)
| OMPSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPSimdDirective (stmt_info , stmt_list)
| OMPTargetParallelForSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetParallelForSimdDirective (stmt_info , stmt_list)
| OMPTargetSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetSimdDirective (stmt_info , stmt_list)
| OMPTaskLoopDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTaskLoopDirective (stmt_info , stmt_list)
| OMPTaskLoopSimdDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTaskLoopSimdDirective (stmt_info , stmt_list)
| OMPMasterDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPMasterDirective (stmt_info , stmt_list)
| OMPOrderedDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPOrderedDirective (stmt_info , stmt_list)
| OMPParallelDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPParallelDirective (stmt_info , stmt_list)
| OMPParallelSectionsDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPParallelSectionsDirective (stmt_info , stmt_list)
| OMPSectionDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPSectionDirective (stmt_info , stmt_list)
| OMPSectionsDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPSectionsDirective (stmt_info , stmt_list)
| OMPSingleDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPSingleDirective (stmt_info , stmt_list)
| OMPTargetDataDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetDataDirective (stmt_info , stmt_list)
| OMPTargetDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetDirective (stmt_info , stmt_list)
| OMPTargetEnterDataDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetEnterDataDirective (stmt_info , stmt_list)
| OMPTargetExitDataDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetExitDataDirective (stmt_info , stmt_list)
| OMPTargetParallelDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetParallelDirective (stmt_info , stmt_list)
| OMPTargetParallelForDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetParallelForDirective (stmt_info , stmt_list)
| OMPTargetUpdateDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTargetUpdateDirective (stmt_info , stmt_list)
| OMPTaskDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTaskDirective (stmt_info , stmt_list)
| OMPTaskgroupDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTaskgroupDirective (stmt_info , stmt_list)
| OMPTaskwaitDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTaskwaitDirective (stmt_info , stmt_list)
| OMPTaskyieldDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTaskyieldDirective (stmt_info , stmt_list)
| OMPTeamsDirective (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in OMPTeamsDirective (stmt_info , stmt_list)
| ObjCAtCatchStmt (stmt_info , stmt_list , obj_c_message_expr_kind) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAtCatchStmt (stmt_info , stmt_list , obj_c_message_expr_kind)
| ObjCAtFinallyStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAtFinallyStmt (stmt_info , stmt_list)
| ObjCAtSynchronizedStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAtSynchronizedStmt (stmt_info , stmt_list)
| ObjCAtThrowStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAtThrowStmt (stmt_info , stmt_list)
| ObjCAtTryStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAtTryStmt (stmt_info , stmt_list)
| ObjCAutoreleasePoolStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCAutoreleasePoolStmt (stmt_info , stmt_list)
| ObjCForCollectionStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ObjCForCollectionStmt (stmt_info , stmt_list)
| ReturnStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in ReturnStmt (stmt_info , stmt_list)
| SEHExceptStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SEHExceptStmt (stmt_info , stmt_list)
| SEHFinallyStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SEHFinallyStmt (stmt_info , stmt_list)
| SEHLeaveStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SEHLeaveStmt (stmt_info , stmt_list)
| SEHTryStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SEHTryStmt (stmt_info , stmt_list)
| CaseStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in CaseStmt (stmt_info , stmt_list)
| DefaultStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in DefaultStmt (stmt_info , stmt_list)
| SwitchStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in SwitchStmt (stmt_info , stmt_list)
| WhileStmt (stmt_info , stmt_list) -> let (stmt_info , stmt_list) = __f (stmt_info , stmt_list) in WhileStmt (stmt_info , stmt_list)
let get_expr_tuple = function
| BinaryConditionalOperator (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ConditionalOperator (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ArraySubscriptExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| AsTypeExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| AtomicExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info) -> Some (stmt_info , stmt_list , expr_info)
| CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info) -> Some (stmt_info , stmt_list , expr_info)
| BlockExpr (stmt_info , stmt_list , expr_info , decl) -> Some (stmt_info , stmt_list , expr_info)
| CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> Some (stmt_info , stmt_list , expr_info)
| CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXFoldExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXThisExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXThrowExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXTypeidExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXUuidofExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CallExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CUDAKernelCallExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXMemberCallExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CXXOperatorCallExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| UserDefinedLiteral (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> Some (stmt_info , stmt_list , expr_info)
| CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> Some (stmt_info , stmt_list , expr_info)
| CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> Some (stmt_info , stmt_list , expr_info)
| CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> Some (stmt_info , stmt_list , expr_info)
| CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> Some (stmt_info , stmt_list , expr_info)
| CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> Some (stmt_info , stmt_list , expr_info)
| ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> Some (stmt_info , stmt_list , expr_info)
| ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CharacterLiteral (stmt_info , stmt_list , expr_info , int) -> Some (stmt_info , stmt_list , expr_info)
| ChooseExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CompoundLiteralExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ConvertVectorExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CoawaitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| CoyieldExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| DesignatedInitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info) -> Some (stmt_info , stmt_list , expr_info)
| ExpressionTraitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ExtVectorElementExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| FloatingLiteral (stmt_info , stmt_list , expr_info , string) -> Some (stmt_info , stmt_list , expr_info)
| FunctionParmPackExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| GNUNullExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| GenericSelectionExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ImaginaryLiteral (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ImplicitValueInitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| InitListExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info) -> Some (stmt_info , stmt_list , expr_info)
| LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| MSPropertyRefExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| NoInitExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| OMPArraySectionExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCArrayLiteral (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> Some (stmt_info , stmt_list , expr_info)
| ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCIsaExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref) -> Some (stmt_info , stmt_list , expr_info)
| ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector) -> Some (stmt_info , stmt_list , expr_info)
| ObjCStringLiteral (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| OffsetOfExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| PackExpansionExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ParenExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ParenListExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type) -> Some (stmt_info , stmt_list , expr_info)
| PseudoObjectExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| ShuffleVectorExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| SizeOfPackExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| StmtExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| StringLiteral (stmt_info , stmt_list , expr_info , string) -> Some (stmt_info , stmt_list , expr_info)
| SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info) -> Some (stmt_info , stmt_list , expr_info)
| TypoExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info) -> Some (stmt_info , stmt_list , expr_info)
| UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info) -> Some (stmt_info , stmt_list , expr_info)
| VAArgExpr (stmt_info , stmt_list , expr_info) -> Some (stmt_info , stmt_list , expr_info)
| _ -> None
let update_expr_tuple __f = function
| BinaryConditionalOperator (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in BinaryConditionalOperator (stmt_info , stmt_list , expr_info)
| ConditionalOperator (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ConditionalOperator (stmt_info , stmt_list , expr_info)
| AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in AddrLabelExpr (stmt_info , stmt_list , expr_info , addr_label_expr_info)
| ArraySubscriptExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ArraySubscriptExpr (stmt_info , stmt_list , expr_info)
| ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ArrayTypeTraitExpr (stmt_info , stmt_list , expr_info)
| AsTypeExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in AsTypeExpr (stmt_info , stmt_list , expr_info)
| AtomicExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in AtomicExpr (stmt_info , stmt_list , expr_info)
| BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in BinaryOperator (stmt_info , stmt_list , expr_info , binary_operator_info)
| CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CompoundAssignOperator (stmt_info , stmt_list , expr_info , binary_operator_info , compound_assign_operator_info)
| BlockExpr (stmt_info , stmt_list , expr_info , decl) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in BlockExpr (stmt_info , stmt_list , expr_info , decl)
| CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXBindTemporaryExpr (stmt_info , stmt_list , expr_info , cxx_bind_temporary_expr_info)
| CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXBoolLiteralExpr (stmt_info , stmt_list , expr_info , int)
| CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXConstructExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info)
| CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXTemporaryObjectExpr (stmt_info , stmt_list , expr_info , cxx_construct_expr_info)
| CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXDefaultArgExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info)
| CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXDefaultInitExpr (stmt_info , stmt_list , expr_info , cxx_default_expr_info)
| CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXDeleteExpr (stmt_info , stmt_list , expr_info , cxx_delete_expr_info)
| CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXDependentScopeMemberExpr (stmt_info , stmt_list , expr_info)
| CXXFoldExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXFoldExpr (stmt_info , stmt_list , expr_info)
| CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXInheritedCtorInitExpr (stmt_info , stmt_list , expr_info)
| CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXNewExpr (stmt_info , stmt_list , expr_info , cxx_new_expr_info)
| CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXNoexceptExpr (stmt_info , stmt_list , expr_info , cxx_noexcept_expr_info)
| CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXNullPtrLiteralExpr (stmt_info , stmt_list , expr_info)
| CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXPseudoDestructorExpr (stmt_info , stmt_list , expr_info)
| CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXScalarValueInitExpr (stmt_info , stmt_list , expr_info)
| CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXStdInitializerListExpr (stmt_info , stmt_list , expr_info)
| CXXThisExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXThisExpr (stmt_info , stmt_list , expr_info)
| CXXThrowExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXThrowExpr (stmt_info , stmt_list , expr_info)
| CXXTypeidExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXTypeidExpr (stmt_info , stmt_list , expr_info)
| CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXUnresolvedConstructExpr (stmt_info , stmt_list , expr_info)
| CXXUuidofExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXUuidofExpr (stmt_info , stmt_list , expr_info)
| CallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CallExpr (stmt_info , stmt_list , expr_info)
| CUDAKernelCallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CUDAKernelCallExpr (stmt_info , stmt_list , expr_info)
| CXXMemberCallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXMemberCallExpr (stmt_info , stmt_list , expr_info)
| CXXOperatorCallExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXOperatorCallExpr (stmt_info , stmt_list , expr_info)
| UserDefinedLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in UserDefinedLiteral (stmt_info , stmt_list , expr_info)
| CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CStyleCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr)
| CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXFunctionalCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr)
| CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXConstCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXDynamicCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXReinterpretCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CXXStaticCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr , string)
| ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCBridgedCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info , type_ptr)
| ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ImplicitCastExpr (stmt_info , stmt_list , expr_info , cast_expr_info)
| CharacterLiteral (stmt_info , stmt_list , expr_info , int) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CharacterLiteral (stmt_info , stmt_list , expr_info , int)
| ChooseExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ChooseExpr (stmt_info , stmt_list , expr_info)
| CompoundLiteralExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CompoundLiteralExpr (stmt_info , stmt_list , expr_info)
| ConvertVectorExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ConvertVectorExpr (stmt_info , stmt_list , expr_info)
| CoawaitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CoawaitExpr (stmt_info , stmt_list , expr_info)
| CoyieldExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in CoyieldExpr (stmt_info , stmt_list , expr_info)
| DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in DeclRefExpr (stmt_info , stmt_list , expr_info , decl_ref_expr_info)
| DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in DependentScopeDeclRefExpr (stmt_info , stmt_list , expr_info)
| DesignatedInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in DesignatedInitExpr (stmt_info , stmt_list , expr_info)
| DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in DesignatedInitUpdateExpr (stmt_info , stmt_list , expr_info)
| ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ExprWithCleanups (stmt_info , stmt_list , expr_info , expr_with_cleanups_info)
| ExpressionTraitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ExpressionTraitExpr (stmt_info , stmt_list , expr_info)
| ExtVectorElementExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ExtVectorElementExpr (stmt_info , stmt_list , expr_info)
| FloatingLiteral (stmt_info , stmt_list , expr_info , string) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in FloatingLiteral (stmt_info , stmt_list , expr_info , string)
| FunctionParmPackExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in FunctionParmPackExpr (stmt_info , stmt_list , expr_info)
| GNUNullExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in GNUNullExpr (stmt_info , stmt_list , expr_info)
| GenericSelectionExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in GenericSelectionExpr (stmt_info , stmt_list , expr_info)
| ImaginaryLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ImaginaryLiteral (stmt_info , stmt_list , expr_info)
| ImplicitValueInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ImplicitValueInitExpr (stmt_info , stmt_list , expr_info)
| InitListExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in InitListExpr (stmt_info , stmt_list , expr_info)
| IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in IntegerLiteral (stmt_info , stmt_list , expr_info , integer_literal_info)
| LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in LambdaExpr (stmt_info , stmt_list , expr_info , lambda_expr_info)
| MSPropertyRefExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in MSPropertyRefExpr (stmt_info , stmt_list , expr_info)
| MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in MSPropertySubscriptExpr (stmt_info , stmt_list , expr_info)
| MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in MaterializeTemporaryExpr (stmt_info , stmt_list , expr_info , materialize_temporary_expr_info)
| MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in MemberExpr (stmt_info , stmt_list , expr_info , member_expr_info)
| NoInitExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in NoInitExpr (stmt_info , stmt_list , expr_info)
| OMPArraySectionExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in OMPArraySectionExpr (stmt_info , stmt_list , expr_info)
| ObjCArrayLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCArrayLiteral (stmt_info , stmt_list , expr_info)
| ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCAvailabilityCheckExpr (stmt_info , stmt_list , expr_info)
| ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCBoolLiteralExpr (stmt_info , stmt_list , expr_info , int)
| ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCBoxedExpr (stmt_info , stmt_list , expr_info , objc_boxed_expr_info)
| ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCDictionaryLiteral (stmt_info , stmt_list , expr_info)
| ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCEncodeExpr (stmt_info , stmt_list , expr_info , objc_encode_expr_info)
| ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCIndirectCopyRestoreExpr (stmt_info , stmt_list , expr_info)
| ObjCIsaExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCIsaExpr (stmt_info , stmt_list , expr_info)
| ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCIvarRefExpr (stmt_info , stmt_list , expr_info , obj_c_ivar_ref_expr_info)
| ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCMessageExpr (stmt_info , stmt_list , expr_info , obj_c_message_expr_info)
| ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCPropertyRefExpr (stmt_info , stmt_list , expr_info , obj_c_property_ref_expr_info)
| ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCProtocolExpr (stmt_info , stmt_list , expr_info , decl_ref)
| ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCSelectorExpr (stmt_info , stmt_list , expr_info , selector)
| ObjCStringLiteral (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCStringLiteral (stmt_info , stmt_list , expr_info)
| ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ObjCSubscriptRefExpr (stmt_info , stmt_list , expr_info , obj_c_subscript_ref_expr_info)
| OffsetOfExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in OffsetOfExpr (stmt_info , stmt_list , expr_info)
| OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in OpaqueValueExpr (stmt_info , stmt_list , expr_info , opaque_value_expr_info)
| UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in UnresolvedLookupExpr (stmt_info , stmt_list , expr_info , overload_expr_info , unresolved_lookup_expr_info)
| UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in UnresolvedMemberExpr (stmt_info , stmt_list , expr_info , overload_expr_info)
| PackExpansionExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in PackExpansionExpr (stmt_info , stmt_list , expr_info)
| ParenExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ParenExpr (stmt_info , stmt_list , expr_info)
| ParenListExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ParenListExpr (stmt_info , stmt_list , expr_info)
| PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in PredefinedExpr (stmt_info , stmt_list , expr_info , predefined_expr_type)
| PseudoObjectExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in PseudoObjectExpr (stmt_info , stmt_list , expr_info)
| ShuffleVectorExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in ShuffleVectorExpr (stmt_info , stmt_list , expr_info)
| SizeOfPackExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in SizeOfPackExpr (stmt_info , stmt_list , expr_info)
| StmtExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in StmtExpr (stmt_info , stmt_list , expr_info)
| StringLiteral (stmt_info , stmt_list , expr_info , string) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in StringLiteral (stmt_info , stmt_list , expr_info , string)
| SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in SubstNonTypeTemplateParmExpr (stmt_info , stmt_list , expr_info)
| SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in SubstNonTypeTemplateParmPackExpr (stmt_info , stmt_list , expr_info)
| TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in TypeTraitExpr (stmt_info , stmt_list , expr_info , type_trait_info)
| TypoExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in TypoExpr (stmt_info , stmt_list , expr_info)
| UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in UnaryExprOrTypeTraitExpr (stmt_info , stmt_list , expr_info , unary_expr_or_type_trait_expr_info)
| UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in UnaryOperator (stmt_info , stmt_list , expr_info , unary_operator_info)
| VAArgExpr (stmt_info , stmt_list , expr_info) -> let (stmt_info , stmt_list , expr_info) = __f (stmt_info , stmt_list , expr_info) in VAArgExpr (stmt_info , stmt_list , expr_info)
| x -> x
let get_type_tuple = function
| NoneType (type_info) -> (type_info) (* special case for nullptr type *)
| BuiltinType (type_info , builtin_type_kind) -> (type_info)
| ComplexType (type_info) -> (type_info)
| PointerType (type_info , qual_type) -> (type_info)
| BlockPointerType (type_info , type_ptr) -> (type_info)
| LValueReferenceType (type_info , qual_type) -> (type_info)
| RValueReferenceType (type_info , qual_type) -> (type_info)
| MemberPointerType (type_info , type_ptr) -> (type_info)
| ConstantArrayType (type_info , type_ptr , int) -> (type_info)
| IncompleteArrayType (type_info , type_ptr) -> (type_info)
| VariableArrayType (type_info , type_ptr) -> (type_info)
| DependentSizedArrayType (type_info , type_ptr) -> (type_info)
| DependentSizedExtVectorType (type_info) -> (type_info)
| VectorType (type_info) -> (type_info)
| ExtVectorType (type_info) -> (type_info)
| FunctionProtoType (type_info , function_type_info , params_type_info) -> (type_info)
| FunctionNoProtoType (type_info , function_type_info) -> (type_info)
| UnresolvedUsingType (type_info) -> (type_info)
| ParenType (type_info , type_ptr) -> (type_info)
| TypedefType (type_info , typedef_type_info) -> (type_info)
| AdjustedType (type_info , type_ptr) -> (type_info)
| DecayedType (type_info , type_ptr) -> (type_info)
| TypeOfExprType (type_info) -> (type_info)
| TypeOfType (type_info) -> (type_info)
| DecltypeType (type_info , type_ptr) -> (type_info)
| UnaryTransformType (type_info) -> (type_info)
| RecordType (type_info , pointer) -> (type_info)
| EnumType (type_info , pointer) -> (type_info)
| ElaboratedType (type_info) -> (type_info)
| AttributedType (type_info , attr_type_info) -> (type_info)
| TemplateTypeParmType (type_info) -> (type_info)
| SubstTemplateTypeParmType (type_info) -> (type_info)
| SubstTemplateTypeParmPackType (type_info) -> (type_info)
| TemplateSpecializationType (type_info) -> (type_info)
| AutoType (type_info) -> (type_info)
| InjectedClassNameType (type_info) -> (type_info)
| DependentNameType (type_info) -> (type_info)
| DependentTemplateSpecializationType (type_info) -> (type_info)
| PackExpansionType (type_info) -> (type_info)
| ObjCObjectType (type_info , objc_object_type_info) -> (type_info)
| ObjCInterfaceType (type_info , pointer) -> (type_info)
| ObjCObjectPointerType (type_info , qual_type) -> (type_info)
| PipeType (type_info) -> (type_info)
| AtomicType (type_info , type_ptr) -> (type_info)

