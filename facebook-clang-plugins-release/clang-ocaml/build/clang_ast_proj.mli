(*
 *  Copyright (c) 2014, Facebook, Inc.
 *  All rights reserved.
 *
 *  This source code is licensed under the BSD-style license found in the
 *  LICENSE file in the root directory of this source tree. An additional grant
 *  of patent rights can be found in the PATENTS file in the same directory.
 *
 *)

open Clang_ast_t

val get_decl_kind_string : decl -> string
val get_decl_tuple : decl -> (decl_info)
val get_decl_context_tuple : decl -> (decl list * decl_context_info) option
val get_named_decl_tuple : decl -> (decl_info * named_decl_info) option
val get_type_decl_tuple : decl -> (decl_info * named_decl_info * opt_type * type_ptr) option
val get_tag_decl_tuple : decl -> (decl_info * named_decl_info * opt_type * type_ptr * decl list * decl_context_info) option

val get_stmt_kind_string : stmt -> string
val get_stmt_tuple : stmt -> (stmt_info * stmt list)
val get_expr_tuple : stmt -> (stmt_info * stmt list * expr_info) option

val get_type_tuple : c_type -> (type_info)

val update_decl_tuple : ((decl_info) -> (decl_info)) -> decl -> decl
val update_decl_context_tuple : ((decl list * decl_context_info) -> (decl list * decl_context_info)) -> decl -> decl
val update_named_decl_tuple : ((decl_info * named_decl_info) -> (decl_info * named_decl_info)) -> decl -> decl
val update_type_decl_tuple : ((decl_info * named_decl_info * opt_type * type_ptr) -> (decl_info * named_decl_info * opt_type * type_ptr)) -> decl -> decl
val update_tag_decl_tuple : ((decl_info * named_decl_info * opt_type * type_ptr * decl list * decl_context_info) -> (decl_info * named_decl_info * opt_type * type_ptr * decl list * decl_context_info)) -> decl -> decl

val update_stmt_tuple : ((stmt_info * stmt list) -> (stmt_info * stmt list)) -> stmt -> stmt
val update_expr_tuple : ((stmt_info * stmt list * expr_info) -> (stmt_info * stmt list * expr_info)) -> stmt -> stmt

