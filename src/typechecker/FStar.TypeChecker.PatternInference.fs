﻿(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.TypeChecker.PatternInference
open FStar.ST
open FStar.All

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
module Const = FStar.Parser.Const
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module BU = FStar.Util

let filter_trigger (names:set<bv>) (t:S.term) =
    let bvs = FStar.Syntax.Free.names t in
    if BU.set_is_subset_of names bvs then Some t else None

let has_no_smt_theory_symbols env e =
    match (SS.compress e).n with
    | Tm_fvar fv
    | Tm_uinst({n=Tm_fvar fv}, _)
      when Env.fv_has_attr env fv Const.smt_theory_symbol_attr_lid -> false
    | _ -> true

let rec find_trigger env (names:set<bv>) (t:S.term) : (bool * list<S.term>) =
    (* To automatically generate patterns for (forall (x1...xn). e) or (exists (x1...xn). e), 
     F* searches inside e for a term t that contains all the variables x1...xn:
      - For simplicity, the search need not look inside other binders, 
        such as nested foralls, exists, let, or lambdas inside e.
         -- this could be improved, but it will prevent accidentally generating patterns that 
            include out-of-scope variables
      - The term t should contain only function applications, constants, and variables.  
        It should contain at least one function application (i.e. it can't just be a variable by itself).  
        It should not contain:
         -- any function with the "[@smt_theory_symbol]" attribute, like /\, ==, +, etc.
         -- "let", foralls, exists, and lambdas
      - F* should make t as small as possible while still covering x1...xn.  
        For example, it should choose f(x, y) instead of h(f(x, y)).
      - If there are no such t, automatic generation fails.
      - There may be more than one t.  In this case, F* would generate a disjunction of the 
        terms {:pattern t1 \/ ... \/ tk}. *)
    let debug = false in
    if debug then 
      BU.print2 "find trigger for : %s (%s)\n" (Print.term_to_string t) (Print.tag_of_term (SS.compress t));
    
    match (SS.compress t).n with
    | Tm_bvar x ->
      (false, [])

    | Tm_name x ->
      (false, [])

    | Tm_fvar fv ->
      (false, [])

    | Tm_uinst(e, universes) ->
      find_trigger env names e
     
    | Tm_constant c ->
      (false, [])

    | Tm_type u ->
      (true, [])

    | Tm_abs(xs, body, _) -> //fun x1 .. xn -> body
      (true, [])

    | Tm_arrow(xs, body) ->
      (true, [])

    | Tm_refine(x, phi) ->
      (true, [])

    | Tm_app (e, args) ->
      // make sure e doesn't have [@smt_theory_symbol]
      // compute trigger for each args
      // if an arg has a trigger that mention all the bv, then its a trigger
      // if there is no trigger from the args then
      // if none of the args is a trigger killer, then Tm_app is a trigger
      
      //if (FStar.TypeChecker.Env.lookup_attrs_of_lid)
      begin
      match (SS.compress e).n with
      | Tm_fvar fv
      | Tm_uinst({n=Tm_fvar fv}, _)
        when (S.fv_eq_lid fv Const.forall_lid
          ||  S.fv_eq_lid fv Const.exists_lid) ->
        (true, [])

      | _ ->
        let (trigger_killer, _) = find_trigger env names e in
        let (trigger_killer, c) = List.fold_left (fun (k, l) (e, q) -> 
                                      let (b, c) = find_trigger env names e in 
                                      ((k || b), l@c))
                                  (trigger_killer, []) args in
        let c = c |> List.choose (fun t -> filter_trigger names t) in
        let  c = 
          match c with
          | [] -> 
            if (not trigger_killer) && (has_no_smt_theory_symbols env e) then
             // no suitable trigger found yet, add current term as a candidate.
             // Still keep the other candidates around in case we want to infer 
             // patterns with ';'
             c@[t]
            else c
          | _ -> c
        in 
        (trigger_killer, c)
      end
    | Tm_match(e, branches) ->
      (true, [])

    | Tm_ascribed _ -> // what is an ascribed
      (true, [])

    | Tm_let((is_rec, source_lbs), body) ->
      (true, [])

    | Tm_uvar (u, _) -> 
      (false, [])

    | Tm_delayed _ ->
      failwith "Tm_delayed is impossible after compress"

    | Tm_meta(e, m) ->
      (true, [])

    | Tm_lazy i ->
      (true, [])

    | Tm_quoted (tm, qi) ->
      (true, [])

    | Tm_unknown -> 
      (true, [])

(* let check_no_smt_theory_symbols env t =
  match (SS.compress t).n with
  | Tm_fvar fv ->
      if Env.fv_has_attr en fv Const.smt_theory_symbol_attr_lid then [t]
      else []
*)

let terms_to_bvs names =
    match names with
    | [] -> failwith "Empty bound vars"
    | hd::tl ->
        List.fold_left (fun out x -> BU.set_union out (Free.names x)) (Free.names hd) tl

let infer_pattern env (names: list<S.term>) (t:S.term) : list<S.args> =
    let debug = true in
    if debug then 
      BU.print3 "Infer pattern for : %s (%s) with names: (%s)\n" 
        (Print.term_to_string t) 
        (Print.tag_of_term (SS.compress t))
        (names |> List.map Print.term_to_string |> String.concat ", ");
    let bvs = terms_to_bvs names in
    let (_, p) = find_trigger env bvs t in
    let pats = p |> List.choose (fun t -> filter_trigger bvs t) in
    if debug then
      BU.print1 "Found patterns: %s\n" (pats |> List.map Print.term_to_string |> String.concat "; ");
    List.fold_left (fun l t -> l@[[S.as_arg t]]) [] pats

let remove_invalid_pattern (names: list<S.term>) (pats: list<S.args>) : list<S.args> =
    match names with
    | [] -> pats
    | _ ->
      let bvs = terms_to_bvs names in
      let pats = List.fold_left(fun l p -> let p = List.choose (fun (t,_) -> filter_trigger bvs t) p in l@p) [] pats in
      List.fold_left (fun l t -> l@[[S.as_arg t]]) [] pats