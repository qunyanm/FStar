open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___8_5 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___8_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___8_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___8_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___8_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___8_5.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___8_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___8_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___8_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___8_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___8_5.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___8_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___8_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___8_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___8_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___8_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___8_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___8_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___8_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___8_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___8_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___8_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 = (uu___8_5.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___8_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___8_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___8_5.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___8_5.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___8_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___8_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___8_5.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___8_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___8_5.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___8_5.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___8_5.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___8_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___8_5.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice = (uu___8_5.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___8_5.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___8_5.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___8_5.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___8_5.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___8_5.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___8_5.FStar_TypeChecker_Env.nbe)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___11_13 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___11_13.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___11_13.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___11_13.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___11_13.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___11_13.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___11_13.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___11_13.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___11_13.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___11_13.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___11_13.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___11_13.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___11_13.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___11_13.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___11_13.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___11_13.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___11_13.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___11_13.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___11_13.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___11_13.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___11_13.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___11_13.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___11_13.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___11_13.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___11_13.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___11_13.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___11_13.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___11_13.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___11_13.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___11_13.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___11_13.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___11_13.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___11_13.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___11_13.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___11_13.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___11_13.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___11_13.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_13.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___11_13.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___11_13.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___11_13.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___11_13.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___11_13.FStar_TypeChecker_Env.nbe)
    }
  
let (mk_lex_list :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun vs  ->
    FStar_List.fold_right
      (fun v1  ->
         fun tl1  ->
           let r =
             if tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v1.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos
                 tl1.FStar_Syntax_Syntax.pos
              in
           let uu____49 =
             let uu____54 =
               let uu____55 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____64 =
                 let uu____75 = FStar_Syntax_Syntax.as_arg tl1  in [uu____75]
                  in
               uu____55 :: uu____64  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____54
              in
           uu____49 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_116  ->
    match uu___0_116 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____121 -> false
  
let steps :
  'Auu____130 . 'Auu____130 -> FStar_TypeChecker_Env.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
  
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
  
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
  
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____218 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____232 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____232 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____259 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____263 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____263
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____267 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____267 uu____269
                             in
                          let uu____272 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____272
                           in
                        let uu____278 =
                          let uu____291 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____292 =
                            let uu____293 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____293
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____291 env uu____292
                           in
                        match uu____278 with
                        | (s,uu____308,g0) ->
                            let uu____322 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____322 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____332 =
                                     FStar_TypeChecker_Env.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____332
                                    in
                                 (s, g1)
                             | uu____333 -> fail1 ())))
             in
          aux false kt
  
let push_binding :
  'Auu____344 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____344) -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____399 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____399
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
  
let (set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____425  ->
           let uu____426 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____426 t)
  
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> e 
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____485 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                   uu____485
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_Syntax_Syntax.res_typ  in
           let uu____488 =
             let uu____495 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____495 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____505 =
                   FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                     t'
                    in
                 (match uu____505 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                      let uu____519 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____519 with
                       | (e2,g) ->
                           ((let uu____533 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____533
                             then
                               let uu____536 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____538 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____540 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____542 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____536 uu____538 uu____540 uu____542
                             else ());
                            (let msg =
                               let uu____554 =
                                 FStar_TypeChecker_Env.is_trivial_guard_formula
                                   g
                                  in
                               if uu____554
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _583  ->
                                      FStar_Pervasives_Native.Some _583)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Env.conj_guard g guard  in
                             let lc2 =
                               let uu____586 =
                                 (FStar_All.pipe_right tlc FStar_Util.is_left)
                                   &&
                                   (FStar_TypeChecker_Util.should_return env
                                      (FStar_Pervasives_Native.Some e2) lc1)
                                  in
                               if uu____586
                               then
                                 let uu____594 =
                                   let uu____595 =
                                     FStar_TypeChecker_Util.lcomp_univ_opt
                                       lc1
                                      in
                                   FStar_TypeChecker_Util.return_value env
                                     uu____595 t1 e2
                                    in
                                 FStar_All.pipe_right uu____594
                                   FStar_Syntax_Util.lcomp_of_comp
                               else lc1  in
                             let uu____600 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc2 g1
                                in
                             match uu____600 with
                             | (lc3,g2) ->
                                 let uu____613 = set_lcomp_result lc3 t'  in
                                 ((memo_tk e2 t'), uu____613, g2)))))
              in
           match uu____488 with | (e1,lc1,g) -> (e1, lc1, g))
  
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____651 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____651 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____661 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____661 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun copt  ->
      fun ec  ->
        let uu____714 = ec  in
        match uu____714 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____737 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____737
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____742 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____742
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____748 =
              match copt with
              | FStar_Pervasives_Native.Some uu____761 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____764 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____767 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____767))
                     in
                  if uu____764
                  then
                    let uu____776 =
                      let uu____779 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____779  in
                    (uu____776, c)
                  else
                    (let uu____784 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____784
                     then
                       let uu____793 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____793)
                     else
                       (let uu____798 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____798
                        then
                          let uu____807 =
                            let uu____810 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____810  in
                          (uu____807, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____748 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Env.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____838 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____838
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      ((let uu____841 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Low
                           in
                        if uu____841
                        then
                          let uu____845 = FStar_Syntax_Print.term_to_string e
                             in
                          let uu____847 =
                            FStar_Syntax_Print.comp_to_string c4  in
                          let uu____849 =
                            FStar_Syntax_Print.comp_to_string expected_c  in
                          FStar_Util.print3
                            "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                            uu____845 uu____847 uu____849
                        else ());
                       (let uu____854 =
                          FStar_TypeChecker_Util.check_comp env e c4
                            expected_c
                           in
                        match uu____854 with
                        | (e1,uu____868,g) ->
                            let g1 =
                              let uu____871 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_TypeChecker_Util.label_guard uu____871
                                "could not prove post-condition" g
                               in
                            ((let uu____874 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Low
                                 in
                              if uu____874
                              then
                                let uu____877 =
                                  FStar_Range.string_of_range
                                    e1.FStar_Syntax_Syntax.pos
                                   in
                                let uu____879 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g1
                                   in
                                FStar_Util.print2
                                  "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                  uu____877 uu____879
                              else ());
                             (let e2 =
                                FStar_TypeChecker_Util.maybe_lift env e1
                                  (FStar_Syntax_Util.comp_effect_name c4)
                                  (FStar_Syntax_Util.comp_effect_name
                                     expected_c)
                                  (FStar_Syntax_Util.comp_result c4)
                                 in
                              (e2, expected_c, g1)))))))
  
let no_logical_guard :
  'Auu____894 'Auu____895 .
    FStar_TypeChecker_Env.env ->
      ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____917  ->
      match uu____917 with
      | (te,kt,f) ->
          let uu____927 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____927 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____935 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____941 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____935 uu____941)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____954 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____954 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____959 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____959
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1001 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1001 with
        | (head1,args) ->
            let uu____1046 =
              let uu____1061 =
                let uu____1062 = FStar_Syntax_Util.un_uinst head1  in
                uu____1062.FStar_Syntax_Syntax.n  in
              (uu____1061, args)  in
            (match uu____1046 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1078) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1105,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1106))::(hd1,FStar_Pervasives_Native.None
                                                                 )::(tl1,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd1  in
                 let tlvs = get_pat_vars' all andlist tl1  in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1183,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1184))::(pat,FStar_Pervasives_Native.None
                                                                 )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1268 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1299 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1299) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1335 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1342 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1335 uu____1342  in
          let uu____1343 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1370  ->
                    match uu____1370 with
                    | (b,uu____1377) ->
                        let uu____1378 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1378))
             in
          match uu____1343 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1385) ->
              let uu____1390 =
                let uu____1396 =
                  let uu____1398 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1398
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1396)  in
              FStar_Errors.log_issue rng uu____1390
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1424 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1424 with
        | (head1,args) ->
            let uu____1469 =
              let uu____1484 =
                let uu____1485 = FStar_Syntax_Util.un_uinst head1  in
                uu____1485.FStar_Syntax_Syntax.n  in
              (uu____1484, args)  in
            (match uu____1469 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1501) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1523::(hd1,uu____1525)::(tl1,uu____1527)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1594 = pat_terms hd1  in
                 let uu____1597 = pat_terms tl1  in
                 FStar_List.append uu____1594 uu____1597
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1601::(pat,uu____1603)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1688 -> [])
         in
      let rec aux t1 =
        let uu____1713 =
          let uu____1714 = FStar_Syntax_Subst.compress t1  in
          uu____1714.FStar_Syntax_Syntax.n  in
        match uu____1713 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1719 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1720 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1721 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1722 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1735 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1736 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1737 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1756 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1771 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1778 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1801 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1815 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1838 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1846 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____1846 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____1879 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____1896  ->
                   match uu____1896 with
                   | (t3,uu____1908) ->
                       let uu____1913 = aux t3  in
                       FStar_List.append acc uu____1913) uu____1879 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1917,uu____1918) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1960) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____1966) -> aux t2  in
      let tlist =
        let uu____1974 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____1974 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = (Prims.parse_int "0")
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____1997 =
                    let uu____1999 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____1999  in
                  Prims.op_Hat s uu____1997) "" tlist
            in
         let uu____2003 =
           let uu____2009 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2009)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2003)
  
let check_smt_pat :
  'Auu____2024 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2024) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2065 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2065
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2068;
                  FStar_Syntax_Syntax.effect_name = uu____2069;
                  FStar_Syntax_Syntax.result_typ = uu____2070;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2074)::[];
                  FStar_Syntax_Syntax.flags = uu____2075;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2137 -> failwith "Impossible"
          else ()
  
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env  in
            let env1 =
              let uu___345_2200 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___345_2200.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___345_2200.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___345_2200.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___345_2200.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___345_2200.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___345_2200.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___345_2200.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___345_2200.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___345_2200.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___345_2200.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___345_2200.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___345_2200.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___345_2200.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___345_2200.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___345_2200.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___345_2200.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___345_2200.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___345_2200.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___345_2200.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___345_2200.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___345_2200.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___345_2200.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___345_2200.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___345_2200.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___345_2200.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___345_2200.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___345_2200.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___345_2200.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___345_2200.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___345_2200.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___345_2200.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___345_2200.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___345_2200.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___345_2200.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___345_2200.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___345_2200.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.postprocess =
                  (uu___345_2200.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___345_2200.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___345_2200.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___345_2200.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___345_2200.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___345_2200.FStar_TypeChecker_Env.nbe)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2226 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2226
               then
                 let uu____2229 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2232 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2229 uu____2232
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2266  ->
                         match uu____2266 with
                         | (b,uu____2276) ->
                             let t =
                               let uu____2282 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2282
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2285 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2286 -> []
                              | uu____2301 ->
                                  let uu____2302 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2302])))
                  in
               let as_lex_list dec =
                 let uu____2315 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2315 with
                 | (head1,uu____2335) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2363 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2371 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2380  ->
                         match uu___1_2380 with
                         | FStar_Syntax_Syntax.DECREASES uu____2382 -> true
                         | uu____2386 -> false))
                  in
               match uu____2371 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2393 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2414 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2443 =
              match uu____2443 with
              | (l,t,u_names) ->
                  let uu____2467 =
                    let uu____2468 = FStar_Syntax_Subst.compress t  in
                    uu____2468.FStar_Syntax_Syntax.n  in
                  (match uu____2467 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2527  ->
                                 match uu____2527 with
                                 | (x,imp) ->
                                     let uu____2546 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2546
                                     then
                                       let uu____2555 =
                                         let uu____2556 =
                                           let uu____2559 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2559
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2556
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2555, imp)
                                     else (x, imp)))
                          in
                       let uu____2566 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2566 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2587 =
                                let uu____2592 =
                                  let uu____2593 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2602 =
                                    let uu____2613 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2613]  in
                                  uu____2593 :: uu____2602  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2592
                                 in
                              uu____2587 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2648 = FStar_Util.prefix formals2  in
                            (match uu____2648 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___412_2711 = last1  in
                                   let uu____2712 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___412_2711.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___412_2711.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2712
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2748 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____2748
                                   then
                                     let uu____2751 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2753 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2755 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2751 uu____2753 uu____2755
                                   else ());
                                  (l, t', u_names))))
                   | uu____2762 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos)
               in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
  
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt  ->
    fun g  ->
      match topt with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1  ->
               let uu____2826 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2826)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3429 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3429
       then
         let uu____3432 =
           let uu____3434 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3434  in
         let uu____3436 = FStar_Syntax_Print.term_to_string e  in
         let uu____3438 =
           let uu____3440 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3440  in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3432
           uu____3436 uu____3438
       else ());
      (let uu____3444 =
         FStar_Util.record_time
           (fun uu____3463  ->
              tc_maybe_toplevel_term
                (let uu___431_3466 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___431_3466.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___431_3466.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___431_3466.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___431_3466.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___431_3466.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___431_3466.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___431_3466.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___431_3466.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___431_3466.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___431_3466.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___431_3466.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___431_3466.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___431_3466.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___431_3466.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___431_3466.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___431_3466.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___431_3466.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___431_3466.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___431_3466.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___431_3466.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___431_3466.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___431_3466.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___431_3466.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___431_3466.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___431_3466.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___431_3466.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___431_3466.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___431_3466.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___431_3466.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___431_3466.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___431_3466.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___431_3466.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___431_3466.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___431_3466.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___431_3466.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___431_3466.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___431_3466.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___431_3466.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___431_3466.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___431_3466.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___431_3466.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___431_3466.FStar_TypeChecker_Env.nbe)
                 }) e)
          in
       match uu____3444 with
       | (r,ms) ->
           ((let uu____3491 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3491
             then
               ((let uu____3495 =
                   let uu____3497 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3497
                    in
                 let uu____3499 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3501 =
                   let uu____3503 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3503  in
                 let uu____3504 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3495 uu____3499 uu____3501 uu____3504);
                (let uu____3507 = r  in
                 match uu____3507 with
                 | (e1,uu____3515,uu____3516) ->
                     let uu____3517 =
                       let uu____3519 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3519
                        in
                     let uu____3521 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____3523 =
                       let uu____3525 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____3525  in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3517
                       uu____3521 uu____3523))
             else ());
            r))

and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      (let uu____3543 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____3543
       then
         let uu____3546 =
           let uu____3548 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3548  in
         let uu____3550 = FStar_Syntax_Print.tag_of_term top  in
         let uu____3552 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3546 uu____3550
           uu____3552
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3563 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3593 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3600 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3613 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3614 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3615 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3616 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3617 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3636 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3651 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3658 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_3674 =
             match uu___2_3674 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3680 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3696 =
                 let uu____3697 = FStar_Syntax_Subst.compress t  in
                 uu____3697.FStar_Syntax_Syntax.n  in
               match uu____3696 with
               | FStar_Syntax_Syntax.Tm_name uu____3701 -> true
               | uu____3703 -> false  in
             FStar_Util.for_some
               (fun uu____3713  ->
                  match uu____3713 with
                  | (uu____3719,t) ->
                      let uu____3721 = is_name1 t  in
                      Prims.op_Negation uu____3721)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____3740  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____3783  ->
                       match uu____3783 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___504_3812 = qi  in
                  let uu____3813 =
                    FStar_List.map
                      (fun uu____3841  ->
                         match uu____3841 with
                         | ((bv,uu____3857),bv') ->
                             let uu____3869 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____3869)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___504_3812.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3813
                  }  in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                let e1 =
                  FStar_List.fold_left
                    (fun t  ->
                       fun lb  ->
                         let uu____3881 =
                           let uu____3888 =
                             let uu____3889 =
                               let uu____3903 =
                                 let uu____3906 =
                                   let uu____3907 =
                                     let uu____3914 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____3914
                                      in
                                   [uu____3907]  in
                                 FStar_Syntax_Subst.close uu____3906 t  in
                               ((false, [lb]), uu____3903)  in
                             FStar_Syntax_Syntax.Tm_let uu____3889  in
                           FStar_Syntax_Syntax.mk uu____3888  in
                         uu____3881 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____3950 =
                  FStar_List.fold_right
                    (fun uu____3986  ->
                       fun uu____3987  ->
                         match (uu____3986, uu____3987) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4056 = tc_term env_tm tm  in
                             (match uu____4056 with
                              | (tm1,uu____4074,g) ->
                                  let uu____4076 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4076))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____3950 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___532_4118 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___532_4118.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       }  in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let c =
                  FStar_Syntax_Syntax.mk_Comp
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        [FStar_Syntax_Syntax.U_zero];
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_Tac_lid;
                      FStar_Syntax_Syntax.result_typ =
                        FStar_Syntax_Syntax.t_term;
                      FStar_Syntax_Syntax.effect_args = [];
                      FStar_Syntax_Syntax.flags =
                        [FStar_Syntax_Syntax.SOMETRIVIAL;
                        FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                    }
                   in
                let uu____4137 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4137 with
                 | (env',uu____4151) ->
                     let uu____4156 =
                       tc_term
                         (let uu___541_4165 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___541_4165.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___541_4165.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___541_4165.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___541_4165.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___541_4165.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___541_4165.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___541_4165.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___541_4165.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___541_4165.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___541_4165.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___541_4165.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___541_4165.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___541_4165.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___541_4165.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___541_4165.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___541_4165.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___541_4165.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___541_4165.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___541_4165.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___541_4165.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___541_4165.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___541_4165.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___541_4165.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___541_4165.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___541_4165.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___541_4165.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___541_4165.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___541_4165.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___541_4165.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___541_4165.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___541_4165.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___541_4165.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___541_4165.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___541_4165.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___541_4165.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___541_4165.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___541_4165.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___541_4165.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___541_4165.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___541_4165.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___541_4165.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___541_4165.FStar_TypeChecker_Env.nbe)
                          }) qt
                        in
                     (match uu____4156 with
                      | (qt1,uu____4174,uu____4175) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4181 =
                            let uu____4188 =
                              let uu____4193 =
                                FStar_Syntax_Util.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4193  in
                            value_check_expected_typ env1 top uu____4188
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4181 with
                           | (t1,lc,g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   FStar_Pervasives_Native.None
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4210;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4211;
             FStar_Syntax_Syntax.ltyp = uu____4212;
             FStar_Syntax_Syntax.rng = uu____4213;_}
           ->
           let uu____4224 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4224
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4231 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4231 with
            | (e2,c,g) ->
                let g1 =
                  let uu___571_4248 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___571_4248.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___571_4248.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___571_4248.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____4249 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4249, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (attr,names1,pats)) ->
           let uu____4296 = FStar_Syntax_Util.type_u ()  in
           (match uu____4296 with
            | (t,u) ->
                let uu____4309 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4309 with
                 | (e2,c,g) ->
                     let is_nopattern_attr attr1 =
                       match attr1 with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some x ->
                           x.FStar_Ident.idText = "nopattern"
                        in
                     let pats1 =
                       match pats with
                       | [] ->
                           let uu____4356 =
                             (FStar_Options.auto_patterns ()) &&
                               (Prims.op_Negation (is_nopattern_attr attr))
                              in
                           if uu____4356
                           then
                             let uu____4361 =
                               FStar_TypeChecker_PatternInference.infer_pattern
                                 env1 names1 e2
                                in
                             (match uu____4361 with
                              | [] ->
                                  ((let uu____4367 =
                                      let uu____4373 =
                                        let uu____4375 =
                                          FStar_Syntax_Print.term_to_string
                                            e2
                                           in
                                        let uu____4377 =
                                          let uu____4379 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Syntax_Print.tag_of_term
                                            uu____4379
                                           in
                                        let uu____4380 =
                                          let uu____4382 =
                                            FStar_All.pipe_right names1
                                              (FStar_List.map
                                                 FStar_Syntax_Print.term_to_string)
                                             in
                                          FStar_All.pipe_right uu____4382
                                            (FStar_String.concat ", ")
                                           in
                                        FStar_Util.format3
                                          "no pattern can be inferred : %s (%s) with names: (%s)\n"
                                          uu____4375 uu____4377 uu____4380
                                         in
                                      (FStar_Errors.Warning_NoPatternInferred,
                                        uu____4373)
                                       in
                                    FStar_Errors.log_issue
                                      e2.FStar_Syntax_Syntax.pos uu____4367);
                                   [])
                              | pats1 -> pats1)
                           else pats
                       | uu____4404 -> pats  in
                     let uu____4417 =
                       let uu____4434 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4434 with
                       | (env2,uu____4458) -> tc_smt_pats env2 pats1  in
                     (match uu____4417 with
                      | (pats2,g') ->
                          let g'1 =
                            let uu___607_4496 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___607_4496.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___607_4496.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___607_4496.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____4497 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (attr, names1, pats2))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4518 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4497, c, uu____4518))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4524 =
             let uu____4525 = FStar_Syntax_Subst.compress e1  in
             uu____4525.FStar_Syntax_Syntax.n  in
           (match uu____4524 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4534,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4536;
                               FStar_Syntax_Syntax.lbtyp = uu____4537;
                               FStar_Syntax_Syntax.lbeff = uu____4538;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4540;
                               FStar_Syntax_Syntax.lbpos = uu____4541;_}::[]),e2)
                ->
                let uu____4572 =
                  let uu____4579 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4579 e11  in
                (match uu____4572 with
                 | (e12,c1,g1) ->
                     let uu____4589 = tc_term env1 e2  in
                     (match uu____4589 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2)
                             in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ
                             in
                          let attrs =
                            let uu____4613 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_Syntax_Syntax.eff_name
                               in
                            if uu____4613
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____4623 =
                              let uu____4630 =
                                let uu____4631 =
                                  let uu____4645 =
                                    let uu____4653 =
                                      let uu____4656 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____4656]  in
                                    (false, uu____4653)  in
                                  (uu____4645, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____4631  in
                              FStar_Syntax_Syntax.mk uu____4630  in
                            uu____4623 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4680 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____4680)))
            | uu____4681 ->
                let uu____4682 = tc_term env1 e1  in
                (match uu____4682 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____4704) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____4716) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____4735 = tc_term env1 e1  in
           (match uu____4735 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____4759) ->
           let uu____4806 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4806 with
            | (env0,uu____4820) ->
                let uu____4825 = tc_comp env0 expected_c  in
                (match uu____4825 with
                 | (expected_c1,uu____4839,g) ->
                     let uu____4841 =
                       let uu____4848 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____4848 e1  in
                     (match uu____4841 with
                      | (e2,c',g') ->
                          let uu____4858 =
                            let uu____4865 =
                              let uu____4870 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____4870)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____4865
                             in
                          (match uu____4858 with
                           | (e3,expected_c2,g'') ->
                               let uu____4880 = tc_tactic_opt env0 topt  in
                               (match uu____4880 with
                                | (topt1,gtac) ->
                                    let e4 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_ascribed
                                           (e3,
                                             ((FStar_Util.Inr expected_c2),
                                               topt1),
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.comp_effect_name
                                                   expected_c2))))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let lc =
                                      FStar_Syntax_Util.lcomp_of_comp
                                        expected_c2
                                       in
                                    let f =
                                      let uu____4940 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____4940
                                       in
                                    let uu____4941 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____4941 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____4958 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____4958
                                            in
                                         let uu____4959 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____4959)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____4963) ->
           let uu____5010 = FStar_Syntax_Util.type_u ()  in
           (match uu____5010 with
            | (k,u) ->
                let uu____5023 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____5023 with
                 | (t1,uu____5037,f) ->
                     let uu____5039 = tc_tactic_opt env1 topt  in
                     (match uu____5039 with
                      | (topt1,gtac) ->
                          let uu____5058 =
                            let uu____5065 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____5065 e1  in
                          (match uu____5058 with
                           | (e2,c,g) ->
                               let uu____5075 =
                                 let uu____5080 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5086  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5080 e2 c f
                                  in
                               (match uu____5075 with
                                | (c1,f1) ->
                                    let uu____5096 =
                                      let uu____5103 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_Syntax_Syntax.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____5103
                                        c1
                                       in
                                    (match uu____5096 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____5150 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5150
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____5152 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____5152)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5153;
              FStar_Syntax_Syntax.vars = uu____5154;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5233 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5233 with
            | (unary_op1,uu____5257) ->
                let head1 =
                  let uu____5285 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5285
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____5333;
              FStar_Syntax_Syntax.vars = uu____5334;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5413 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5413 with
            | (unary_op1,uu____5437) ->
                let head1 =
                  let uu____5465 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5465
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____5513);
              FStar_Syntax_Syntax.pos = uu____5514;
              FStar_Syntax_Syntax.vars = uu____5515;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5594 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5594 with
            | (unary_op1,uu____5618) ->
                let head1 =
                  let uu____5646 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5646
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____5694;
              FStar_Syntax_Syntax.vars = uu____5695;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5791 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5791 with
            | (unary_op1,uu____5815) ->
                let head1 =
                  let uu____5843 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5843
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5899;
              FStar_Syntax_Syntax.vars = uu____5900;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____5938 =
             let uu____5945 =
               let uu____5946 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5946  in
             tc_term uu____5945 e1  in
           (match uu____5938 with
            | (e2,c,g) ->
                let uu____5970 = FStar_Syntax_Util.head_and_args top  in
                (match uu____5970 with
                 | (head1,uu____5994) ->
                     let uu____6019 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____6052 =
                       let uu____6053 =
                         let uu____6054 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____6054  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____6053
                        in
                     (uu____6019, uu____6052, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6055;
              FStar_Syntax_Syntax.vars = uu____6056;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____6109 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6109 with
            | (head1,uu____6133) ->
                let env' =
                  let uu____6159 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6159  in
                let uu____6160 = tc_term env' r  in
                (match uu____6160 with
                 | (er,uu____6174,gr) ->
                     let uu____6176 = tc_term env1 t  in
                     (match uu____6176 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____6193 =
                            let uu____6194 =
                              let uu____6199 =
                                let uu____6200 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____6209 =
                                  let uu____6220 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____6220]  in
                                uu____6200 :: uu____6209  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6199
                               in
                            uu____6194 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____6193, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6253;
              FStar_Syntax_Syntax.vars = uu____6254;_},uu____6255)
           ->
           let uu____6280 =
             let uu____6286 =
               let uu____6288 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6288  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6286)  in
           FStar_Errors.raise_error uu____6280 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6298;
              FStar_Syntax_Syntax.vars = uu____6299;_},uu____6300)
           ->
           let uu____6325 =
             let uu____6331 =
               let uu____6333 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6333  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6331)  in
           FStar_Errors.raise_error uu____6325 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6343;
              FStar_Syntax_Syntax.vars = uu____6344;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6391 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____6391 with
             | (env0,uu____6405) ->
                 let uu____6410 = tc_term env0 e1  in
                 (match uu____6410 with
                  | (e2,c,g) ->
                      let uu____6426 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____6426 with
                       | (reify_op,uu____6450) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_Syntax_Syntax.res_typ
                              in
                           let ef =
                             let uu____6477 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_Syntax_Util.comp_effect_name uu____6477
                              in
                           ((let uu____6481 =
                               let uu____6483 =
                                 FStar_TypeChecker_Env.is_user_reifiable_effect
                                   env1 ef
                                  in
                               Prims.op_Negation uu____6483  in
                             if uu____6481
                             then
                               let uu____6486 =
                                 let uu____6492 =
                                   FStar_Util.format1
                                     "Effect %s cannot be reified"
                                     ef.FStar_Ident.str
                                    in
                                 (FStar_Errors.Fatal_EffectCannotBeReified,
                                   uu____6492)
                                  in
                               FStar_Errors.raise_error uu____6486
                                 e2.FStar_Syntax_Syntax.pos
                             else ());
                            (let repr =
                               let uu____6499 =
                                 FStar_Syntax_Syntax.lcomp_comp c  in
                               FStar_TypeChecker_Env.reify_comp env1
                                 uu____6499 u_c
                                in
                             let e3 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (reify_op, [(e2, aqual)]))
                                 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let c1 =
                               let uu____6536 =
                                 FStar_TypeChecker_Env.is_total_effect env1
                                   ef
                                  in
                               if uu____6536
                               then
                                 let uu____6539 =
                                   FStar_Syntax_Syntax.mk_Total repr  in
                                 FStar_All.pipe_right uu____6539
                                   FStar_Syntax_Util.lcomp_of_comp
                               else
                                 (let ct =
                                    {
                                      FStar_Syntax_Syntax.comp_univs = [u_c];
                                      FStar_Syntax_Syntax.effect_name =
                                        FStar_Parser_Const.effect_Dv_lid;
                                      FStar_Syntax_Syntax.result_typ = repr;
                                      FStar_Syntax_Syntax.effect_args = [];
                                      FStar_Syntax_Syntax.flags = []
                                    }  in
                                  let uu____6551 =
                                    FStar_Syntax_Syntax.mk_Comp ct  in
                                  FStar_All.pipe_right uu____6551
                                    FStar_Syntax_Util.lcomp_of_comp)
                                in
                             let uu____6552 =
                               comp_check_expected_typ env1 e3 c1  in
                             match uu____6552 with
                             | (e4,c2,g') ->
                                 let uu____6568 =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 (e4, c2, uu____6568)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6570;
              FStar_Syntax_Syntax.vars = uu____6571;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6619 =
               let uu____6621 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____6621  in
             if uu____6619
             then
               let uu____6624 =
                 let uu____6630 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6630)  in
               FStar_Errors.raise_error uu____6624 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6636 = FStar_Syntax_Util.head_and_args top  in
             match uu____6636 with
             | (reflect_op,uu____6660) ->
                 let uu____6685 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____6685 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____6725 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____6725 with
                       | (env_no_ex,topt) ->
                           let uu____6744 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let t =
                               let uu____6764 =
                                 let uu____6771 =
                                   let uu____6772 =
                                     let uu____6789 =
                                       let uu____6800 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____6809 =
                                         let uu____6820 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____6820]  in
                                       uu____6800 :: uu____6809  in
                                     (repr, uu____6789)  in
                                   FStar_Syntax_Syntax.Tm_app uu____6772  in
                                 FStar_Syntax_Syntax.mk uu____6771  in
                               uu____6764 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6865 =
                               let uu____6872 =
                                 let uu____6873 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____6873
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____6872 t  in
                             match uu____6865 with
                             | (t1,uu____6899,g) ->
                                 let uu____6901 =
                                   let uu____6902 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____6902.FStar_Syntax_Syntax.n  in
                                 (match uu____6901 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____6915,(res,uu____6917)::(wp,uu____6919)::[])
                                      -> (t1, res, wp, g)
                                  | uu____6976 -> failwith "Impossible")
                              in
                           (match uu____6744 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____7002 =
                                  let uu____7009 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____7009 with
                                  | (e2,c,g) ->
                                      ((let uu____7026 =
                                          let uu____7028 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____7028
                                           in
                                        if uu____7026
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____7051 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_Syntax_Syntax.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____7051 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____7062 =
                                                let uu____7072 =
                                                  let uu____7080 =
                                                    let uu____7082 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____7084 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____7082 uu____7084
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____7080,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____7072]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____7062);
                                             (let uu____7102 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____7102)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____7106 =
                                              let uu____7107 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____7107
                                               in
                                            (e2, uu____7106)))
                                   in
                                (match uu____7002 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____7123 =
                                         let uu____7124 =
                                           let uu____7125 =
                                             let uu____7126 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____7126]  in
                                           let uu____7127 =
                                             let uu____7138 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____7138]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____7125;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7127;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7124
                                          in
                                       FStar_All.pipe_right uu____7123
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____7198 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____7198 with
                                      | (e4,c1,g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_Syntax_Syntax.eff_name),
                                                        (c1.FStar_Syntax_Syntax.res_typ)))))
                                              FStar_Pervasives_Native.None
                                              e4.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____7221 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____7221))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7260 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7260 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____7310,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____7311))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7364 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7364 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7439 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7649 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____7439 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____7768 =
               let uu____7769 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____7769 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____7768 instantiate_both  in
           ((let uu____7785 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____7785
             then
               let uu____7788 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____7790 = FStar_Syntax_Print.term_to_string top  in
               let uu____7792 =
                 let uu____7794 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____7794
                   (fun uu___3_7801  ->
                      match uu___3_7801 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7788
                 uu____7790 uu____7792
             else ());
            (let uu____7810 = tc_term (no_inst env2) head1  in
             match uu____7810 with
             | (head2,chead,g_head) ->
                 let uu____7826 =
                   let uu____7833 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____7836 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____7836))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____7833
                   then
                     let uu____7845 =
                       let uu____7852 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____7852
                        in
                     match uu____7845 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____7866 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____7866)
                    in
                 (match uu____7826 with
                  | (e1,c,g) ->
                      let uu____7878 =
                        let uu____7885 =
                          FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
                        if uu____7885
                        then
                          let uu____7894 =
                            FStar_TypeChecker_Util.maybe_instantiate env0 e1
                              c.FStar_Syntax_Syntax.res_typ
                             in
                          match uu____7894 with
                          | (e2,res_typ,implicits) ->
                              let uu____7910 =
                                FStar_Syntax_Util.set_result_typ_lc c res_typ
                                 in
                              (e2, uu____7910, implicits)
                        else (e1, c, FStar_TypeChecker_Env.trivial_guard)  in
                      (match uu____7878 with
                       | (e2,c1,implicits) ->
                           ((let uu____7923 =
                               FStar_TypeChecker_Env.debug env2
                                 FStar_Options.Extreme
                                in
                             if uu____7923
                             then
                               let uu____7926 =
                                 FStar_TypeChecker_Rel.print_pending_implicits
                                   g
                                  in
                               FStar_Util.print1
                                 "Introduced {%s} implicits in application\n"
                                 uu____7926
                             else ());
                            (let uu____7931 =
                               comp_check_expected_typ env0 e2 c1  in
                             match uu____7931 with
                             | (e3,c2,g') ->
                                 let gres =
                                   FStar_TypeChecker_Env.conj_guard g g'  in
                                 let gres1 =
                                   FStar_TypeChecker_Env.conj_guard gres
                                     implicits
                                    in
                                 ((let uu____7950 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.Extreme
                                      in
                                   if uu____7950
                                   then
                                     let uu____7953 =
                                       FStar_Syntax_Print.term_to_string e3
                                        in
                                     let uu____7955 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env2 gres1
                                        in
                                     FStar_Util.print2
                                       "Guard from application node %s is %s\n"
                                       uu____7953 uu____7955
                                   else ());
                                  (e3, c2, gres1))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____7998 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____7998 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____8018 = tc_term env12 e1  in
                (match uu____8018 with
                 | (e11,c1,g1) ->
                     let uu____8034 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8048 = FStar_Syntax_Util.type_u ()  in
                           (match uu____8048 with
                            | (k,uu____8060) ->
                                let uu____8061 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____8061 with
                                 | (res_t,uu____8082,g) ->
                                     let uu____8096 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____8097 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____8096, res_t, uu____8097)))
                        in
                     (match uu____8034 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____8108 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____8108
                            then
                              let uu____8111 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____8111
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____8238 =
                              let uu____8243 =
                                FStar_List.fold_right
                                  (fun uu____8325  ->
                                     fun uu____8326  ->
                                       match (uu____8325, uu____8326) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____8571 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8571)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____8243 with
                              | (cases,g) ->
                                  let uu____8676 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____8676, g)
                               in
                            match uu____8238 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches)
                                   in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____8818  ->
                                              match uu____8818 with
                                              | ((pat,wopt,br),uu____8863,eff_label,uu____8865,uu____8866,uu____8867)
                                                  ->
                                                  let uu____8904 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____8904)))
                                       in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ
                                       in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____8971 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____8971
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____8979 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____8979  in
                                     let lb =
                                       let uu____8983 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____8983 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____8989 =
                                         let uu____8996 =
                                           let uu____8997 =
                                             let uu____9011 =
                                               let uu____9014 =
                                                 let uu____9015 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____9015]  in
                                               FStar_Syntax_Subst.close
                                                 uu____9014 e_match
                                                in
                                             ((false, [lb]), uu____9011)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____8997
                                            in
                                         FStar_Syntax_Syntax.mk uu____8996
                                          in
                                       uu____8989
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____9048 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____9048
                                  then
                                    let uu____9051 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____9053 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____9051 uu____9053
                                  else ());
                                 (let uu____9058 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____9058))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9059;
                FStar_Syntax_Syntax.lbunivs = uu____9060;
                FStar_Syntax_Syntax.lbtyp = uu____9061;
                FStar_Syntax_Syntax.lbeff = uu____9062;
                FStar_Syntax_Syntax.lbdef = uu____9063;
                FStar_Syntax_Syntax.lbattrs = uu____9064;
                FStar_Syntax_Syntax.lbpos = uu____9065;_}::[]),uu____9066)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9092),uu____9093) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9111;
                FStar_Syntax_Syntax.lbunivs = uu____9112;
                FStar_Syntax_Syntax.lbtyp = uu____9113;
                FStar_Syntax_Syntax.lbeff = uu____9114;
                FStar_Syntax_Syntax.lbdef = uu____9115;
                FStar_Syntax_Syntax.lbattrs = uu____9116;
                FStar_Syntax_Syntax.lbpos = uu____9117;_}::uu____9118),uu____9119)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9147),uu____9148) ->
           check_inner_let_rec env1 top)

and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun head1  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____9182 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9221))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9262 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____9182 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____9295 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____9295 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____9299 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9299)
                 in
              let uu____9302 =
                let uu____9309 =
                  let uu____9310 =
                    let uu____9311 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9311
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9310  in
                tc_term uu____9309 typ  in
              (match uu____9302 with
               | (typ1,uu____9327,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9330 = tc_tactic env tau  in
                     match uu____9330 with
                     | (tau1,uu____9344,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1204_9349 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1204_9349.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1204_9349.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____9351 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____9351
                            then
                              let uu____9356 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____9356
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9362 =
                              let uu____9363 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_Syntax_Util.lcomp_of_comp uu____9363
                               in
                            (t, uu____9362,
                              FStar_TypeChecker_Env.trivial_guard)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___1212_9367 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1212_9367.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1212_9367.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1212_9367.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1212_9367.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1212_9367.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1212_9367.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1212_9367.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1212_9367.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1212_9367.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1212_9367.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1212_9367.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1212_9367.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1212_9367.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1212_9367.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1212_9367.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1212_9367.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1212_9367.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1212_9367.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1212_9367.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1212_9367.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1212_9367.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1212_9367.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1212_9367.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1212_9367.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1212_9367.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1212_9367.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1212_9367.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1212_9367.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1212_9367.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1212_9367.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1212_9367.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1212_9367.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1212_9367.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1212_9367.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1212_9367.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1212_9367.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1212_9367.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1212_9367.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1212_9367.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1212_9367.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1212_9367.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1212_9367.FStar_TypeChecker_Env.nbe)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____9390 = tc_tactic env tactic  in
          (match uu____9390 with
           | (tactic1,uu____9404,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____9456 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____9456 with
        | (e2,t,implicits) ->
            let tc =
              let uu____9477 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____9477
              then FStar_Util.Inl t
              else
                (let uu____9486 =
                   let uu____9487 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____9487
                    in
                 FStar_Util.Inr uu____9486)
               in
            let is_data_ctor uu___4_9496 =
              match uu___4_9496 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9501) -> true
              | uu____9509 -> false  in
            let uu____9513 =
              (is_data_ctor dc) &&
                (let uu____9516 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____9516)
               in
            if uu____9513
            then
              let uu____9525 =
                let uu____9531 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9531)  in
              let uu____9535 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____9525 uu____9535
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9553 =
            let uu____9555 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9555
             in
          failwith uu____9553
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____9582 =
            let uu____9587 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____9587  in
          value_check_expected_typ env1 e uu____9582
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____9589 =
            let uu____9602 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____9602 with
            | FStar_Pervasives_Native.None  ->
                let uu____9617 = FStar_Syntax_Util.type_u ()  in
                (match uu____9617 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____9589 with
           | (t,uu____9655,g0) ->
               let uu____9669 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____9669 with
                | (e1,uu____9690,g1) ->
                    let uu____9704 =
                      let uu____9705 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____9705
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____9706 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____9704, uu____9706)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9708 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9718 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____9718)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____9708 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1277_9732 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1277_9732.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1277_9732.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____9735 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____9735 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____9756 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____9756
                       then FStar_Util.Inl t1
                       else
                         (let uu____9765 =
                            let uu____9766 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____9766
                             in
                          FStar_Util.Inr uu____9765)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9768;
             FStar_Syntax_Syntax.vars = uu____9769;_},uu____9770)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9775 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9775
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9785 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9785
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9795;
             FStar_Syntax_Syntax.vars = uu____9796;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____9805 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9805 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____9829 =
                     let uu____9835 =
                       let uu____9837 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____9839 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____9841 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____9837 uu____9839 uu____9841
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____9835)
                      in
                   let uu____9845 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____9829 uu____9845)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____9862 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9867 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9867 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9869 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9869 with
           | ((us,t),range) ->
               ((let uu____9892 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____9892
                 then
                   let uu____9897 =
                     let uu____9899 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____9899  in
                   let uu____9900 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____9902 = FStar_Range.string_of_range range  in
                   let uu____9904 = FStar_Range.string_of_use_range range  in
                   let uu____9906 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____9897 uu____9900 uu____9902 uu____9904 uu____9906
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9914 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9914 us  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____9942 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9942 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____9956 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____9956 with
                | (env2,uu____9970) ->
                    let uu____9975 = tc_binders env2 bs1  in
                    (match uu____9975 with
                     | (bs2,env3,g,us) ->
                         let uu____9994 = tc_comp env3 c1  in
                         (match uu____9994 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1357_10013 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1357_10013.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1357_10013.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g1 =
                                  let uu____10024 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10024
                                   in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 bs2 g1
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u  in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____10040 =
            let uu____10045 =
              let uu____10046 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10046]  in
            FStar_Syntax_Subst.open_term uu____10045 phi  in
          (match uu____10040 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____10074 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10074 with
                | (env2,uu____10088) ->
                    let uu____10093 =
                      let uu____10108 = FStar_List.hd x1  in
                      tc_binder env2 uu____10108  in
                    (match uu____10093 with
                     | (x2,env3,f1,u) ->
                         ((let uu____10144 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____10144
                           then
                             let uu____10147 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____10149 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____10151 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10147 uu____10149 uu____10151
                           else ());
                          (let uu____10158 = FStar_Syntax_Util.type_u ()  in
                           match uu____10158 with
                           | (t_phi,uu____10170) ->
                               let uu____10171 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____10171 with
                                | (phi2,uu____10185,f2) ->
                                    let e1 =
                                      let uu___1395_10190 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1395_10190.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1395_10190.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____10199 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10199
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10227) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____10254 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____10254
            then
              let uu____10257 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1408_10261 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1408_10261.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1408_10261.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10257
            else ());
           (let uu____10277 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____10277 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____10290 ->
          let uu____10291 =
            let uu____10293 = FStar_Syntax_Print.term_to_string top  in
            let uu____10295 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10293
              uu____10295
             in
          failwith uu____10291

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10307 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10309,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10322,FStar_Pervasives_Native.Some msize) ->
            FStar_Syntax_Syntax.tconst
              (match msize with
               | (FStar_Const.Signed ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.int8_lid
               | (FStar_Const.Signed ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.int16_lid
               | (FStar_Const.Signed ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.int32_lid
               | (FStar_Const.Signed ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.int64_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.uint8_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.uint16_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.uint32_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.uint64_lid)
        | FStar_Const.Const_string uu____10340 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10346 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10348 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10349 ->
            let uu____10351 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____10351 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10356 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____10357 =
              let uu____10363 =
                let uu____10365 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10365
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10363)  in
            FStar_Errors.raise_error uu____10357 r
        | FStar_Const.Const_set_range_of  ->
            let uu____10369 =
              let uu____10375 =
                let uu____10377 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10377
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10375)  in
            FStar_Errors.raise_error uu____10369 r
        | FStar_Const.Const_reify  ->
            let uu____10381 =
              let uu____10387 =
                let uu____10389 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10389
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10387)  in
            FStar_Errors.raise_error uu____10381 r
        | FStar_Const.Const_reflect uu____10393 ->
            let uu____10394 =
              let uu____10400 =
                let uu____10402 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10402
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10400)  in
            FStar_Errors.raise_error uu____10394 r
        | uu____10406 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r

and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____10425) ->
          let uu____10434 = FStar_Syntax_Util.type_u ()  in
          (match uu____10434 with
           | (k,u) ->
               let uu____10447 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10447 with
                | (t1,uu____10461,g) ->
                    let uu____10463 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10463, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____10465) ->
          let uu____10474 = FStar_Syntax_Util.type_u ()  in
          (match uu____10474 with
           | (k,u) ->
               let uu____10487 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10487 with
                | (t1,uu____10501,g) ->
                    let uu____10503 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10503, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____10513 =
              let uu____10518 =
                let uu____10519 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____10519 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10518  in
            uu____10513 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____10536 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____10536 with
           | (tc1,uu____10550,f) ->
               let uu____10552 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____10552 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____10602 =
                        let uu____10603 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10603.FStar_Syntax_Syntax.n  in
                      match uu____10602 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10606,us) -> us
                      | uu____10612 -> []  in
                    let uu____10613 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____10613 with
                     | (uu____10636,args1) ->
                         let uu____10662 =
                           let uu____10685 = FStar_List.hd args1  in
                           let uu____10702 = FStar_List.tl args1  in
                           (uu____10685, uu____10702)  in
                         (match uu____10662 with
                          | (res,args2) ->
                              let uu____10783 =
                                let uu____10792 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_10820  ->
                                          match uu___5_10820 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____10828 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____10828 with
                                               | (env1,uu____10840) ->
                                                   let uu____10845 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____10845 with
                                                    | (e1,uu____10857,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____10792
                                  FStar_List.unzip
                                 in
                              (match uu____10783 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1537_10898 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1537_10898.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1537_10898.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____10904 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____10904))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____10914 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____10918 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____10928 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____10928
        | FStar_Syntax_Syntax.U_max us ->
            let uu____10932 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____10932
        | FStar_Syntax_Syntax.U_name x ->
            let uu____10936 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____10936
            then u2
            else
              (let uu____10941 =
                 let uu____10943 =
                   let uu____10945 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____10945 " not found"  in
                 Prims.op_Hat "Universe variable " uu____10943  in
               failwith uu____10941)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____10952 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____10952 FStar_Pervasives_Native.snd
         | uu____10961 -> aux u)

and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail1 msg t =
            let uu____10992 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____10992 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____11081 bs2 bs_expected1 =
              match uu____11081 with
              | (env2,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((let special q1 q2 =
                           match (q1, q2) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta
                              uu____11272),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11273)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11288),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11289)) -> true
                           | uu____11298 -> false  in
                         let uu____11308 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11311 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____11311 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____11308
                         then
                           let uu____11313 =
                             let uu____11319 =
                               let uu____11321 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11321
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11319)
                              in
                           let uu____11325 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____11313 uu____11325
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____11329 =
                           let uu____11336 =
                             let uu____11337 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____11337.FStar_Syntax_Syntax.n  in
                           match uu____11336 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11348 ->
                               ((let uu____11350 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____11350
                                 then
                                   let uu____11353 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11353
                                 else ());
                                (let uu____11358 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____11358 with
                                 | (t,uu____11372,g1_env) ->
                                     let g2_env =
                                       let uu____11375 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____11375
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11380 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____11380 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11383 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____11389 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____11383 uu____11389
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              let uu____11391 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____11391
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____11393 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____11393)))
                            in
                         match uu____11329 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1635_11419 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1635_11419.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1635_11419.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____11442 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____11442
                                in
                             let uu____11445 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____11445 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____11510 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____11510,
                                    subst3))))
                   | (rest,[]) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ([],rest) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1))
               in
            aux (env1, []) bs1 bs_expected  in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____11682 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11692 = tc_binders env1 bs  in
                  match uu____11692 with
                  | (bs1,envbody,g_env,uu____11722) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____11778 =
                    let uu____11779 = FStar_Syntax_Subst.compress t2  in
                    uu____11779.FStar_Syntax_Syntax.n  in
                  match uu____11778 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____11812 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11832 -> failwith "Impossible");
                       (let uu____11842 = tc_binders env1 bs  in
                        match uu____11842 with
                        | (bs1,envbody,g_env,uu____11884) ->
                            let uu____11885 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____11885 with
                             | (envbody1,uu____11923) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____11944;
                         FStar_Syntax_Syntax.pos = uu____11945;
                         FStar_Syntax_Syntax.vars = uu____11946;_},uu____11947)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11991 -> failwith "Impossible");
                       (let uu____12001 = tc_binders env1 bs  in
                        match uu____12001 with
                        | (bs1,envbody,g_env,uu____12043) ->
                            let uu____12044 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12044 with
                             | (envbody1,uu____12082) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____12104) ->
                      let uu____12109 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____12109 with
                       | (uu____12170,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____12247 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____12247 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12392 c_expected2
                               body3 =
                               match uu____12392 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____12506 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____12506,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12523 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12523
                                           in
                                        let uu____12524 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____12524,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____12541 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____12541
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env_bs
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____12607 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____12607 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____12634 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____12634 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____12689 =
                                                           let uu____12716 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12716,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____12689
                                                           c_expected4 body3))
                                           | uu____12739 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env_bs, bs2, guard_env, c,
                                                 body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None
                                              in
                                           (env_bs, bs2, guard_env, c, body4)))
                                in
                             let uu____12768 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____12768 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1761_12833 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1761_12833.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1761_12833.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1761_12833.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1761_12833.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1761_12833.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1761_12833.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1761_12833.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1761_12833.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1761_12833.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1761_12833.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1761_12833.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1761_12833.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1761_12833.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1761_12833.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1761_12833.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1761_12833.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1761_12833.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1761_12833.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1761_12833.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1761_12833.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1761_12833.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1761_12833.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1761_12833.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1761_12833.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1761_12833.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1761_12833.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1761_12833.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1761_12833.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1761_12833.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1761_12833.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1761_12833.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1761_12833.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1761_12833.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1761_12833.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1761_12833.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1761_12833.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1761_12833.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1761_12833.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1761_12833.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1761_12833.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1761_12833.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1761_12833.FStar_TypeChecker_Env.nbe)
                               }  in
                             let uu____12840 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____12906  ->
                                       fun uu____12907  ->
                                         match (uu____12906, uu____12907)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____12998 =
                                               let uu____13005 =
                                                 let uu____13006 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____13006
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____13005 t3  in
                                             (match uu____12998 with
                                              | (t4,uu____13030,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____13043 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1779_13046
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1779_13046.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1779_13046.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____13043 ::
                                                          letrec_binders
                                                    | uu____13047 ->
                                                        letrec_binders
                                                     in
                                                  let uu____13052 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____13052)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____12840 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____13072 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____13072)
                              in
                           let uu____13075 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____13075 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____13151 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____13151 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____13198 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13198))))
                  | uu____13215 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13247 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____13247
                      else
                        (let uu____13251 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____13251 with
                         | (uu____13300,bs1,uu____13302,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____13334 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____13334 with
          | (env1,topt) ->
              ((let uu____13354 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____13354
                then
                  let uu____13357 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13357
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13371 = expected_function_typ1 env1 topt body  in
                match uu____13371 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____13412 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____13412
                      then
                        let uu____13417 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____13420 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13417 uu____13420
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____13426 =
                        let should_check_expected_effect =
                          let uu____13439 =
                            let uu____13446 =
                              let uu____13447 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____13447.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____13446)  in
                          match uu____13439 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13453,(FStar_Util.Inr
                                           expected_c,uu____13455),uu____13456))
                              -> false
                          | uu____13506 -> true  in
                        let uu____13514 =
                          tc_term
                            (let uu___1841_13523 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1841_13523.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1841_13523.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1841_13523.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1841_13523.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1841_13523.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1841_13523.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1841_13523.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1841_13523.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1841_13523.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1841_13523.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1841_13523.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1841_13523.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1841_13523.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1841_13523.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1841_13523.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1841_13523.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1841_13523.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1841_13523.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1841_13523.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1841_13523.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1841_13523.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1841_13523.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1841_13523.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1841_13523.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1841_13523.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1841_13523.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1841_13523.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1841_13523.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1841_13523.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1841_13523.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1841_13523.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1841_13523.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1841_13523.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1841_13523.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1841_13523.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1841_13523.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1841_13523.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1841_13523.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1841_13523.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1841_13523.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1841_13523.FStar_TypeChecker_Env.nbe)
                             }) body1
                           in
                        match uu____13514 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____13550 =
                                let uu____13557 =
                                  let uu____13562 =
                                    FStar_Syntax_Syntax.lcomp_comp cbody  in
                                  (body2, uu____13562)  in
                                check_expected_effect
                                  (let uu___1849_13565 = envbody1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___1849_13565.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___1849_13565.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___1849_13565.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___1849_13565.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___1849_13565.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___1849_13565.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___1849_13565.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___1849_13565.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___1849_13565.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___1849_13565.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___1849_13565.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___1849_13565.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___1849_13565.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___1849_13565.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___1849_13565.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___1849_13565.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___1849_13565.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq = use_eq;
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___1849_13565.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___1849_13565.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___1849_13565.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___1849_13565.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___1849_13565.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___1849_13565.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___1849_13565.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___1849_13565.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___1849_13565.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___1849_13565.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___1849_13565.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___1849_13565.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___1849_13565.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___1849_13565.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___1849_13565.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___1849_13565.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___1849_13565.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___1849_13565.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___1849_13565.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___1849_13565.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___1849_13565.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___1849_13565.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___1849_13565.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___1849_13565.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___1849_13565.FStar_TypeChecker_Env.nbe)
                                   }) c_opt uu____13557
                                 in
                              (match uu____13550 with
                               | (body3,cbody1,guard) ->
                                   let uu____13579 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 guard
                                      in
                                   (body3, cbody1, uu____13579))
                            else
                              (let uu____13586 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____13586, guard_body1))
                         in
                      match uu____13426 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____13611 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13614 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____13614)
                               in
                            if uu____13611
                            then
                              let uu____13617 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____13618 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____13617
                                uu____13618
                            else
                              (let guard =
                                 let uu____13622 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13622
                                  in
                               guard)
                             in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              bs1 guard
                             in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody  in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt)))
                             in
                          let uu____13636 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13657
                                     -> (e, t1, guard1)
                                 | uu____13672 ->
                                     let uu____13673 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____13673 with
                                      | (e1,guard') ->
                                          let uu____13686 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t1, uu____13686)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____13636 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____13697 =
                                 let uu____13702 =
                                   FStar_Syntax_Util.lcomp_of_comp c  in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13702 guard2
                                  in
                               (match uu____13697 with
                                | (c1,g) -> (e1, c1, g)))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
                FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = chead.FStar_Syntax_Syntax.res_typ  in
              (let uu____13751 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____13751
               then
                 let uu____13754 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____13756 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____13754
                   uu____13756
               else ());
              (let monadic_application uu____13834 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____13834 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____13895 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     (match uu____13895 with
                      | (rt,g0) ->
                          let cres1 =
                            let uu___1909_13909 = cres  in
                            {
                              FStar_Syntax_Syntax.eff_name =
                                (uu___1909_13909.FStar_Syntax_Syntax.eff_name);
                              FStar_Syntax_Syntax.res_typ = rt;
                              FStar_Syntax_Syntax.cflags =
                                (uu___1909_13909.FStar_Syntax_Syntax.cflags);
                              FStar_Syntax_Syntax.comp_thunk =
                                (uu___1909_13909.FStar_Syntax_Syntax.comp_thunk)
                            }  in
                          let uu____13910 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____13926 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____13926
                                   in
                                (cres1, g)
                            | uu____13927 ->
                                let g =
                                  let uu____13937 =
                                    let uu____13938 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____13938
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____13937
                                   in
                                let uu____13939 =
                                  let uu____13940 =
                                    let uu____13941 =
                                      let uu____13942 =
                                        FStar_Syntax_Syntax.lcomp_comp cres1
                                         in
                                      FStar_Syntax_Util.arrow bs uu____13942
                                       in
                                    FStar_Syntax_Syntax.mk_Total uu____13941
                                     in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Util.lcomp_of_comp
                                    uu____13940
                                   in
                                (uu____13939, g)
                             in
                          (match uu____13910 with
                           | (cres2,guard1) ->
                               ((let uu____13954 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____13954
                                 then
                                   let uu____13957 =
                                     FStar_Syntax_Print.lcomp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____13957
                                 else ());
                                (let cres3 =
                                   let head_is_pure_and_some_arg_is_effectful
                                     =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1)
                                       &&
                                       (FStar_Util.for_some
                                          (fun uu____13977  ->
                                             match uu____13977 with
                                             | (uu____13987,uu____13988,lc)
                                                 ->
                                                 (let uu____13996 =
                                                    FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                      lc
                                                     in
                                                  Prims.op_Negation
                                                    uu____13996)
                                                   ||
                                                   (FStar_TypeChecker_Util.should_not_inline_lc
                                                      lc)) arg_comps_rev)
                                      in
                                   let term =
                                     FStar_Syntax_Syntax.mk_Tm_app head2
                                       (FStar_List.rev arg_rets_rev)
                                       FStar_Pervasives_Native.None
                                       head2.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____14009 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        cres2)
                                       &&
                                       head_is_pure_and_some_arg_is_effectful
                                      in
                                   if uu____14009
                                   then
                                     ((let uu____14013 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____14013
                                       then
                                         let uu____14016 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: Return inserted in monadic application: %s\n"
                                           uu____14016
                                       else ());
                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                        env term cres2)
                                   else
                                     ((let uu____14024 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____14024
                                       then
                                         let uu____14027 =
                                           FStar_Syntax_Print.term_to_string
                                             term
                                            in
                                         FStar_Util.print1
                                           "(a) Monadic app: No return inserted in monadic application: %s\n"
                                           uu____14027
                                       else ());
                                      cres2)
                                    in
                                 let comp =
                                   FStar_List.fold_left
                                     (fun out_c  ->
                                        fun uu____14058  ->
                                          match uu____14058 with
                                          | ((e,q),x,c) ->
                                              ((let uu____14100 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14100
                                                then
                                                  let uu____14103 =
                                                    match x with
                                                    | FStar_Pervasives_Native.None
                                                         -> "_"
                                                    | FStar_Pervasives_Native.Some
                                                        x1 ->
                                                        FStar_Syntax_Print.bv_to_string
                                                          x1
                                                     in
                                                  let uu____14108 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14110 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print3
                                                    "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                    uu____14103 uu____14108
                                                    uu____14110
                                                else ());
                                               (let uu____14115 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14115
                                                then
                                                  FStar_TypeChecker_Util.bind
                                                    e.FStar_Syntax_Syntax.pos
                                                    env
                                                    (FStar_Pervasives_Native.Some
                                                       e) c (x, out_c)
                                                else
                                                  FStar_TypeChecker_Util.bind
                                                    e.FStar_Syntax_Syntax.pos
                                                    env
                                                    FStar_Pervasives_Native.None
                                                    c (x, out_c)))) cres3
                                     arg_comps_rev
                                    in
                                 let comp1 =
                                   (let uu____14126 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Extreme
                                       in
                                    if uu____14126
                                    then
                                      let uu____14129 =
                                        FStar_Syntax_Print.term_to_string
                                          head2
                                         in
                                      FStar_Util.print1
                                        "(c) Monadic app: Binding head %s\n"
                                        uu____14129
                                    else ());
                                   (let uu____14134 =
                                      FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                        chead1
                                       in
                                    if uu____14134
                                    then
                                      FStar_TypeChecker_Util.bind
                                        head2.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some head2)
                                        chead1
                                        (FStar_Pervasives_Native.None, comp)
                                    else
                                      FStar_TypeChecker_Util.bind
                                        head2.FStar_Syntax_Syntax.pos env
                                        FStar_Pervasives_Native.None chead1
                                        (FStar_Pervasives_Native.None, comp))
                                    in
                                 let comp2 =
                                   FStar_TypeChecker_Util.subst_lcomp subst1
                                     comp1
                                    in
                                 let shortcuts_evaluation_order =
                                   let uu____14146 =
                                     let uu____14147 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____14147.FStar_Syntax_Syntax.n  in
                                   match uu____14146 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.op_And)
                                         ||
                                         (FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.op_Or)
                                   | uu____14152 -> false  in
                                 let app =
                                   if shortcuts_evaluation_order
                                   then
                                     let args1 =
                                       FStar_List.fold_left
                                         (fun args1  ->
                                            fun uu____14175  ->
                                              match uu____14175 with
                                              | (arg,uu____14189,uu____14190)
                                                  -> arg :: args1) []
                                         arg_comps_rev
                                        in
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head2
                                         args1 FStar_Pervasives_Native.None r
                                        in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.res_typ
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic env
                                       app1
                                       comp2.FStar_Syntax_Syntax.eff_name
                                       comp2.FStar_Syntax_Syntax.res_typ
                                   else
                                     (let uu____14201 =
                                        let map_fun uu____14267 =
                                          match uu____14267 with
                                          | ((e,q),uu____14308,c) ->
                                              ((let uu____14331 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.Extreme
                                                   in
                                                if uu____14331
                                                then
                                                  let uu____14334 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e
                                                     in
                                                  let uu____14336 =
                                                    FStar_Syntax_Print.lcomp_to_string
                                                      c
                                                     in
                                                  FStar_Util.print2
                                                    "For arg e=(%s) c=(%s)... "
                                                    uu____14334 uu____14336
                                                else ());
                                               (let uu____14341 =
                                                  FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                    c
                                                   in
                                                if uu____14341
                                                then
                                                  ((let uu____14367 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14367
                                                    then
                                                      FStar_Util.print_string
                                                        "... not lifting\n"
                                                    else ());
                                                   (FStar_Pervasives_Native.None,
                                                     (e, q)))
                                                else
                                                  (let warn_effectful_args =
                                                     (FStar_TypeChecker_Util.must_erase_for_extraction
                                                        env
                                                        chead1.FStar_Syntax_Syntax.res_typ)
                                                       &&
                                                       (let uu____14408 =
                                                          let uu____14410 =
                                                            let uu____14411 =
                                                              FStar_Syntax_Util.un_uinst
                                                                head2
                                                               in
                                                            uu____14411.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____14410
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_fvar
                                                              fv ->
                                                              let uu____14416
                                                                =
                                                                FStar_Parser_Const.psconst
                                                                  "ignore"
                                                                 in
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv
                                                                uu____14416
                                                          | uu____14418 ->
                                                              true
                                                           in
                                                        Prims.op_Negation
                                                          uu____14408)
                                                      in
                                                   if warn_effectful_args
                                                   then
                                                     (let uu____14422 =
                                                        let uu____14428 =
                                                          let uu____14430 =
                                                            FStar_Syntax_Print.term_to_string
                                                              e
                                                             in
                                                          let uu____14432 =
                                                            FStar_Syntax_Print.term_to_string
                                                              head2
                                                             in
                                                          FStar_Util.format3
                                                            "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                            uu____14430
                                                            (c.FStar_Syntax_Syntax.eff_name).FStar_Ident.str
                                                            uu____14432
                                                           in
                                                        (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                          uu____14428)
                                                         in
                                                      FStar_Errors.log_issue
                                                        e.FStar_Syntax_Syntax.pos
                                                        uu____14422)
                                                   else ();
                                                   (let uu____14439 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14439
                                                    then
                                                      FStar_Util.print_string
                                                        "... lifting!\n"
                                                    else ());
                                                   (let x =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    let e1 =
                                                      FStar_TypeChecker_Util.maybe_lift
                                                        env e
                                                        c.FStar_Syntax_Syntax.eff_name
                                                        comp2.FStar_Syntax_Syntax.eff_name
                                                        c.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    let uu____14447 =
                                                      let uu____14456 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      (uu____14456, q)  in
                                                    ((FStar_Pervasives_Native.Some
                                                        (x,
                                                          (c.FStar_Syntax_Syntax.eff_name),
                                                          (c.FStar_Syntax_Syntax.res_typ),
                                                          e1)), uu____14447)))))
                                           in
                                        let uu____14485 =
                                          let uu____14516 =
                                            let uu____14545 =
                                              let uu____14556 =
                                                let uu____14565 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    head2
                                                   in
                                                (uu____14565,
                                                  FStar_Pervasives_Native.None,
                                                  chead1)
                                                 in
                                              uu____14556 :: arg_comps_rev
                                               in
                                            FStar_List.map map_fun
                                              uu____14545
                                             in
                                          FStar_All.pipe_left
                                            FStar_List.split uu____14516
                                           in
                                        match uu____14485 with
                                        | (lifted_args,reverse_args) ->
                                            let uu____14766 =
                                              let uu____14767 =
                                                FStar_List.hd reverse_args
                                                 in
                                              FStar_Pervasives_Native.fst
                                                uu____14767
                                               in
                                            let uu____14788 =
                                              let uu____14789 =
                                                FStar_List.tl reverse_args
                                                 in
                                              FStar_List.rev uu____14789  in
                                            (lifted_args, uu____14766,
                                              uu____14788)
                                         in
                                      match uu____14201 with
                                      | (lifted_args,head3,args1) ->
                                          let app =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head3 args1
                                              FStar_Pervasives_Native.None r
                                             in
                                          let app1 =
                                            FStar_TypeChecker_Util.maybe_lift
                                              env app
                                              cres3.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.res_typ
                                             in
                                          let app2 =
                                            FStar_TypeChecker_Util.maybe_monadic
                                              env app1
                                              comp2.FStar_Syntax_Syntax.eff_name
                                              comp2.FStar_Syntax_Syntax.res_typ
                                             in
                                          let bind_lifted_args e uu___6_14900
                                            =
                                            match uu___6_14900 with
                                            | FStar_Pervasives_Native.None 
                                                -> e
                                            | FStar_Pervasives_Native.Some
                                                (x,m,t,e1) ->
                                                let lb =
                                                  FStar_Syntax_Util.mk_letbinding
                                                    (FStar_Util.Inl x) [] t m
                                                    e1 []
                                                    e1.FStar_Syntax_Syntax.pos
                                                   in
                                                let letbinding =
                                                  let uu____14961 =
                                                    let uu____14968 =
                                                      let uu____14969 =
                                                        let uu____14983 =
                                                          let uu____14986 =
                                                            let uu____14987 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____14987]  in
                                                          FStar_Syntax_Subst.close
                                                            uu____14986 e
                                                           in
                                                        ((false, [lb]),
                                                          uu____14983)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_let
                                                        uu____14969
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____14968
                                                     in
                                                  uu____14961
                                                    FStar_Pervasives_Native.None
                                                    e.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_meta
                                                     (letbinding,
                                                       (FStar_Syntax_Syntax.Meta_monadic
                                                          (m,
                                                            (comp2.FStar_Syntax_Syntax.res_typ)))))
                                                  FStar_Pervasives_Native.None
                                                  e.FStar_Syntax_Syntax.pos
                                             in
                                          FStar_List.fold_left
                                            bind_lifted_args app2 lifted_args)
                                    in
                                 let uu____15039 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     FStar_Pervasives_Native.None env app
                                     comp2 guard1
                                    in
                                 match uu____15039 with
                                 | (comp3,g) ->
                                     ((let uu____15057 =
                                         FStar_TypeChecker_Env.debug env
                                           FStar_Options.Extreme
                                          in
                                       if uu____15057
                                       then
                                         let uu____15060 =
                                           FStar_Syntax_Print.term_to_string
                                             app
                                            in
                                         let uu____15062 =
                                           FStar_Syntax_Print.lcomp_to_string
                                             comp3
                                            in
                                         FStar_Util.print2
                                           "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                           uu____15060 uu____15062
                                       else ());
                                      (app, comp3, g))))))
                  in
               let rec tc_args head_info uu____15143 bs args1 =
                 match uu____15143 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15282))::rest,
                         (uu____15284,FStar_Pervasives_Native.None )::uu____15285)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____15346 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____15346 with
                           | (t1,g_ex) ->
                               let uu____15359 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____15359 with
                                | (varg,uu____15380,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____15408 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____15408)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____15417 =
                                      let uu____15452 =
                                        let uu____15463 =
                                          let uu____15472 =
                                            let uu____15473 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____15473
                                              FStar_Syntax_Util.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15472)
                                           in
                                        uu____15463 :: outargs  in
                                      (subst2, uu____15452, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____15417 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____15519,FStar_Pervasives_Native.None
                                                                 )::uu____15520)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____15582 = tc_tactic env tau1  in
                          (match uu____15582 with
                           | (tau2,uu____15596,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15599 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____15599 with
                                | (t1,g_ex) ->
                                    let uu____15612 =
                                      let uu____15625 =
                                        let uu____15632 =
                                          let uu____15637 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____15637, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____15632
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15625
                                       in
                                    (match uu____15612 with
                                     | (varg,uu____15650,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____15678 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____15678)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____15687 =
                                           let uu____15722 =
                                             let uu____15733 =
                                               let uu____15742 =
                                                 let uu____15743 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____15743
                                                   FStar_Syntax_Util.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____15742)
                                                in
                                             uu____15733 :: outargs  in
                                           (subst2, uu____15722, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____15687 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____15859,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____15860)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____15871),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15872)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____15880),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15881)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____15896 ->
                                let uu____15905 =
                                  let uu____15911 =
                                    let uu____15913 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____15915 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____15917 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____15919 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____15913 uu____15915 uu____15917
                                      uu____15919
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____15911)
                                   in
                                FStar_Errors.raise_error uu____15905
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2119_15926 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2119_15926.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2119_15926.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____15928 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____15928
                             then
                               let uu____15931 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____15933 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15935 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15937 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____15939 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____15931 uu____15933 uu____15935
                                 uu____15937 uu____15939
                             else ());
                            (let uu____15944 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____15944 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2128_15959 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2128_15959.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2128_15959.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2128_15959.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2128_15959.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2128_15959.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2128_15959.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2128_15959.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2128_15959.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2128_15959.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2128_15959.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2128_15959.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2128_15959.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2128_15959.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2128_15959.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2128_15959.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2128_15959.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2128_15959.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2128_15959.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2128_15959.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2128_15959.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2128_15959.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2128_15959.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2128_15959.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2128_15959.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2128_15959.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2128_15959.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2128_15959.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2128_15959.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2128_15959.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2128_15959.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2128_15959.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2128_15959.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2128_15959.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2128_15959.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2128_15959.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2128_15959.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2128_15959.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2128_15959.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2128_15959.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2128_15959.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2128_15959.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2128_15959.FStar_TypeChecker_Env.nbe)
                                   }  in
                                 ((let uu____15961 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____15961
                                   then
                                     let uu____15964 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____15966 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____15968 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____15964 uu____15966 uu____15968
                                   else ());
                                  (let uu____15973 = tc_term env2 e  in
                                   match uu____15973 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____15990 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____15990
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____16013 =
                                           let uu____16016 =
                                             let uu____16025 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16025
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____16016
                                            in
                                         (uu____16013, aq)  in
                                       let uu____16034 =
                                         (FStar_Syntax_Util.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_Syntax_Syntax.eff_name)
                                          in
                                       if uu____16034
                                       then
                                         let subst2 =
                                           let uu____16044 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____16044 e1
                                            in
                                         tc_args head_info
                                           (subst2,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, fvs)
                                           rest rest'
                                       else
                                         tc_args head_info
                                           (subst1,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, (x1 ::
                                             fvs)) rest rest')))))
                      | (uu____16143,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____16179) ->
                          let uu____16230 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____16230 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 solve ghead2 tres =
                                 let tres1 =
                                   let uu____16286 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____16286
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____16317 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____16317 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____16339 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead2,
                                              uu____16339)
                                             in
                                          ((let uu____16341 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____16341
                                            then
                                              FStar_Errors.log_issue
                                                tres1.FStar_Syntax_Syntax.pos
                                                (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                  "Potentially redundant explicit currying of a function type")
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Env.trivial_guard,
                                               []) bs2 args1))
                                 | uu____16388 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____16396 =
                                         let uu____16397 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____16397.FStar_Syntax_Syntax.n
                                          in
                                       match uu____16396 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____16400;
                                              FStar_Syntax_Syntax.index =
                                                uu____16401;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____16403)
                                           -> norm_tres tres4
                                       | uu____16411 -> tres3  in
                                     let uu____16412 = norm_tres tres1  in
                                     aux true solve ghead2 uu____16412
                                 | uu____16414 when Prims.op_Negation solve
                                     ->
                                     let ghead3 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env ghead2
                                        in
                                     aux norm1 true ghead3 tres1
                                 | uu____16417 ->
                                     let uu____16418 =
                                       let uu____16424 =
                                         let uu____16426 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____16428 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         let uu____16430 =
                                           FStar_Syntax_Print.term_to_string
                                             tres1
                                            in
                                         FStar_Util.format3
                                           "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                           uu____16426 uu____16428
                                           uu____16430
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____16424)
                                        in
                                     let uu____16434 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____16418
                                       uu____16434
                                  in
                               aux false false ghead1
                                 chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf guard =
                 let uu____16464 =
                   let uu____16465 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____16465.FStar_Syntax_Syntax.n  in
                 match uu____16464 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16474 ->
                     let uu____16487 =
                       FStar_List.fold_right
                         (fun uu____16518  ->
                            fun uu____16519  ->
                              match uu____16519 with
                              | (bs,guard1) ->
                                  let uu____16546 =
                                    let uu____16559 =
                                      let uu____16560 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16560
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16559
                                     in
                                  (match uu____16546 with
                                   | (t,uu____16577,g) ->
                                       let uu____16591 =
                                         let uu____16594 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16594 :: bs  in
                                       let uu____16595 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16591, uu____16595))) args
                         ([], guard)
                        in
                     (match uu____16487 with
                      | (bs,guard1) ->
                          let uu____16612 =
                            let uu____16619 =
                              let uu____16632 =
                                let uu____16633 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16633
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16632
                               in
                            match uu____16619 with
                            | (t,uu____16650,g) ->
                                let uu____16664 = FStar_Options.ml_ish ()  in
                                if uu____16664
                                then
                                  let uu____16673 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16676 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16673, uu____16676)
                                else
                                  (let uu____16681 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16684 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16681, uu____16684))
                             in
                          (match uu____16612 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16703 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16703
                                 then
                                   let uu____16707 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16709 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16711 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16707 uu____16709 uu____16711
                                 else ());
                                (let g =
                                   let uu____16717 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16717
                                    in
                                 let uu____16718 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16718))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____16719;
                        FStar_Syntax_Syntax.pos = uu____16720;
                        FStar_Syntax_Syntax.vars = uu____16721;_},uu____16722)
                     ->
                     let uu____16759 =
                       FStar_List.fold_right
                         (fun uu____16790  ->
                            fun uu____16791  ->
                              match uu____16791 with
                              | (bs,guard1) ->
                                  let uu____16818 =
                                    let uu____16831 =
                                      let uu____16832 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16832
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16831
                                     in
                                  (match uu____16818 with
                                   | (t,uu____16849,g) ->
                                       let uu____16863 =
                                         let uu____16866 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16866 :: bs  in
                                       let uu____16867 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16863, uu____16867))) args
                         ([], guard)
                        in
                     (match uu____16759 with
                      | (bs,guard1) ->
                          let uu____16884 =
                            let uu____16891 =
                              let uu____16904 =
                                let uu____16905 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16905
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16904
                               in
                            match uu____16891 with
                            | (t,uu____16922,g) ->
                                let uu____16936 = FStar_Options.ml_ish ()  in
                                if uu____16936
                                then
                                  let uu____16945 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16948 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16945, uu____16948)
                                else
                                  (let uu____16953 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16956 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16953, uu____16956))
                             in
                          (match uu____16884 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16975 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16975
                                 then
                                   let uu____16979 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16981 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16983 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16979 uu____16981 uu____16983
                                 else ());
                                (let g =
                                   let uu____16989 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16989
                                    in
                                 let uu____16990 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16990))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____17013 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____17013 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____17035 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____17035)  in
                          ((let uu____17037 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____17037
                            then
                              let uu____17040 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17042 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____17044 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____17047 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17040 uu____17042 uu____17044
                                uu____17047
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____17093) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____17099,uu____17100) ->
                     check_function_app t guard
                 | uu____17141 ->
                     let uu____17142 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____17142
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
                FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____17225 =
                    FStar_List.fold_left2
                      (fun uu____17294  ->
                         fun uu____17295  ->
                           fun uu____17296  ->
                             match (uu____17294, uu____17295, uu____17296)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____17449 =
                                     let uu____17451 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____17451 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____17449
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17457 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____17457 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____17486 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17486 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17491 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____17491)
                                              &&
                                              (let uu____17494 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____17494))
                                          in
                                       let uu____17496 =
                                         let uu____17507 =
                                           let uu____17518 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____17518]  in
                                         FStar_List.append seen uu____17507
                                          in
                                       let uu____17551 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____17496, uu____17551, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____17225 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____17619 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____17619
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____17622 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____17622 with | (c2,g) -> (e, c2, g)))
              | uu____17639 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
          FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun pat_t  ->
      fun p0  ->
        let fail1 msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p
           in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t  in
            let uu____17730 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17730 with
            | (head1,args) ->
                let uu____17773 =
                  let uu____17774 = FStar_Syntax_Subst.compress head1  in
                  uu____17774.FStar_Syntax_Syntax.n  in
                (match uu____17773 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____17778;
                        FStar_Syntax_Syntax.vars = uu____17779;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____17786 ->
                     if norm1
                     then t1
                     else
                       (let uu____17790 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____17790))
          
          and unfold_once t f us args =
            let uu____17808 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____17808
            then t
            else
              (let uu____17813 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____17813 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____17833 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____17833 with
                    | (uu____17838,head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            FStar_Pervasives_Native.None
                            t.FStar_Syntax_Syntax.pos
                           in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t'
                           in
                        aux false t'1))
           in
          let uu____17845 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____17845  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____17864 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____17864
           then
             let uu____17869 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____17871 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____17869 uu____17871
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____17891 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____17893 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____17891 uu____17893 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____17897 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____17897 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____17941 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____17941 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____17942;
                    FStar_Syntax_Syntax.pos = uu____17943;
                    FStar_Syntax_Syntax.vars = uu____17944;_} ->
                    let uu____17947 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____17947 with
                     | (head_p,args_p) ->
                         let uu____17990 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____17990
                         then
                           let uu____17993 =
                             let uu____17994 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____17994.FStar_Syntax_Syntax.n  in
                           (match uu____17993 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____17999 =
                                    let uu____18001 =
                                      let uu____18003 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18003
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18001
                                     in
                                  if uu____17999
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____18031 =
                                    let uu____18056 =
                                      let uu____18060 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18060
                                       in
                                    match uu____18056 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____18109 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____18109 with
                                         | (params_p,uu____18167) ->
                                             let uu____18208 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____18208 with
                                              | (params_s,uu____18266) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____18031 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____18395  ->
                                             fun uu____18396  ->
                                               match (uu____18395,
                                                       uu____18396)
                                               with
                                               | ((p,uu____18430),(s,uu____18432))
                                                   ->
                                                   let uu____18465 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____18465 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____18468 =
                                                          let uu____18470 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____18472 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18470
                                                            uu____18472
                                                           in
                                                        fail2 uu____18468
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____18477 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18481 =
                              let uu____18483 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____18485 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18483 uu____18485
                               in
                            fail2 uu____18481))
                | uu____18488 ->
                    let uu____18489 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____18489 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____18526 = FStar_Syntax_Util.head_and_args e  in
          match uu____18526 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18590 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18590 with
                    | (us,t_f) ->
                        let uu____18607 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____18607 with
                         | (formals,t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____18736 formals1 args1 =
                                 match uu____18736 with
                                 | (subst1,args_out,bvs,guard) ->
                                     (match (formals1, args1) with
                                      | ([],[]) ->
                                          let head2 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head1 us
                                             in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head2 args_out
                                              FStar_Pervasives_Native.None
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____18881 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____18881, bvs, guard)
                                      | ((f1,uu____18887)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____18945 =
                                            let uu____18966 =
                                              let uu____18967 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____18967.FStar_Syntax_Syntax.n
                                               in
                                            match uu____18966 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2428_18992 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2428_18992.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2428_18992.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  }  in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1
                                                   in
                                                let subst2 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst1  in
                                                ((a1, imp_a), subst2,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____19015 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____19029 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____19029 with
                                                 | (a1,uu____19057,g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g
                                                        in
                                                     let subst2 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst1  in
                                                     ((a1, imp_a), subst2,
                                                       bvs, g1))
                                            | uu____19081 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____18945 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____19143 =
                                                 let uu____19166 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19166)
                                                  in
                                               aux uu____19143 formals2 args2)
                                      | uu____19205 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19261 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____19310 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19310
           then
             let uu____19315 = FStar_Syntax_Print.pat_to_string p  in
             let uu____19317 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19315
               uu____19317
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19332 ->
               let uu____19339 =
                 let uu____19341 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19341
                  in
               failwith uu____19339
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2460_19356 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2460_19356.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2460_19356.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19357 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19357,
                 (let uu___2463_19361 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2463_19361.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2467_19364 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2467_19364.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2467_19364.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19365 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19365,
                 (let uu___2470_19369 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2470_19369.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____19370 ->
               let uu____19371 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____19371 with
                | (uu____19393,e_c,uu____19395,uu____19396) ->
                    let uu____19401 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____19401 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____19424 =
                              let uu____19426 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_Syntax_Syntax.res_typ expected_t
                                 in
                              Prims.op_Negation uu____19426  in
                            if uu____19424
                            then
                              let uu____19429 =
                                let uu____19431 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____19433 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____19431 uu____19433
                                 in
                              fail1 uu____19429
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____19491  ->
                        match uu____19491 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____19521
                                 -> (p1, b)
                             | uu____19531 ->
                                 let uu____19532 =
                                   let uu____19535 =
                                     let uu____19536 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____19536
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____19535
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____19532, b))) sub_pats
                    in
                 let uu___2498_19540 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2498_19540.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____19585  ->
                         match uu____19585 with
                         | (x,uu____19595) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____19603
                                  -> false
                              | uu____19611 -> true)))
                  in
               let uu____19613 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____19613 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____19650 =
                          let uu____19652 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____19654 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____19656 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____19663 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____19652 uu____19654 uu____19656 uu____19663
                           in
                        failwith uu____19650)
                     else ();
                     (let uu____19668 =
                        let uu____19677 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____19677 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard) ->
                            let g' =
                              let uu____19705 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____19705  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____19708 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____19708
                              then
                                let uu____19713 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____19715 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____19717 =
                                  let uu____19719 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____19727 =
                                           let uu____19729 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____19731 =
                                             let uu____19733 =
                                               let uu____19735 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____19735 ")"
                                                in
                                             Prims.op_Hat " : " uu____19733
                                              in
                                           Prims.op_Hat uu____19729
                                             uu____19731
                                            in
                                         Prims.op_Hat "(" uu____19727)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____19719
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____19713 uu____19715 uu____19717
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1))
                         in
                      match uu____19668 with
                      | (simple_pat_e1,simple_bvs1,g1) ->
                          let uu____19767 =
                            let uu____19789 =
                              let uu____19811 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], uu____19811)  in
                            FStar_List.fold_left2
                              (fun uu____19872  ->
                                 fun uu____19873  ->
                                   fun x  ->
                                     match (uu____19872, uu____19873) with
                                     | ((env2,bvs,pats,subst1,g),(p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____20006 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____20006 with
                                          | (bvs_p,e_p,p2,g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let uu____20047 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____20047))) uu____19789
                              sub_pats1 simple_bvs1
                             in
                          (match uu____19767 with
                           | (_env,bvs,checked_sub_pats,subst1,g) ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst1
                                   simple_pat_e1
                                  in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd1,b)::simple_pats1 ->
                                       (match hd1.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x,e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst1
                                                e
                                               in
                                            let hd2 =
                                              let uu___2570_20259 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2570_20259.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____20264 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____20264
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____20308)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____20345 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____20345
                                             | uu____20365 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____20391 ->
                                            failwith
                                              "Impossible: expected a simple pattern")
                                    in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1,simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats
                                        in
                                     let uu___2591_20434 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2591_20434.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____20446 -> failwith "Impossible"  in
                               let uu____20450 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, pat_e, uu____20450, g))))))
           in
        (let uu____20454 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____20454
         then
           let uu____20459 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____20459
         else ());
        (let uu____20464 =
           let uu____20475 =
             let uu___2596_20476 =
               let uu____20477 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____20477 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2596_20476.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2596_20476.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2596_20476.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2596_20476.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2596_20476.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2596_20476.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2596_20476.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2596_20476.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2596_20476.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2596_20476.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2596_20476.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2596_20476.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2596_20476.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2596_20476.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2596_20476.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2596_20476.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2596_20476.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2596_20476.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2596_20476.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2596_20476.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2596_20476.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2596_20476.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2596_20476.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2596_20476.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2596_20476.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2596_20476.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2596_20476.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2596_20476.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2596_20476.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2596_20476.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2596_20476.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2596_20476.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2596_20476.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2596_20476.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2596_20476.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2596_20476.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2596_20476.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2596_20476.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2596_20476.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2596_20476.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2596_20476.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2596_20476.FStar_TypeChecker_Env.nbe)
             }  in
           let uu____20493 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____20475 uu____20493 pat_t  in
         match uu____20464 with
         | (bvs,pat_e,pat,g) ->
             ((let uu____20517 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____20517
               then
                 let uu____20522 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____20524 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____20522
                   uu____20524
               else ());
              (let uu____20529 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____20530 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, uu____20529, pat_e, uu____20530, g))))

and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) *
          FStar_Syntax_Syntax.term * FStar_Ident.lident *
          FStar_Syntax_Syntax.cflag Prims.list *
          (Prims.bool -> FStar_Syntax_Syntax.lcomp) *
          FStar_TypeChecker_Env.guard_t))
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____20576 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____20576 with
        | (pattern,when_clause,branch_exp) ->
            let uu____20622 = branch1  in
            (match uu____20622 with
             | (cpat,uu____20664,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____20686 =
                   let uu____20693 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____20693
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____20686 with
                  | (scrutinee_env,uu____20727) ->
                      let uu____20732 = tc_pat env pat_t pattern  in
                      (match uu____20732 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp,guard_pat)
                           ->
                           let uu____20783 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____20813 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____20813
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____20836 =
                                      let uu____20843 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____20843 e  in
                                    match uu____20836 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____20783 with
                            | (when_clause1,g_when) ->
                                let uu____20897 = tc_term pat_env branch_exp
                                   in
                                (match uu____20897 with
                                 | (branch_exp1,c,g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____20953 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _20964  ->
                                                  FStar_Pervasives_Native.Some
                                                    _20964) uu____20953
                                          in
                                       let uu____20965 =
                                         let eqs =
                                           let uu____20987 =
                                             let uu____20989 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____20989
                                              in
                                           if uu____20987
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____21005 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____21020 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____21023 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____21026 ->
                                                  let uu____21027 =
                                                    let uu____21030 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____21030 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____21027)
                                            in
                                         let uu____21033 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch
                                            in
                                         match uu____21033 with
                                         | (c1,g_branch1) ->
                                             let uu____21060 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____21077 when
                                                   let uu____21090 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____21090
                                                   -> (c1, g_when)
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) -> (c1, g_when)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let gf =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       gf
                                                      in
                                                   let uu____21121 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____21122 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____21121, uu____21122)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____21143 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____21143
                                                      in
                                                   let uu____21144 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____21145 =
                                                     let uu____21146 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____21146 g_when
                                                      in
                                                   (uu____21144, uu____21145)
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_w =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       w
                                                      in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       g_w
                                                      in
                                                   let uu____21164 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____21164, g_when)
                                                in
                                             (match uu____21060 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return1 =
                                                    let c_weak1 =
                                                      let uu____21207 =
                                                        should_return1 &&
                                                          (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____21207
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____21212 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  let uu____21213 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1
                                                     in
                                                  ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                    (c_weak.FStar_Syntax_Syntax.cflags),
                                                    maybe_return_c_weak,
                                                    uu____21212, uu____21213))
                                          in
                                       match uu____20965 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____21264 =
                                               let uu____21266 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____21266
                                                in
                                             if uu____21264
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pattern2
                                                  pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____21320 =
                                                      let uu____21328 =
                                                        FStar_TypeChecker_Env.typ_of_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      FStar_TypeChecker_Env.datacons_of_typ
                                                        env uu____21328
                                                       in
                                                    match uu____21320 with
                                                    | (is_induc,datacons) ->
                                                        if
                                                          (Prims.op_Negation
                                                             is_induc)
                                                            ||
                                                            ((FStar_List.length
                                                                datacons)
                                                               >
                                                               (Prims.parse_int "1"))
                                                        then
                                                          let discriminator =
                                                            FStar_Syntax_Util.mk_discriminator
                                                              f.FStar_Syntax_Syntax.v
                                                             in
                                                          let uu____21344 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              discriminator
                                                             in
                                                          (match uu____21344
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> []
                                                           | uu____21365 ->
                                                               let disc =
                                                                 FStar_Syntax_Syntax.fvar
                                                                   discriminator
                                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let disc1 =
                                                                 let uu____21381
                                                                   =
                                                                   let uu____21386
                                                                    =
                                                                    let uu____21387
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                    [uu____21387]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____21386
                                                                    in
                                                                 uu____21381
                                                                   FStar_Pervasives_Native.None
                                                                   scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let uu____21412
                                                                 =
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   FStar_Syntax_Syntax.U_zero
                                                                   FStar_Syntax_Util.t_bool
                                                                   disc1
                                                                   FStar_Syntax_Util.exp_true_bool
                                                                  in
                                                               [uu____21412])
                                                        else []
                                                     in
                                                  let fail1 uu____21420 =
                                                    let uu____21421 =
                                                      let uu____21423 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____21425 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____21427 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____21423
                                                        uu____21425
                                                        uu____21427
                                                       in
                                                    failwith uu____21421  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____21442) ->
                                                        head_constructor t1
                                                    | uu____21447 -> fail1 ()
                                                     in
                                                  let force_scrutinee
                                                    uu____21453 =
                                                    match scrutinee_tm1 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____21454 =
                                                          let uu____21456 =
                                                            FStar_Range.string_of_range
                                                              pattern2.FStar_Syntax_Syntax.p
                                                             in
                                                          let uu____21458 =
                                                            FStar_Syntax_Print.pat_to_string
                                                              pattern2
                                                             in
                                                          FStar_Util.format2
                                                            "Impossible (%s): scrutinee of match is not defined %s"
                                                            uu____21456
                                                            uu____21458
                                                           in
                                                        failwith uu____21454
                                                    | FStar_Pervasives_Native.Some
                                                        t -> t
                                                     in
                                                  let pat_exp2 =
                                                    let uu____21465 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____21465
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match ((pattern2.FStar_Syntax_Syntax.v),
                                                          (pat_exp2.FStar_Syntax_Syntax.n))
                                                  with
                                                  | (uu____21470,FStar_Syntax_Syntax.Tm_name
                                                     uu____21471) -> []
                                                  | (uu____21472,FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     )) -> []
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     _c,FStar_Syntax_Syntax.Tm_constant
                                                     c1) ->
                                                      let uu____21475 =
                                                        let uu____21476 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        let uu____21477 =
                                                          force_scrutinee ()
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____21476
                                                          uu____21477
                                                          pat_exp2
                                                         in
                                                      [uu____21475]
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     (FStar_Const.Const_int
                                                     (uu____21478,FStar_Pervasives_Native.Some
                                                      uu____21479)),uu____21480)
                                                      ->
                                                      let uu____21497 =
                                                        let uu____21504 =
                                                          FStar_TypeChecker_Env.clear_expected_typ
                                                            env
                                                           in
                                                        match uu____21504
                                                        with
                                                        | (env1,uu____21518)
                                                            ->
                                                            env1.FStar_TypeChecker_Env.type_of
                                                              env1 pat_exp2
                                                         in
                                                      (match uu____21497 with
                                                       | (uu____21525,t,uu____21527)
                                                           ->
                                                           let uu____21528 =
                                                             let uu____21529
                                                               =
                                                               force_scrutinee
                                                                 ()
                                                                in
                                                             FStar_Syntax_Util.mk_eq2
                                                               FStar_Syntax_Syntax.U_zero
                                                               t uu____21529
                                                               pat_exp2
                                                              in
                                                           [uu____21528])
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21530,[]),FStar_Syntax_Syntax.Tm_uinst
                                                     uu____21531) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21555 =
                                                        let uu____21557 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21557
                                                         in
                                                      if uu____21555
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21567 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21570 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21567
                                                           uu____21570)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21573,[]),FStar_Syntax_Syntax.Tm_fvar
                                                     uu____21574) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21592 =
                                                        let uu____21594 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21594
                                                         in
                                                      if uu____21592
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21604 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21607 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21604
                                                           uu____21607)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21610,pat_args),FStar_Syntax_Syntax.Tm_app
                                                     (head1,args)) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____21657 =
                                                        (let uu____21661 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____21661)
                                                          ||
                                                          ((FStar_List.length
                                                              pat_args)
                                                             <>
                                                             (FStar_List.length
                                                                args))
                                                         in
                                                      if uu____21657
                                                      then
                                                        failwith
                                                          "Impossible: application patterns must be fully-applied data constructors"
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____21689 =
                                                             let uu____21694
                                                               =
                                                               FStar_List.zip
                                                                 pat_args
                                                                 args
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____21694
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____21780
                                                                     ->
                                                                    match uu____21780
                                                                    with
                                                                    | 
                                                                    ((pi,uu____21802),
                                                                    (ei,uu____21804))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____21832
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____21832
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____21853
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____21865
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____21865
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    (Prims.parse_int "1"))
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____21867
                                                                    =
                                                                    let uu____21868
                                                                    =
                                                                    let uu____21873
                                                                    =
                                                                    let uu____21874
                                                                    =
                                                                    let uu____21883
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____21883
                                                                     in
                                                                    [uu____21874]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____21873
                                                                     in
                                                                    uu____21868
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____21867
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____21689
                                                             FStar_List.flatten
                                                            in
                                                         let uu____21906 =
                                                           let uu____21909 =
                                                             force_scrutinee
                                                               ()
                                                              in
                                                           discriminate
                                                             uu____21909 f
                                                            in
                                                         FStar_List.append
                                                           uu____21906
                                                           sub_term_guards)
                                                  | (FStar_Syntax_Syntax.Pat_dot_term
                                                     uu____21912,uu____21913)
                                                      -> []
                                                  | uu____21920 ->
                                                      let uu____21925 =
                                                        let uu____21927 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            pattern2
                                                           in
                                                        let uu____21929 =
                                                          FStar_Syntax_Print.term_to_string
                                                            pat_exp2
                                                           in
                                                        FStar_Util.format2
                                                          "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                          uu____21927
                                                          uu____21929
                                                         in
                                                      failwith uu____21925
                                                   in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pattern2 pat
                                                  =
                                                  let uu____21958 =
                                                    let uu____21960 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____21960
                                                     in
                                                  if uu____21958
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____21966 =
                                                         build_branch_guard
                                                           scrutinee_tm1
                                                           pattern2 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____21966
                                                        in
                                                     let uu____21975 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____21975 with
                                                     | (k,uu____21981) ->
                                                         let uu____21982 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____21982
                                                          with
                                                          | (t1,uu____21990,uu____21991)
                                                              -> t1))
                                                   in
                                                let branch_guard =
                                                  build_and_check_branch_guard
                                                    (FStar_Pervasives_Native.Some
                                                       scrutinee_tm) pattern1
                                                    norm_pat_exp
                                                   in
                                                let branch_guard1 =
                                                  match when_condition with
                                                  | FStar_Pervasives_Native.None
                                                       -> branch_guard
                                                  | FStar_Pervasives_Native.Some
                                                      w ->
                                                      FStar_Syntax_Util.mk_conj
                                                        branch_guard w
                                                   in
                                                branch_guard1)
                                              in
                                           let guard =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_when1 g_branch1
                                              in
                                           ((let uu____22003 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____22003
                                             then
                                               let uu____22006 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____22006
                                             else ());
                                            (let uu____22012 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____22029 =
                                               let uu____22030 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____22030 guard
                                                in
                                             (uu____22012, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____22029))))))))))

and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____22077 = check_let_bound_def true env1 lb  in
          (match uu____22077 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____22103 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____22125 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____22125, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____22131 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____22131
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____22132 =
                      let uu____22145 =
                        let uu____22160 =
                          let uu____22169 =
                            let uu____22176 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____22176)
                             in
                          [uu____22169]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____22160
                         in
                      FStar_List.hd uu____22145  in
                    match uu____22132 with
                    | (uu____22212,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta;
                               FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                               FStar_TypeChecker_Env.CompressUvars;
                               FStar_TypeChecker_Env.NoFullNorm;
                               FStar_TypeChecker_Env.Exclude
                                 FStar_TypeChecker_Env.Zeta] env1)
                           in
                        let g13 =
                          FStar_TypeChecker_Env.abstract_guard_n gvs g12  in
                        let uu____22226 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____22226))
                  in
               (match uu____22103 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____22243 =
                      let uu____22252 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____22252
                      then
                        let uu____22263 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____22263 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____22297 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____22297
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____22298 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____22298, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____22313 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____22313
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____22319 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____22319
                            then e2
                            else
                              ((let uu____22327 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____22327
                                  FStar_TypeChecker_Err.top_level_effect);
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect)))
                                 FStar_Pervasives_Native.None
                                 e2.FStar_Syntax_Syntax.pos)
                             in
                          (e21, c)))
                       in
                    (match uu____22243 with
                     | (e21,c12) ->
                         ((let uu____22351 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____22351
                           then
                             let uu____22354 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____22354
                           else ());
                          (let e12 =
                             let uu____22360 = FStar_Options.tcnorm ()  in
                             if uu____22360
                             then
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.UnfoldAttr
                                    [FStar_Parser_Const.tcnorm_attr];
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1 e11
                             else e11  in
                           (let uu____22366 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____22366
                            then
                              let uu____22369 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____22369
                            else ());
                           (let cres =
                              FStar_TypeChecker_Env.null_wp_for_eff env1
                                (FStar_Syntax_Util.comp_effect_name c12)
                                FStar_Syntax_Syntax.U_zero
                                FStar_Syntax_Syntax.t_unit
                               in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars2
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos
                               in
                            let uu____22378 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____22392 =
                              FStar_Syntax_Util.lcomp_of_comp cres  in
                            (uu____22378, uu____22392,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____22393 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____22404 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____22404
        then
          let universe_of_binders bs =
            let uu____22431 =
              FStar_List.fold_left
                (fun uu____22456  ->
                   fun b  ->
                     match uu____22456 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____22431 with | (uu____22504,us) -> FStar_List.rev us
             in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders
             in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2

and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___2908_22540 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___2908_22540.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___2908_22540.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___2908_22540.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___2908_22540.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___2908_22540.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___2908_22540.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___2908_22540.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___2908_22540.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___2908_22540.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___2908_22540.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___2908_22540.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___2908_22540.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___2908_22540.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___2908_22540.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___2908_22540.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___2908_22540.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___2908_22540.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___2908_22540.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___2908_22540.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___2908_22540.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___2908_22540.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___2908_22540.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___2908_22540.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___2908_22540.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___2908_22540.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___2908_22540.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___2908_22540.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___2908_22540.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___2908_22540.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___2908_22540.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___2908_22540.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___2908_22540.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___2908_22540.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___2908_22540.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___2908_22540.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___2908_22540.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___2908_22540.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___2908_22540.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___2908_22540.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___2908_22540.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___2908_22540.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___2908_22540.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____22542 =
            let uu____22554 =
              let uu____22555 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____22555 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____22554 lb  in
          (match uu____22542 with
           | (e1,uu____22578,c1,g1,annotated) ->
               let pure_or_ghost =
                 FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs
                  in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____22592 =
                     let uu____22598 =
                       let uu____22600 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____22602 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____22600 uu____22602
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____22598)
                      in
                   FStar_Errors.raise_error uu____22592
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____22613 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_Syntax_Syntax.res_typ)
                      in
                   if uu____22613
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___2923_22625 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2923_22625.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2923_22625.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____22626 =
                   let uu____22631 =
                     let uu____22632 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____22632]  in
                   FStar_Syntax_Subst.open_term uu____22631 e2  in
                 match uu____22626 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____22676 = tc_term env_x e21  in
                     (match uu____22676 with
                      | (e22,c2,g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_Syntax_Syntax.res_typ c2
                             in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21)
                             in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ
                             in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.eff_name
                              c21.FStar_Syntax_Syntax.res_typ
                             in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_Syntax_Syntax.res_typ
                              cres.FStar_Syntax_Syntax.eff_name e11 attrs
                              lb.FStar_Syntax_Syntax.lbpos
                             in
                          let e3 =
                            let uu____22702 =
                              let uu____22709 =
                                let uu____22710 =
                                  let uu____22724 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____22724)  in
                                FStar_Syntax_Syntax.Tm_let uu____22710  in
                              FStar_Syntax_Syntax.mk uu____22709  in
                            uu____22702 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____22742 =
                              let uu____22743 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____22744 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____22743
                                c1.FStar_Syntax_Syntax.res_typ uu____22744
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _22745  ->
                                 FStar_TypeChecker_Common.NonTrivial _22745)
                              uu____22742
                             in
                          let g21 =
                            let uu____22747 =
                              let uu____22748 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____22748 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____22747
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____22751 =
                            let uu____22753 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____22753  in
                          if uu____22751
                          then
                            let tt =
                              let uu____22764 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____22764
                                FStar_Option.get
                               in
                            ((let uu____22770 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____22770
                              then
                                let uu____22775 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____22777 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____22775 uu____22777
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____22784 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             match uu____22784 with
                             | (t,g_ex) ->
                                 ((let uu____22798 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____22798
                                   then
                                     let uu____22803 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_Syntax_Syntax.res_typ
                                        in
                                     let uu____22805 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____22803 uu____22805
                                   else ());
                                  (let uu____22810 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___2956_22812 = cres  in
                                      {
                                        FStar_Syntax_Syntax.eff_name =
                                          (uu___2956_22812.FStar_Syntax_Syntax.eff_name);
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          (uu___2956_22812.FStar_Syntax_Syntax.cflags);
                                        FStar_Syntax_Syntax.comp_thunk =
                                          (uu___2956_22812.FStar_Syntax_Syntax.comp_thunk)
                                      }), uu____22810))))))))
      | uu____22813 ->
          failwith "Impossible (inner let with more than one lb)"

and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____22849 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____22849 with
           | (lbs1,e21) ->
               let uu____22868 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____22868 with
                | (env0,topt) ->
                    let uu____22887 = build_let_rec_env true env0 lbs1  in
                    (match uu____22887 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____22910 = check_let_recs rec_env lbs2  in
                         (match uu____22910 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____22930 =
                                  let uu____22931 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____22931
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____22930
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____22937 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____22937
                                  (fun _22954  ->
                                     FStar_Pervasives_Native.Some _22954)
                                 in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef
                                             in
                                          if
                                            lb.FStar_Syntax_Syntax.lbunivs =
                                              []
                                          then lb
                                          else
                                            FStar_Syntax_Util.close_univs_and_mk_letbinding
                                              all_lb_names
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef
                                              lb.FStar_Syntax_Syntax.lbattrs
                                              lb.FStar_Syntax_Syntax.lbpos))
                                else
                                  (let ecs =
                                     let uu____22991 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____23025 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____23025)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____22991
                                      in
                                   FStar_List.map2
                                     (fun uu____23060  ->
                                        fun lb  ->
                                          match uu____23060 with
                                          | (x,uvs,e,c,gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3)
                                 in
                              let cres =
                                let uu____23108 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____23108
                                 in
                              let uu____23109 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____23109 with
                               | (lbs5,e22) ->
                                   ((let uu____23129 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____23129
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____23130 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____23130, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____23144 -> failwith "Impossible"

and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____23180 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____23180 with
           | (lbs1,e21) ->
               let uu____23199 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____23199 with
                | (env0,topt) ->
                    let uu____23218 = build_let_rec_env false env0 lbs1  in
                    (match uu____23218 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____23241 =
                           let uu____23248 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____23248
                             (fun uu____23271  ->
                                match uu____23271 with
                                | (lbs3,g) ->
                                    let uu____23290 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____23290))
                            in
                         (match uu____23241 with
                          | (lbs3,g_lbs) ->
                              let uu____23305 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3031_23328 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3031_23328.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3031_23328.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3034_23330 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3034_23330.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3034_23330.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3034_23330.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3034_23330.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3034_23330.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3034_23330.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp))
                                             in
                                          (env3, lb1)) env1)
                                 in
                              (match uu____23305 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____23357 = tc_term env2 e21  in
                                   (match uu____23357 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb  ->
                                               fun cres1  ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres
                                           in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1
                                           in
                                        let cres3 =
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                           in
                                        let guard =
                                          let uu____23381 =
                                            let uu____23382 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____23382 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____23381
                                           in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres3
                                           in
                                        let tres =
                                          norm env2
                                            cres4.FStar_Syntax_Syntax.res_typ
                                           in
                                        let cres5 =
                                          let uu___3055_23392 = cres4  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___3055_23392.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___3055_23392.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___3055_23392.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____23400 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____23400))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____23401 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____23401 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____23442 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____23443 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____23443 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3071_23457
                                                           = cres5  in
                                                         {
                                                           FStar_Syntax_Syntax.eff_name
                                                             =
                                                             (uu___3071_23457.FStar_Syntax_Syntax.eff_name);
                                                           FStar_Syntax_Syntax.res_typ
                                                             = tres1;
                                                           FStar_Syntax_Syntax.cflags
                                                             =
                                                             (uu___3071_23457.FStar_Syntax_Syntax.cflags);
                                                           FStar_Syntax_Syntax.comp_thunk
                                                             =
                                                             (uu___3071_23457.FStar_Syntax_Syntax.comp_thunk)
                                                         }  in
                                                       let uu____23458 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____23458))))))))))
      | uu____23459 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Env.guard_t))
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____23507 = FStar_Options.ml_ish ()  in
          if uu____23507
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____23515 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____23515 with
             | (formals,c) ->
                 let uu____23547 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____23547 with
                  | (actuals,uu____23558,uu____23559) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____23580 =
                          let uu____23586 =
                            let uu____23588 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____23590 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____23588 uu____23590
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____23586)
                           in
                        FStar_Errors.raise_error uu____23580
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____23598 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____23598 actuals
                            in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument was found"
                              else
                                (let uu____23629 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____23629)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____23648 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____23648)
                               in
                            let msg =
                              let uu____23653 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____23655 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____23653 uu____23655 formals_msg
                                actuals_msg
                               in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                msg) lbdef.FStar_Syntax_Syntax.pos)
                         else ();
                         (let quals =
                            FStar_TypeChecker_Env.lookup_effect_quals env
                              (FStar_Syntax_Util.comp_effect_name c)
                             in
                          FStar_All.pipe_right quals
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect)))))
           in
        let uu____23667 =
          FStar_List.fold_left
            (fun uu____23700  ->
               fun lb  ->
                 match uu____23700 with
                 | (lbs1,env1,g_acc) ->
                     let uu____23725 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____23725 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____23748 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____23767 =
                                 let uu____23774 =
                                   let uu____23775 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____23775
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3117_23786 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3117_23786.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3117_23786.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3117_23786.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3117_23786.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3117_23786.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3117_23786.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3117_23786.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3117_23786.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3117_23786.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3117_23786.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3117_23786.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3117_23786.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3117_23786.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3117_23786.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3117_23786.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3117_23786.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3117_23786.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3117_23786.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3117_23786.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3117_23786.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3117_23786.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3117_23786.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3117_23786.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3117_23786.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3117_23786.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3117_23786.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3117_23786.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3117_23786.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3117_23786.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3117_23786.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3117_23786.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3117_23786.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3117_23786.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3117_23786.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3117_23786.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3117_23786.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3117_23786.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3117_23786.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3117_23786.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3117_23786.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3117_23786.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3117_23786.FStar_TypeChecker_Env.nbe)
                                    }) t uu____23774
                                  in
                               match uu____23767 with
                               | (t1,uu____23795,g) ->
                                   let uu____23797 =
                                     let uu____23798 =
                                       let uu____23799 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____23799
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____23798
                                      in
                                   let uu____23800 = norm env01 t1  in
                                   (uu____23797, uu____23800))
                             in
                          (match uu____23748 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____23820 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____23820
                                 then
                                   let uu___3127_23823 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3127_23823.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3127_23823.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3127_23823.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3127_23823.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3127_23823.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3127_23823.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3127_23823.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3127_23823.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3127_23823.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3127_23823.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3127_23823.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3127_23823.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3127_23823.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3127_23823.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3127_23823.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3127_23823.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3127_23823.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3127_23823.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3127_23823.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3127_23823.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3127_23823.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3127_23823.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3127_23823.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3127_23823.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3127_23823.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3127_23823.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3127_23823.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3127_23823.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3127_23823.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3127_23823.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3127_23823.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3127_23823.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3127_23823.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3127_23823.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3127_23823.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3127_23823.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3127_23823.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3127_23823.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3127_23823.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3127_23823.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3127_23823.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3127_23823.FStar_TypeChecker_Env.nbe)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3130_23837 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3130_23837.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3130_23837.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3130_23837.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3130_23837.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____23667 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____23863 =
        let uu____23872 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____23898 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____23898 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____23928 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____23928
                       | uu____23935 ->
                           let lb1 =
                             let uu___3147_23938 = lb  in
                             let uu____23939 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3147_23938.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3147_23938.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3147_23938.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3147_23938.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____23939;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3147_23938.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3147_23938.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____23942 =
                             let uu____23949 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____23949
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____23942 with
                            | (e,c,g) ->
                                ((let uu____23958 =
                                    let uu____23960 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____23960  in
                                  if uu____23958
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                        "Expected let rec to be a Tot term; got effect GTot")
                                      e.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let lb2 =
                                    FStar_Syntax_Util.mk_letbinding
                                      lb1.FStar_Syntax_Syntax.lbname
                                      lb1.FStar_Syntax_Syntax.lbunivs
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                      FStar_Parser_Const.effect_Tot_lid e
                                      lb1.FStar_Syntax_Syntax.lbattrs
                                      lb1.FStar_Syntax_Syntax.lbpos
                                     in
                                  (lb2, g)))))))
           in
        FStar_All.pipe_right uu____23872 FStar_List.unzip  in
      match uu____23863 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard
             in
          (lbs1, g_lbs)

and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t *
          Prims.bool))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____24016 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____24016 with
        | (env1,uu____24035) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____24043 = check_lbtyp top_level env lb  in
            (match uu____24043 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____24092 =
                     tc_maybe_toplevel_term
                       (let uu___3178_24101 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3178_24101.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3178_24101.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3178_24101.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3178_24101.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3178_24101.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3178_24101.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3178_24101.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3178_24101.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3178_24101.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3178_24101.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3178_24101.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3178_24101.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3178_24101.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3178_24101.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3178_24101.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3178_24101.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3178_24101.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3178_24101.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3178_24101.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3178_24101.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3178_24101.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3178_24101.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3178_24101.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3178_24101.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3178_24101.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3178_24101.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3178_24101.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3178_24101.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3178_24101.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3178_24101.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3178_24101.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3178_24101.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3178_24101.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3178_24101.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3178_24101.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3178_24101.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3178_24101.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3178_24101.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3178_24101.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3178_24101.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3178_24101.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3178_24101.FStar_TypeChecker_Env.nbe)
                        }) e11
                      in
                   match uu____24092 with
                   | (e12,c1,g1) ->
                       let uu____24116 =
                         let uu____24121 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____24127  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____24121 e12 c1 wf_annot
                          in
                       (match uu____24116 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____24144 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____24144
                              then
                                let uu____24147 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____24149 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____24151 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____24147 uu____24149 uu____24151
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.subst_elt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____24190 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24190 with
             | (univ_opening,univ_vars1) ->
                 let uu____24223 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____24223))
        | uu____24228 ->
            let uu____24229 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24229 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24279 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____24279)
                 else
                   (let uu____24286 = FStar_Syntax_Util.type_u ()  in
                    match uu____24286 with
                    | (k,uu____24306) ->
                        let uu____24307 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____24307 with
                         | (t2,uu____24329,g) ->
                             ((let uu____24332 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____24332
                               then
                                 let uu____24335 =
                                   let uu____24337 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____24337
                                    in
                                 let uu____24338 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____24335 uu____24338
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____24344 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____24344))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____24350  ->
      match uu____24350 with
      | (x,imp) ->
          let uu____24377 = FStar_Syntax_Util.type_u ()  in
          (match uu____24377 with
           | (tu,u) ->
               ((let uu____24399 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____24399
                 then
                   let uu____24402 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____24404 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____24406 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____24402 uu____24404 uu____24406
                 else ());
                (let uu____24411 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____24411 with
                 | (t,uu____24433,g) ->
                     let uu____24435 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____24451 = tc_tactic env tau  in
                           (match uu____24451 with
                            | (tau1,uu____24465,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____24469 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____24435 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3240_24504 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3240_24504.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3240_24504.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____24506 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____24506
                            then
                              let uu____24509 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____24513 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____24509
                                uu____24513
                            else ());
                           (let uu____24518 = push_binding env x1  in
                            (x1, uu____24518, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____24530 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____24530
       then
         let uu____24533 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____24533
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____24646 = tc_binder env1 b  in
             (match uu____24646 with
              | (b1,env',g,u) ->
                  let uu____24695 = aux env' bs2  in
                  (match uu____24695 with
                   | (bs3,env'1,g',us) ->
                       let uu____24756 =
                         let uu____24757 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____24757  in
                       ((b1 :: bs3), env'1, uu____24756, (u :: us))))
          in
       aux env bs)

and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.args Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Env.guard_t))
  =
  fun en  ->
    fun pats  ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____24855  ->
             fun uu____24856  ->
               match (uu____24855, uu____24856) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____24948 = tc_term en1 t  in
                     match uu____24948 with
                     | (t1,uu____24968,g') ->
                         let uu____24970 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____24970)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____25024  ->
             match uu____25024 with
             | (pats1,g) ->
                 let uu____25051 = tc_args en p  in
                 (match uu____25051 with
                  | (args,g') ->
                      let uu____25064 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____25064))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____25077 = tc_maybe_toplevel_term env e  in
      match uu____25077 with
      | (e1,c,g) ->
          let uu____25093 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____25093
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____25107 =
               let uu____25113 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____25113
               then
                 let uu____25121 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____25121, false)
               else
                 (let uu____25126 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____25126, true))
                in
             match uu____25107 with
             | (target_comp,allow_ghost) ->
                 let uu____25139 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____25139 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____25149 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____25150 =
                        FStar_TypeChecker_Env.conj_guard g1 g'  in
                      (e1, uu____25149, uu____25150)
                  | uu____25151 ->
                      if allow_ghost
                      then
                        let uu____25161 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____25161
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____25175 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____25175
                           e1.FStar_Syntax_Syntax.pos)))

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
          FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env  ->
    fun t  ->
      let uu____25199 = tc_tot_or_gtot_term env t  in
      match uu____25199 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____25232 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25232
       then
         let uu____25237 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____25237
       else ());
      (let env1 =
         let uu___3322_25243 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3322_25243.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3322_25243.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3322_25243.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3322_25243.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3322_25243.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3322_25243.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3322_25243.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3322_25243.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3322_25243.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3322_25243.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3322_25243.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3322_25243.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3322_25243.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3322_25243.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3322_25243.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3322_25243.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3322_25243.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3322_25243.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3322_25243.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3322_25243.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3322_25243.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3322_25243.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3322_25243.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3322_25243.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3322_25243.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3322_25243.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3322_25243.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3322_25243.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3322_25243.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3322_25243.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3322_25243.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3322_25243.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3322_25243.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3322_25243.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3322_25243.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3322_25243.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3322_25243.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3322_25243.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3322_25243.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3322_25243.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3322_25243.FStar_TypeChecker_Env.nbe)
         }  in
       let uu____25251 =
         try
           (fun uu___3326_25265  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____25286) ->
             let uu____25289 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____25289
          in
       match uu____25251 with
       | (t,c,g) ->
           let uu____25306 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____25306
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____25317 =
                let uu____25323 =
                  let uu____25325 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____25325
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____25323)
                 in
              let uu____25329 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____25317 uu____25329))
  
let level_of_type_fail :
  'Auu____25345 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____25345
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____25363 =
          let uu____25369 =
            let uu____25371 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____25371 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____25369)  in
        let uu____25375 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____25363 uu____25375
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____25409 =
            let uu____25410 = FStar_Syntax_Util.unrefine t1  in
            uu____25410.FStar_Syntax_Syntax.n  in
          match uu____25409 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____25414 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____25420 = FStar_Syntax_Util.type_u ()  in
                 match uu____25420 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3357_25428 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3357_25428.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3357_25428.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3357_25428.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3357_25428.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3357_25428.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3357_25428.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3357_25428.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3357_25428.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3357_25428.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3357_25428.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3357_25428.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3357_25428.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3357_25428.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3357_25428.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3357_25428.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3357_25428.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3357_25428.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3357_25428.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3357_25428.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3357_25428.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3357_25428.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3357_25428.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3357_25428.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3357_25428.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3357_25428.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3357_25428.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3357_25428.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3357_25428.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3357_25428.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3357_25428.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3357_25428.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3357_25428.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3357_25428.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3357_25428.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3357_25428.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3357_25428.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3357_25428.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3357_25428.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3357_25428.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3357_25428.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3357_25428.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3357_25428.FStar_TypeChecker_Env.nbe)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25433 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____25433
                       | uu____25435 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun e  ->
      let uu____25452 =
        let uu____25453 = FStar_Syntax_Subst.compress e  in
        uu____25453.FStar_Syntax_Syntax.n  in
      match uu____25452 with
      | FStar_Syntax_Syntax.Tm_bvar uu____25456 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____25459 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____25483 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____25500) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____25545) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____25552 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25552 with | ((uu____25561,t),uu____25563) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____25569 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____25569
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25572,(FStar_Util.Inl t,uu____25574),uu____25575) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____25622,(FStar_Util.Inr c,uu____25624),uu____25625) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____25673 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____25682;
             FStar_Syntax_Syntax.vars = uu____25683;_},us)
          ->
          let uu____25689 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____25689 with
           | ((us',t),uu____25700) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____25707 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____25707)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____25726 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____25728 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____25737) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____25764 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____25764 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____25784  ->
                      match uu____25784 with
                      | (b,uu____25792) ->
                          let uu____25797 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____25797) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____25802 = universe_of_aux env res  in
                 level_of_type env res uu____25802  in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res)
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2  in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____25913 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____25929 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____25967 ->
                let uu____25968 = universe_of_aux env hd3  in
                (uu____25968, args1)
            | FStar_Syntax_Syntax.Tm_name uu____25979 ->
                let uu____25980 = universe_of_aux env hd3  in
                (uu____25980, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____25991 ->
                let uu____26004 = universe_of_aux env hd3  in
                (uu____26004, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____26015 ->
                let uu____26022 = universe_of_aux env hd3  in
                (uu____26022, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____26033 ->
                let uu____26060 = universe_of_aux env hd3  in
                (uu____26060, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____26071 ->
                let uu____26078 = universe_of_aux env hd3  in
                (uu____26078, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____26089 ->
                let uu____26090 = universe_of_aux env hd3  in
                (uu____26090, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____26101 ->
                let uu____26116 = universe_of_aux env hd3  in
                (uu____26116, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____26127 ->
                let uu____26134 = universe_of_aux env hd3  in
                (uu____26134, args1)
            | FStar_Syntax_Syntax.Tm_type uu____26145 ->
                let uu____26146 = universe_of_aux env hd3  in
                (uu____26146, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____26157,hd4::uu____26159) ->
                let uu____26224 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____26224 with
                 | (uu____26239,uu____26240,hd5) ->
                     let uu____26258 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____26258 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____26315 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____26317 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____26317 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____26375 ->
                let uu____26376 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____26376 with
                 | (env1,uu____26398) ->
                     let env2 =
                       let uu___3518_26404 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3518_26404.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3518_26404.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3518_26404.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3518_26404.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3518_26404.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3518_26404.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3518_26404.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3518_26404.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3518_26404.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3518_26404.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3518_26404.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3518_26404.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3518_26404.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3518_26404.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3518_26404.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3518_26404.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3518_26404.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3518_26404.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3518_26404.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3518_26404.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3518_26404.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3518_26404.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3518_26404.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3518_26404.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3518_26404.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3518_26404.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3518_26404.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3518_26404.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3518_26404.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3518_26404.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3518_26404.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3518_26404.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3518_26404.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3518_26404.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3518_26404.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3518_26404.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3518_26404.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3518_26404.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3518_26404.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3518_26404.FStar_TypeChecker_Env.nbe)
                       }  in
                     ((let uu____26409 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____26409
                       then
                         let uu____26414 =
                           let uu____26416 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____26416  in
                         let uu____26417 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____26414 uu____26417
                       else ());
                      (let uu____26422 = tc_term env2 hd3  in
                       match uu____26422 with
                       | (uu____26443,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____26444;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____26446;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____26447;_},g)
                           ->
                           ((let uu____26461 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____26461 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____26472 = type_of_head true hd1 args  in
          (match uu____26472 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____26511 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____26511 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____26563 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____26563)))
      | FStar_Syntax_Syntax.Tm_match (uu____26565,hd1::uu____26567) ->
          let uu____26632 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____26632 with
           | (uu____26633,uu____26634,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____26652,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____26699 = universe_of_aux env e  in
      level_of_type env e uu____26699
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____26723 = tc_binders env tps  in
      match uu____26723 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____26781 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____26807 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26813 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____26813
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26815 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26815
            (fun uu____26829  ->
               match uu____26829 with
               | (t2,uu____26837) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26839;
             FStar_Syntax_Syntax.vars = uu____26840;_},us)
          ->
          let uu____26846 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____26846
            (fun uu____26860  ->
               match uu____26860 with
               | (t2,uu____26868) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____26869) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____26871 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____26871
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____26873 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____26873
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____26878;_})
          ->
          let mk_comp =
            let uu____26922 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____26922
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____26953 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____26953
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____27023 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____27023
                 (fun u  ->
                    let uu____27031 =
                      let uu____27034 =
                        let uu____27041 =
                          let uu____27042 =
                            let uu____27057 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____27057)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____27042  in
                        FStar_Syntax_Syntax.mk uu____27041  in
                      uu____27034 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____27031))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____27094 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____27094 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____27153 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____27153
                       (fun uc  ->
                          let uu____27161 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____27161)
                 | (x,imp)::bs3 ->
                     let uu____27187 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____27187
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____27196 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27216) ->
          let uu____27221 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____27221
            (fun u_x  ->
               let uu____27229 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____27229)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____27234;
             FStar_Syntax_Syntax.vars = uu____27235;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27314 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27314 with
           | (unary_op1,uu____27334) ->
               let head1 =
                 let uu____27362 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____27362
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____27410;
             FStar_Syntax_Syntax.vars = uu____27411;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27507 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27507 with
           | (unary_op1,uu____27527) ->
               let head1 =
                 let uu____27555 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____27555
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____27611;
             FStar_Syntax_Syntax.vars = uu____27612;_},uu____27613::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____27652;
             FStar_Syntax_Syntax.vars = uu____27653;_},(t2,uu____27655)::uu____27656::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____27752 =
              let uu____27753 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____27753.FStar_Syntax_Syntax.n  in
            match uu____27752 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____27826 = FStar_Util.first_N n_args bs  in
                    match uu____27826 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____27914 =
                          let uu____27919 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____27919  in
                        (match uu____27914 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____27973 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____27973 with
                       | (bs1,c1) ->
                           let uu____27994 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____27994
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____28076  ->
                     match uu____28076 with
                     | (bs1,t2) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args
                            in
                         let uu____28152 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____28152)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____28154) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____28160,uu____28161) ->
                aux t2
            | uu____28202 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28203,(FStar_Util.Inl t2,uu____28205),uu____28206) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28253,(FStar_Util.Inr c,uu____28255),uu____28256) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____28321 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____28321
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____28329) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____28334 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____28357 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____28371 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____28382 = type_of_well_typed_term env t  in
      match uu____28382 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____28388;
            FStar_Syntax_Syntax.vars = uu____28389;_}
          -> FStar_Pervasives_Native.Some u
      | uu____28392 -> FStar_Pervasives_Native.None

let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___3797_28420 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3797_28420.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3797_28420.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3797_28420.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3797_28420.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3797_28420.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3797_28420.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3797_28420.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3797_28420.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3797_28420.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3797_28420.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3797_28420.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3797_28420.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3797_28420.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3797_28420.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3797_28420.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3797_28420.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3797_28420.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3797_28420.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3797_28420.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3797_28420.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3797_28420.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3797_28420.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3797_28420.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3797_28420.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3797_28420.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3797_28420.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3797_28420.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3797_28420.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3797_28420.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3797_28420.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3797_28420.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3797_28420.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3797_28420.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3797_28420.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3797_28420.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3797_28420.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3797_28420.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3797_28420.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3797_28420.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3797_28420.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3797_28420.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3797_28420.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28427 =
            if must_total
            then
              let uu____28429 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28429 with | (uu____28436,uu____28437,g) -> g
            else
              (let uu____28441 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28441 with | (uu____28448,uu____28449,g) -> g)
             in
          let uu____28451 = type_of_well_typed_term env2 t  in
          match uu____28451 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____28456 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____28456
                then
                  let uu____28461 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____28463 = FStar_Syntax_Print.term_to_string t  in
                  let uu____28465 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____28467 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____28461 uu____28463 uu____28465 uu____28467
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____28476 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____28476
                 then
                   let uu____28481 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____28483 = FStar_Syntax_Print.term_to_string t  in
                   let uu____28485 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____28487 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____28481
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____28483 uu____28485 uu____28487
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None  -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
  
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___3828_28524 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3828_28524.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3828_28524.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3828_28524.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3828_28524.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3828_28524.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3828_28524.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3828_28524.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3828_28524.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3828_28524.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3828_28524.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3828_28524.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3828_28524.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3828_28524.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3828_28524.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3828_28524.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3828_28524.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3828_28524.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3828_28524.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3828_28524.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3828_28524.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3828_28524.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3828_28524.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3828_28524.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3828_28524.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3828_28524.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3828_28524.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3828_28524.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3828_28524.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3828_28524.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3828_28524.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3828_28524.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3828_28524.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3828_28524.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3828_28524.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3828_28524.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3828_28524.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3828_28524.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3828_28524.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3828_28524.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3828_28524.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3828_28524.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3828_28524.FStar_TypeChecker_Env.nbe)
            }  in
          let slow_check uu____28531 =
            if must_total
            then
              let uu____28533 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____28533 with | (uu____28540,uu____28541,g) -> g
            else
              (let uu____28545 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____28545 with | (uu____28552,uu____28553,g) -> g)
             in
          let uu____28555 =
            let uu____28557 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____28557  in
          if uu____28555
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  