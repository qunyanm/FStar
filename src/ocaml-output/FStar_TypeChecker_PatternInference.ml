open Prims
let (filter_trigger :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun names1  ->
    fun t  ->
      let bvs = FStar_Syntax_Free.names t  in
      let uu____19 = FStar_Util.set_is_subset_of names1 bvs  in
      if uu____19
      then FStar_Pervasives_Native.Some t
      else FStar_Pervasives_Native.None
  
let (has_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun e  ->
      let uu____38 =
        let uu____39 = FStar_Syntax_Subst.compress e  in
        uu____39.FStar_Syntax_Syntax.n  in
      match uu____38 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_TypeChecker_Env.fv_has_attr env fv
            FStar_Parser_Const.smt_theory_symbol_attr_lid
          -> false
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____46;
             FStar_Syntax_Syntax.vars = uu____47;_},uu____48)
          when
          FStar_TypeChecker_Env.fv_has_attr env fv
            FStar_Parser_Const.smt_theory_symbol_attr_lid
          -> false
      | uu____54 -> true
  
let rec (find_trigger :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.term ->
        (Prims.bool * FStar_Syntax_Syntax.term Prims.list))
  =
  fun env  ->
    fun names1  ->
      fun t  ->
        let debug1 = false  in
        if debug1
        then
          (let uu____95 = FStar_Syntax_Print.term_to_string t  in
           let uu____97 =
             let uu____99 = FStar_Syntax_Subst.compress t  in
             FStar_Syntax_Print.tag_of_term uu____99  in
           FStar_Util.print2 "find trigger for : %s (%s)\n" uu____95 uu____97)
        else ();
        (let uu____103 =
           let uu____104 = FStar_Syntax_Subst.compress t  in
           uu____104.FStar_Syntax_Syntax.n  in
         match uu____103 with
         | FStar_Syntax_Syntax.Tm_bvar x -> (false, [])
         | FStar_Syntax_Syntax.Tm_name x -> (false, [])
         | FStar_Syntax_Syntax.Tm_fvar fv -> (false, [])
         | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
             find_trigger env names1 e
         | FStar_Syntax_Syntax.Tm_constant c -> (false, [])
         | FStar_Syntax_Syntax.Tm_type u -> (true, [])
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____147) -> (true, [])
         | FStar_Syntax_Syntax.Tm_arrow (xs,body) -> (true, [])
         | FStar_Syntax_Syntax.Tm_refine (x,phi) -> (true, [])
         | FStar_Syntax_Syntax.Tm_app (e,args) ->
             let uu____238 =
               let uu____239 = FStar_Syntax_Subst.compress e  in
               uu____239.FStar_Syntax_Syntax.n  in
             (match uu____238 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.forall_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.exists_lid)
                  -> (true, [])
              | FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____255;
                     FStar_Syntax_Syntax.vars = uu____256;_},uu____257)
                  when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.forall_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.exists_lid)
                  -> (true, [])
              | uu____266 ->
                  let uu____267 = find_trigger env names1 e  in
                  (match uu____267 with
                   | (trigger_killer,uu____283) ->
                       let uu____290 =
                         FStar_List.fold_left
                           (fun uu____320  ->
                              fun uu____321  ->
                                match (uu____320, uu____321) with
                                | ((k,l),(e1,q)) ->
                                    let uu____382 =
                                      find_trigger env names1 e1  in
                                    (match uu____382 with
                                     | (b,c) ->
                                         ((k || b), (FStar_List.append l c))))
                           (trigger_killer, []) args
                          in
                       (match uu____290 with
                        | (trigger_killer1,c) ->
                            let c1 =
                              FStar_All.pipe_right c
                                (FStar_List.choose
                                   (fun t1  -> filter_trigger names1 t1))
                               in
                            let c2 =
                              match c1 with
                              | [] ->
                                  let uu____440 =
                                    (Prims.op_Negation trigger_killer1) &&
                                      (has_no_smt_theory_symbols env e)
                                     in
                                  if uu____440
                                  then FStar_List.append c1 [t]
                                  else c1
                              | uu____447 -> c1  in
                            (trigger_killer1, c2))))
         | FStar_Syntax_Syntax.Tm_match (e,branches) -> (true, [])
         | FStar_Syntax_Syntax.Tm_ascribed uu____495 -> (true, [])
         | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
             (true, [])
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____551) -> (false, [])
         | FStar_Syntax_Syntax.Tm_delayed uu____572 ->
             failwith "Tm_delayed is impossible after compress"
         | FStar_Syntax_Syntax.Tm_meta (e,m) -> (true, [])
         | FStar_Syntax_Syntax.Tm_lazy i -> (true, [])
         | FStar_Syntax_Syntax.Tm_quoted (tm,qi) -> (true, [])
         | FStar_Syntax_Syntax.Tm_unknown  -> (true, []))
  
let (terms_to_bvs :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun names1  ->
    match names1 with
    | [] -> failwith "Empty bound vars"
    | hd1::tl1 ->
        let uu____653 = FStar_Syntax_Free.names hd1  in
        FStar_List.fold_left
          (fun out  ->
             fun x  ->
               let uu____665 = FStar_Syntax_Free.names x  in
               FStar_Util.set_union out uu____665) uu____653 tl1
  
let (infer_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args Prims.list)
  =
  fun env  ->
    fun names1  ->
      fun t  ->
        let debug1 = true  in
        if debug1
        then
          (let uu____697 = FStar_Syntax_Print.term_to_string t  in
           let uu____699 =
             let uu____701 = FStar_Syntax_Subst.compress t  in
             FStar_Syntax_Print.tag_of_term uu____701  in
           let uu____702 =
             let uu____704 =
               FStar_All.pipe_right names1
                 (FStar_List.map FStar_Syntax_Print.term_to_string)
                in
             FStar_All.pipe_right uu____704 (FStar_String.concat ", ")  in
           FStar_Util.print3 "Infer pattern for : %s (%s) with names: (%s)\n"
             uu____697 uu____699 uu____702)
        else ();
        (let bvs = terms_to_bvs names1  in
         let uu____725 = find_trigger env bvs t  in
         match uu____725 with
         | (uu____735,p) ->
             let pats =
               FStar_All.pipe_right p
                 (FStar_List.choose (fun t1  -> filter_trigger bvs t1))
                in
             (if debug1
              then
                (let uu____754 =
                   let uu____756 =
                     FStar_All.pipe_right pats
                       (FStar_List.map FStar_Syntax_Print.term_to_string)
                      in
                   FStar_All.pipe_right uu____756 (FStar_String.concat "; ")
                    in
                 FStar_Util.print1 "Found patterns: %s\n" uu____754)
              else ();
              FStar_List.fold_left
                (fun l  ->
                   fun t1  ->
                     let uu____787 =
                       let uu____792 =
                         let uu____795 = FStar_Syntax_Syntax.as_arg t1  in
                         [uu____795]  in
                       [uu____792]  in
                     FStar_List.append l uu____787) [] pats))
  
let (remove_invalid_pattern :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Syntax_Syntax.args Prims.list ->
      FStar_Syntax_Syntax.args Prims.list)
  =
  fun names1  ->
    fun pats  ->
      match names1 with
      | [] -> pats
      | uu____827 ->
          let bvs = terms_to_bvs names1  in
          let pats1 =
            FStar_List.fold_left
              (fun l  ->
                 fun p  ->
                   let p1 =
                     FStar_List.choose
                       (fun uu____873  ->
                          match uu____873 with
                          | (t,uu____883) -> filter_trigger bvs t) p
                      in
                   FStar_List.append l p1) [] pats
             in
          FStar_List.fold_left
            (fun l  ->
               fun t  ->
                 let uu____901 =
                   let uu____906 =
                     let uu____909 = FStar_Syntax_Syntax.as_arg t  in
                     [uu____909]  in
                   [uu____906]  in
                 FStar_List.append l uu____901) [] pats1
  