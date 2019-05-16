open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tcenv
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> subst1
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { tcenv = env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___28_129 = a  in
              let uu____130 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___28_129.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___28_129.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____130
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____143 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____143
             then
               (d "Elaborating extra WP combinators";
                (let uu____149 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____149))
             else ());
            (let rec collect_binders t =
               let uu____168 =
                 let uu____169 =
                   let uu____172 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____172
                    in
                 uu____169.FStar_Syntax_Syntax.n  in
               match uu____168 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____207) -> t1
                     | uu____216 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____218 = collect_binders rest  in
                   FStar_List.append bs uu____218
               | FStar_Syntax_Syntax.Tm_type uu____233 -> []
               | uu____240 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____267 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____267 FStar_Syntax_Util.name_binders
                in
             (let uu____293 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____293
              then
                let uu____297 =
                  let uu____299 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____299  in
                d uu____297
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____337 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____337 with
                | (sigelt,fv) ->
                    ((let uu____345 =
                        let uu____348 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____348
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____345);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____428  ->
                     match uu____428 with
                     | (t,b) ->
                         let uu____442 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____442))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____481 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____481))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____515 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____515)
                 in
              let uu____518 =
                let uu____535 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____560 =
                        let uu____563 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____563  in
                      FStar_Syntax_Util.arrow gamma uu____560  in
                    let uu____564 =
                      let uu____565 =
                        let uu____574 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____581 =
                          let uu____590 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____590]  in
                        uu____574 :: uu____581  in
                      FStar_List.append binders uu____565  in
                    FStar_Syntax_Util.abs uu____564 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____621 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____622 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____621, uu____622)  in
                match uu____535 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____664 =
                        let uu____665 =
                          let uu____682 =
                            let uu____693 =
                              FStar_List.map
                                (fun uu____715  ->
                                   match uu____715 with
                                   | (bv,uu____727) ->
                                       let uu____732 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____733 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____732, uu____733)) binders
                               in
                            let uu____735 =
                              let uu____742 =
                                let uu____747 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____748 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____747, uu____748)  in
                              let uu____750 =
                                let uu____757 =
                                  let uu____762 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____762)  in
                                [uu____757]  in
                              uu____742 :: uu____750  in
                            FStar_List.append uu____693 uu____735  in
                          (fv, uu____682)  in
                        FStar_Syntax_Syntax.Tm_app uu____665  in
                      mk1 uu____664  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____518 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____835 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____835
                       in
                    let ret1 =
                      let uu____840 =
                        let uu____841 =
                          let uu____844 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____844  in
                        FStar_Syntax_Util.residual_tot uu____841  in
                      FStar_Pervasives_Native.Some uu____840  in
                    let body =
                      let uu____848 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____848 ret1  in
                    let uu____851 =
                      let uu____852 = mk_all_implicit binders  in
                      let uu____859 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____852 uu____859  in
                    FStar_Syntax_Util.abs uu____851 body ret1  in
                  let c_pure1 =
                    let uu____897 = mk_lid "pure"  in
                    register env1 uu____897 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____907 =
                        let uu____908 =
                          let uu____909 =
                            let uu____918 =
                              let uu____925 =
                                let uu____926 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____926
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____925  in
                            [uu____918]  in
                          let uu____939 =
                            let uu____942 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____942  in
                          FStar_Syntax_Util.arrow uu____909 uu____939  in
                        mk_gctx uu____908  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____907
                       in
                    let r =
                      let uu____945 =
                        let uu____946 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____946  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____945
                       in
                    let ret1 =
                      let uu____951 =
                        let uu____952 =
                          let uu____955 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____955  in
                        FStar_Syntax_Util.residual_tot uu____952  in
                      FStar_Pervasives_Native.Some uu____951  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____965 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____968 =
                          let uu____979 =
                            let uu____982 =
                              let uu____983 =
                                let uu____984 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____984
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____983  in
                            [uu____982]  in
                          FStar_List.append gamma_as_args uu____979  in
                        FStar_Syntax_Util.mk_app uu____965 uu____968  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____987 =
                      let uu____988 = mk_all_implicit binders  in
                      let uu____995 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____988 uu____995  in
                    FStar_Syntax_Util.abs uu____987 outer_body ret1  in
                  let c_app1 =
                    let uu____1047 = mk_lid "app"  in
                    register env1 uu____1047 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1059 =
                        let uu____1068 =
                          let uu____1075 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1075  in
                        [uu____1068]  in
                      let uu____1088 =
                        let uu____1091 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1091  in
                      FStar_Syntax_Util.arrow uu____1059 uu____1088  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1095 =
                        let uu____1096 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1096  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1095
                       in
                    let ret1 =
                      let uu____1101 =
                        let uu____1102 =
                          let uu____1105 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1105  in
                        FStar_Syntax_Util.residual_tot uu____1102  in
                      FStar_Pervasives_Native.Some uu____1101  in
                    let uu____1106 =
                      let uu____1107 = mk_all_implicit binders  in
                      let uu____1114 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1107 uu____1114  in
                    let uu____1165 =
                      let uu____1168 =
                        let uu____1179 =
                          let uu____1182 =
                            let uu____1183 =
                              let uu____1194 =
                                let uu____1197 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1197]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1194
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1183  in
                          let uu____1206 =
                            let uu____1209 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1209]  in
                          uu____1182 :: uu____1206  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1179
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1168  in
                    FStar_Syntax_Util.abs uu____1106 uu____1165 ret1  in
                  let c_lift11 =
                    let uu____1219 = mk_lid "lift1"  in
                    register env1 uu____1219 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1233 =
                        let uu____1242 =
                          let uu____1249 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1249  in
                        let uu____1250 =
                          let uu____1259 =
                            let uu____1266 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1266  in
                          [uu____1259]  in
                        uu____1242 :: uu____1250  in
                      let uu____1285 =
                        let uu____1288 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1288  in
                      FStar_Syntax_Util.arrow uu____1233 uu____1285  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1292 =
                        let uu____1293 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1293  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1292
                       in
                    let a2 =
                      let uu____1296 =
                        let uu____1297 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1297  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1296
                       in
                    let ret1 =
                      let uu____1302 =
                        let uu____1303 =
                          let uu____1306 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1306  in
                        FStar_Syntax_Util.residual_tot uu____1303  in
                      FStar_Pervasives_Native.Some uu____1302  in
                    let uu____1307 =
                      let uu____1308 = mk_all_implicit binders  in
                      let uu____1315 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1308 uu____1315  in
                    let uu____1380 =
                      let uu____1383 =
                        let uu____1394 =
                          let uu____1397 =
                            let uu____1398 =
                              let uu____1409 =
                                let uu____1412 =
                                  let uu____1413 =
                                    let uu____1424 =
                                      let uu____1427 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1427]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1424
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1413
                                   in
                                let uu____1436 =
                                  let uu____1439 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1439]  in
                                uu____1412 :: uu____1436  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1409
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1398  in
                          let uu____1448 =
                            let uu____1451 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1451]  in
                          uu____1397 :: uu____1448  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1394
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1383  in
                    FStar_Syntax_Util.abs uu____1307 uu____1380 ret1  in
                  let c_lift21 =
                    let uu____1461 = mk_lid "lift2"  in
                    register env1 uu____1461 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1473 =
                        let uu____1482 =
                          let uu____1489 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1489  in
                        [uu____1482]  in
                      let uu____1502 =
                        let uu____1505 =
                          let uu____1506 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1506  in
                        FStar_Syntax_Syntax.mk_Total uu____1505  in
                      FStar_Syntax_Util.arrow uu____1473 uu____1502  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1512 =
                        let uu____1513 =
                          let uu____1516 =
                            let uu____1517 =
                              let uu____1526 =
                                let uu____1533 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1533
                                 in
                              [uu____1526]  in
                            let uu____1546 =
                              let uu____1549 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1549  in
                            FStar_Syntax_Util.arrow uu____1517 uu____1546  in
                          mk_ctx uu____1516  in
                        FStar_Syntax_Util.residual_tot uu____1513  in
                      FStar_Pervasives_Native.Some uu____1512  in
                    let e1 =
                      let uu____1551 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1551
                       in
                    let body =
                      let uu____1556 =
                        let uu____1557 =
                          let uu____1566 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1566]  in
                        FStar_List.append gamma uu____1557  in
                      let uu____1591 =
                        let uu____1594 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1597 =
                          let uu____1608 =
                            let uu____1609 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1609  in
                          let uu____1610 = args_of_binders1 gamma  in
                          uu____1608 :: uu____1610  in
                        FStar_Syntax_Util.mk_app uu____1594 uu____1597  in
                      FStar_Syntax_Util.abs uu____1556 uu____1591 ret1  in
                    let uu____1613 =
                      let uu____1614 = mk_all_implicit binders  in
                      let uu____1621 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1614 uu____1621  in
                    FStar_Syntax_Util.abs uu____1613 body ret1  in
                  let c_push1 =
                    let uu____1666 = mk_lid "push"  in
                    register env1 uu____1666 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1693 =
                        let uu____1694 =
                          let uu____1711 = args_of_binders1 binders  in
                          (c, uu____1711)  in
                        FStar_Syntax_Syntax.Tm_app uu____1694  in
                      mk1 uu____1693
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1740 =
                        let uu____1741 =
                          let uu____1750 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1757 =
                            let uu____1766 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1766]  in
                          uu____1750 :: uu____1757  in
                        let uu____1791 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1741 uu____1791  in
                      FStar_Syntax_Syntax.mk_Total uu____1740  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1796 =
                      let uu____1797 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1797  in
                    let uu____1812 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1817 =
                        let uu____1820 =
                          let uu____1831 =
                            let uu____1834 =
                              let uu____1835 =
                                let uu____1846 =
                                  let uu____1855 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1855  in
                                [uu____1846]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1835  in
                            [uu____1834]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1831
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1820  in
                      FStar_Syntax_Util.ascribe uu____1817
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1796 uu____1812
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1899 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1899 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1916 =
                        let uu____1927 =
                          let uu____1930 =
                            let uu____1931 =
                              let uu____1942 =
                                let uu____1945 =
                                  let uu____1946 =
                                    let uu____1957 =
                                      let uu____1966 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1966
                                       in
                                    [uu____1957]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1946
                                   in
                                [uu____1945]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1942
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1931  in
                          let uu____1991 =
                            let uu____1994 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1994]  in
                          uu____1930 :: uu____1991  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1927
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1916  in
                    let uu____2003 =
                      let uu____2004 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2004  in
                    FStar_Syntax_Util.abs uu____2003 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____2020 = mk_lid "wp_assert"  in
                    register env1 uu____2020 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____2037 =
                        let uu____2048 =
                          let uu____2051 =
                            let uu____2052 =
                              let uu____2063 =
                                let uu____2066 =
                                  let uu____2067 =
                                    let uu____2078 =
                                      let uu____2087 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2087
                                       in
                                    [uu____2078]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____2067
                                   in
                                [uu____2066]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____2063
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2052  in
                          let uu____2112 =
                            let uu____2115 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2115]  in
                          uu____2051 :: uu____2112  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2048
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2037  in
                    let uu____2124 =
                      let uu____2125 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2125  in
                    FStar_Syntax_Util.abs uu____2124 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2141 = mk_lid "wp_assume"  in
                    register env1 uu____2141 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2154 =
                        let uu____2163 =
                          let uu____2170 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2170  in
                        [uu____2163]  in
                      let uu____2183 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2154 uu____2183  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2191 =
                        let uu____2202 =
                          let uu____2205 =
                            let uu____2206 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2206  in
                          let uu____2225 =
                            let uu____2228 =
                              let uu____2229 =
                                let uu____2240 =
                                  let uu____2243 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2243]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2240
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2229  in
                            [uu____2228]  in
                          uu____2205 :: uu____2225  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2202
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2191  in
                    let uu____2260 =
                      let uu____2261 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2261  in
                    FStar_Syntax_Util.abs uu____2260 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2277 = mk_lid "wp_close"  in
                    register env1 uu____2277 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2288 =
                      let uu____2289 =
                        let uu____2290 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2290
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2289  in
                    FStar_Pervasives_Native.Some uu____2288  in
                  let mk_forall1 x body =
                    let uu____2302 =
                      let uu____2309 =
                        let uu____2310 =
                          let uu____2327 =
                            let uu____2338 =
                              let uu____2347 =
                                let uu____2348 =
                                  let uu____2349 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2349]  in
                                FStar_Syntax_Util.abs uu____2348 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2347  in
                            [uu____2338]  in
                          (FStar_Syntax_Util.tforall, uu____2327)  in
                        FStar_Syntax_Syntax.Tm_app uu____2310  in
                      FStar_Syntax_Syntax.mk uu____2309  in
                    uu____2302 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2407 =
                      let uu____2408 = FStar_Syntax_Subst.compress t  in
                      uu____2408.FStar_Syntax_Syntax.n  in
                    match uu____2407 with
                    | FStar_Syntax_Syntax.Tm_type uu____2412 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2445  ->
                              match uu____2445 with
                              | (b,uu____2454) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2459 -> true  in
                  let rec is_monotonic t =
                    let uu____2472 =
                      let uu____2473 = FStar_Syntax_Subst.compress t  in
                      uu____2473.FStar_Syntax_Syntax.n  in
                    match uu____2472 with
                    | FStar_Syntax_Syntax.Tm_type uu____2477 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2510  ->
                              match uu____2510 with
                              | (b,uu____2519) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2524 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2598 =
                      let uu____2599 = FStar_Syntax_Subst.compress t1  in
                      uu____2599.FStar_Syntax_Syntax.n  in
                    match uu____2598 with
                    | FStar_Syntax_Syntax.Tm_type uu____2604 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2607);
                                      FStar_Syntax_Syntax.pos = uu____2608;
                                      FStar_Syntax_Syntax.vars = uu____2609;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2653 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2653
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2663 =
                              let uu____2666 =
                                let uu____2677 =
                                  let uu____2686 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2686  in
                                [uu____2677]  in
                              FStar_Syntax_Util.mk_app x uu____2666  in
                            let uu____2703 =
                              let uu____2706 =
                                let uu____2717 =
                                  let uu____2726 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2726  in
                                [uu____2717]  in
                              FStar_Syntax_Util.mk_app y uu____2706  in
                            mk_rel1 b uu____2663 uu____2703  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____2750 =
                               let uu____2753 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2756 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2753 uu____2756  in
                             let uu____2759 =
                               let uu____2762 =
                                 let uu____2765 =
                                   let uu____2776 =
                                     let uu____2785 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2785
                                      in
                                   [uu____2776]  in
                                 FStar_Syntax_Util.mk_app x uu____2765  in
                               let uu____2802 =
                                 let uu____2805 =
                                   let uu____2816 =
                                     let uu____2825 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2825
                                      in
                                   [uu____2816]  in
                                 FStar_Syntax_Util.mk_app y uu____2805  in
                               mk_rel1 b uu____2762 uu____2802  in
                             FStar_Syntax_Util.mk_imp uu____2750 uu____2759
                              in
                           let uu____2842 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2842)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2845);
                                      FStar_Syntax_Syntax.pos = uu____2846;
                                      FStar_Syntax_Syntax.vars = uu____2847;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2891 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2891
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2901 =
                              let uu____2904 =
                                let uu____2915 =
                                  let uu____2924 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2924  in
                                [uu____2915]  in
                              FStar_Syntax_Util.mk_app x uu____2904  in
                            let uu____2941 =
                              let uu____2944 =
                                let uu____2955 =
                                  let uu____2964 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2964  in
                                [uu____2955]  in
                              FStar_Syntax_Util.mk_app y uu____2944  in
                            mk_rel1 b uu____2901 uu____2941  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____2988 =
                               let uu____2991 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2994 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2991 uu____2994  in
                             let uu____2997 =
                               let uu____3000 =
                                 let uu____3003 =
                                   let uu____3014 =
                                     let uu____3023 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____3023
                                      in
                                   [uu____3014]  in
                                 FStar_Syntax_Util.mk_app x uu____3003  in
                               let uu____3040 =
                                 let uu____3043 =
                                   let uu____3054 =
                                     let uu____3063 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____3063
                                      in
                                   [uu____3054]  in
                                 FStar_Syntax_Util.mk_app y uu____3043  in
                               mk_rel1 b uu____3000 uu____3040  in
                             FStar_Syntax_Util.mk_imp uu____2988 uu____2997
                              in
                           let uu____3080 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____3080)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___242_3119 = t1  in
                          let uu____3120 =
                            let uu____3121 =
                              let uu____3136 =
                                let uu____3139 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3139  in
                              ([binder], uu____3136)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3121  in
                          {
                            FStar_Syntax_Syntax.n = uu____3120;
                            FStar_Syntax_Syntax.pos =
                              (uu___242_3119.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___242_3119.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3162 ->
                        failwith "unhandled arrow"
                    | uu____3180 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____3217 =
                        let uu____3218 = FStar_Syntax_Subst.compress t1  in
                        uu____3218.FStar_Syntax_Syntax.n  in
                      match uu____3217 with
                      | FStar_Syntax_Syntax.Tm_type uu____3221 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3248 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3248
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3269 =
                                let uu____3270 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3270 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3269
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3300 =
                            let uu____3311 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3329  ->
                                     match uu____3329 with
                                     | (t2,q) ->
                                         let uu____3349 = project i x  in
                                         let uu____3352 = project i y  in
                                         mk_stronger t2 uu____3349 uu____3352)
                                args
                               in
                            match uu____3311 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3300 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3406);
                                      FStar_Syntax_Syntax.pos = uu____3407;
                                      FStar_Syntax_Syntax.vars = uu____3408;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3452  ->
                                   match uu____3452 with
                                   | (bv,q) ->
                                       let uu____3466 =
                                         let uu____3468 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3468  in
                                       FStar_Syntax_Syntax.gen_bv uu____3466
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3477 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3477) bvs
                             in
                          let body =
                            let uu____3479 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3482 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3479 uu____3482  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3491);
                                      FStar_Syntax_Syntax.pos = uu____3492;
                                      FStar_Syntax_Syntax.vars = uu____3493;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3537  ->
                                   match uu____3537 with
                                   | (bv,q) ->
                                       let uu____3551 =
                                         let uu____3553 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3553  in
                                       FStar_Syntax_Syntax.gen_bv uu____3551
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3562 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3562) bvs
                             in
                          let body =
                            let uu____3564 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3567 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3564 uu____3567  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3574 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3577 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3580 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3583 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3577 uu____3580 uu____3583  in
                    let uu____3586 =
                      let uu____3587 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3587  in
                    FStar_Syntax_Util.abs uu____3586 body ret_tot_type  in
                  let stronger1 =
                    let uu____3629 = mk_lid "stronger"  in
                    register env1 uu____3629 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3637 = FStar_Util.prefix gamma  in
                    match uu____3637 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3703 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3703
                             in
                          let uu____3708 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3708 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll
                              (binders1,attr,[],body)) ->
                              let k_app =
                                let uu____3723 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3723  in
                              let guard_free1 =
                                let uu____3735 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3735  in
                              let pat =
                                let uu____3739 =
                                  let uu____3750 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3750]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3739
                                 in
                              let pattern_guarded_body =
                                let uu____3778 =
                                  let uu____3779 =
                                    let uu____3786 =
                                      let uu____3787 =
                                        let uu____3812 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____3817 =
                                          let uu____3830 =
                                            let uu____3841 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____3841]  in
                                          [uu____3830]  in
                                        (attr, uu____3812, uu____3817)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3787
                                       in
                                    (body, uu____3786)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3779  in
                                mk1 uu____3778  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3906 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3915 =
                            let uu____3918 =
                              let uu____3919 =
                                let uu____3922 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3925 =
                                  let uu____3936 = args_of_binders1 wp_args
                                     in
                                  let uu____3939 =
                                    let uu____3942 =
                                      let uu____3943 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3943
                                       in
                                    [uu____3942]  in
                                  FStar_List.append uu____3936 uu____3939  in
                                FStar_Syntax_Util.mk_app uu____3922
                                  uu____3925
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3919  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3918
                             in
                          FStar_Syntax_Util.abs gamma uu____3915
                            ret_gtot_type
                           in
                        let uu____3944 =
                          let uu____3945 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3945  in
                        FStar_Syntax_Util.abs uu____3944 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3961 = mk_lid "ite_wp"  in
                    register env1 uu____3961 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3969 = FStar_Util.prefix gamma  in
                    match uu____3969 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____4027 =
                            let uu____4028 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____4035 =
                              let uu____4046 =
                                let uu____4055 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____4055  in
                              [uu____4046]  in
                            FStar_Syntax_Util.mk_app uu____4028 uu____4035
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____4027
                           in
                        let uu____4072 =
                          let uu____4073 =
                            let uu____4082 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____4082 gamma  in
                          FStar_List.append binders uu____4073  in
                        FStar_Syntax_Util.abs uu____4072 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____4104 = mk_lid "null_wp"  in
                    register env1 uu____4104 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4117 =
                        let uu____4128 =
                          let uu____4131 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4132 =
                            let uu____4135 =
                              let uu____4136 =
                                let uu____4147 =
                                  let uu____4156 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4156  in
                                [uu____4147]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4136
                               in
                            let uu____4173 =
                              let uu____4176 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4176]  in
                            uu____4135 :: uu____4173  in
                          uu____4131 :: uu____4132  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4128
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4117  in
                    let uu____4185 =
                      let uu____4186 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4186  in
                    FStar_Syntax_Util.abs uu____4185 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4202 = mk_lid "wp_trivial"  in
                    register env1 uu____4202 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4208 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4208
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4220 =
                      let uu____4221 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4221  in
                    let uu____4247 =
                      let uu___350_4248 = ed  in
                      let uu____4249 =
                        let uu____4250 = c wp_if_then_else2  in
                        ([], uu____4250)  in
                      let uu____4257 =
                        let uu____4258 = c ite_wp2  in ([], uu____4258)  in
                      let uu____4265 =
                        let uu____4266 = c stronger2  in ([], uu____4266)  in
                      let uu____4273 =
                        let uu____4274 = c wp_close2  in ([], uu____4274)  in
                      let uu____4281 =
                        let uu____4282 = c wp_assert2  in ([], uu____4282)
                         in
                      let uu____4289 =
                        let uu____4290 = c wp_assume2  in ([], uu____4290)
                         in
                      let uu____4297 =
                        let uu____4298 = c null_wp2  in ([], uu____4298)  in
                      let uu____4305 =
                        let uu____4306 = c wp_trivial2  in ([], uu____4306)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___350_4248.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___350_4248.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___350_4248.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___350_4248.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___350_4248.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___350_4248.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___350_4248.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4249;
                        FStar_Syntax_Syntax.ite_wp = uu____4257;
                        FStar_Syntax_Syntax.stronger = uu____4265;
                        FStar_Syntax_Syntax.close_wp = uu____4273;
                        FStar_Syntax_Syntax.assert_p = uu____4281;
                        FStar_Syntax_Syntax.assume_p = uu____4289;
                        FStar_Syntax_Syntax.null_wp = uu____4297;
                        FStar_Syntax_Syntax.trivial = uu____4305;
                        FStar_Syntax_Syntax.repr =
                          (uu___350_4248.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___350_4248.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___350_4248.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___350_4248.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___350_4248.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4220, uu____4247)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___355_4330 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___355_4330.subst);
        tc_const = (uu___355_4330.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4351 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4370 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4390) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4404  ->
                match uu___0_4404 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4407 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4409 ->
        let uu____4410 =
          let uu____4416 =
            let uu____4418 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4418
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4416)  in
        FStar_Errors.raise_error uu____4410 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4428  ->
    match uu___1_4428 with
    | N t ->
        let uu____4431 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4431
    | M t ->
        let uu____4435 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4435
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4444,c) -> nm_of_comp c
    | uu____4466 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4479 = nm_of_comp c  in
    match uu____4479 with | M uu____4481 -> true | N uu____4483 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4494 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4510 =
        let uu____4519 =
          let uu____4526 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4526  in
        [uu____4519]  in
      let uu____4545 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4510 uu____4545  in
    let uu____4548 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4548
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        let uu____4590 =
          let uu____4591 =
            let uu____4606 =
              let uu____4615 =
                let uu____4622 =
                  let uu____4623 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4623  in
                let uu____4624 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4622, uu____4624)  in
              [uu____4615]  in
            let uu____4642 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4606, uu____4642)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4591  in
        mk1 uu____4590

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4682) ->
          let binders1 =
            FStar_List.map
              (fun uu____4728  ->
                 match uu____4728 with
                 | (bv,aqual) ->
                     let uu____4747 =
                       let uu___405_4748 = bv  in
                       let uu____4749 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___405_4748.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___405_4748.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4749
                       }  in
                     (uu____4747, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4754,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4756);
                             FStar_Syntax_Syntax.pos = uu____4757;
                             FStar_Syntax_Syntax.vars = uu____4758;_})
               ->
               let uu____4787 =
                 let uu____4788 =
                   let uu____4803 =
                     let uu____4806 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4806  in
                   (binders1, uu____4803)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4788  in
               mk1 uu____4787
           | uu____4817 ->
               let uu____4818 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4818 with
                | N hn ->
                    let uu____4820 =
                      let uu____4821 =
                        let uu____4836 =
                          let uu____4839 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4839  in
                        (binders1, uu____4836)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4821  in
                    mk1 uu____4820
                | M a ->
                    let uu____4851 =
                      let uu____4852 =
                        let uu____4867 =
                          let uu____4876 =
                            let uu____4885 =
                              let uu____4892 =
                                let uu____4893 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4893  in
                              let uu____4894 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4892, uu____4894)  in
                            [uu____4885]  in
                          FStar_List.append binders1 uu____4876  in
                        let uu____4918 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4867, uu____4918)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4852  in
                    mk1 uu____4851))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____5012 = f x  in
                    FStar_Util.string_builder_append strb uu____5012);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____5021 = f x1  in
                         FStar_Util.string_builder_append strb uu____5021))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____5025 =
              let uu____5031 =
                let uu____5033 = FStar_Syntax_Print.term_to_string t2  in
                let uu____5035 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____5033 uu____5035
                 in
              (FStar_Errors.Warning_DependencyFound, uu____5031)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5025  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5057 =
              let uu____5058 = FStar_Syntax_Subst.compress ty  in
              uu____5058.FStar_Syntax_Syntax.n  in
            match uu____5057 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5084 =
                  let uu____5086 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5086  in
                if uu____5084
                then false
                else
                  (try
                     (fun uu___454_5103  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5127 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5127 s  in
                              let uu____5130 =
                                let uu____5132 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5132  in
                              if uu____5130
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5138 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5138 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5163  ->
                                          match uu____5163 with
                                          | (bv,uu____5175) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1
                                    in
                                 let ct = FStar_Syntax_Util.comp_result c1
                                    in
                                 (non_dependent_or_raise s ct;
                                  (let k = n1 - (FStar_List.length binders1)
                                      in
                                   if k > (Prims.parse_int "0")
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____5203 ->
                ((let uu____5205 =
                    let uu____5211 =
                      let uu____5213 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5213
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5211)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5205);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5229 =
              let uu____5230 = FStar_Syntax_Subst.compress head2  in
              uu____5230.FStar_Syntax_Syntax.n  in
            match uu____5229 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid))
                  ||
                  (let uu____5236 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5236)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5239 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5239 with
                 | ((uu____5249,ty),uu____5251) ->
                     let uu____5256 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5256
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5269 =
                         let uu____5270 = FStar_Syntax_Subst.compress res  in
                         uu____5270.FStar_Syntax_Syntax.n  in
                       (match uu____5269 with
                        | FStar_Syntax_Syntax.Tm_app uu____5274 -> true
                        | uu____5292 ->
                            ((let uu____5294 =
                                let uu____5300 =
                                  let uu____5302 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5302
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5300)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5294);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5310 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5312 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5315) ->
                is_valid_application t2
            | uu____5320 -> false  in
          let uu____5322 = is_valid_application head1  in
          if uu____5322
          then
            let uu____5325 =
              let uu____5326 =
                let uu____5343 =
                  FStar_List.map
                    (fun uu____5372  ->
                       match uu____5372 with
                       | (t2,qual) ->
                           let uu____5397 = star_type' env t2  in
                           (uu____5397, qual)) args
                   in
                (head1, uu____5343)  in
              FStar_Syntax_Syntax.Tm_app uu____5326  in
            mk1 uu____5325
          else
            (let uu____5414 =
               let uu____5420 =
                 let uu____5422 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5422
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5420)  in
             FStar_Errors.raise_err uu____5414)
      | FStar_Syntax_Syntax.Tm_bvar uu____5426 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5427 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5428 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5429 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5457 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5457 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___526_5465 = env  in
                 let uu____5466 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5466;
                   subst = (uu___526_5465.subst);
                   tc_const = (uu___526_5465.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)]
             in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))]
             in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___541_5493 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___541_5493.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___541_5493.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5500 =
            let uu____5501 =
              let uu____5508 = star_type' env t2  in (uu____5508, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5501  in
          mk1 uu____5500
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5560 =
            let uu____5561 =
              let uu____5588 = star_type' env e  in
              let uu____5591 =
                let uu____5608 =
                  let uu____5617 = star_type' env t2  in
                  FStar_Util.Inl uu____5617  in
                (uu____5608, FStar_Pervasives_Native.None)  in
              (uu____5588, uu____5591, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5561  in
          mk1 uu____5560
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5705 =
            let uu____5706 =
              let uu____5733 = star_type' env e  in
              let uu____5736 =
                let uu____5753 =
                  let uu____5762 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5762  in
                (uu____5753, FStar_Pervasives_Native.None)  in
              (uu____5733, uu____5736, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5706  in
          mk1 uu____5705
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5803,(uu____5804,FStar_Pervasives_Native.Some uu____5805),uu____5806)
          ->
          let uu____5855 =
            let uu____5861 =
              let uu____5863 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5863
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5861)  in
          FStar_Errors.raise_err uu____5855
      | FStar_Syntax_Syntax.Tm_refine uu____5867 ->
          let uu____5874 =
            let uu____5880 =
              let uu____5882 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5882
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5880)  in
          FStar_Errors.raise_err uu____5874
      | FStar_Syntax_Syntax.Tm_uinst uu____5886 ->
          let uu____5893 =
            let uu____5899 =
              let uu____5901 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5901
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5899)  in
          FStar_Errors.raise_err uu____5893
      | FStar_Syntax_Syntax.Tm_quoted uu____5905 ->
          let uu____5912 =
            let uu____5918 =
              let uu____5920 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5920
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5918)  in
          FStar_Errors.raise_err uu____5912
      | FStar_Syntax_Syntax.Tm_constant uu____5924 ->
          let uu____5925 =
            let uu____5931 =
              let uu____5933 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5933
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5931)  in
          FStar_Errors.raise_err uu____5925
      | FStar_Syntax_Syntax.Tm_match uu____5937 ->
          let uu____5960 =
            let uu____5966 =
              let uu____5968 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5968
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5966)  in
          FStar_Errors.raise_err uu____5960
      | FStar_Syntax_Syntax.Tm_let uu____5972 ->
          let uu____5986 =
            let uu____5992 =
              let uu____5994 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5994
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5992)  in
          FStar_Errors.raise_err uu____5986
      | FStar_Syntax_Syntax.Tm_uvar uu____5998 ->
          let uu____6011 =
            let uu____6017 =
              let uu____6019 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____6019
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6017)  in
          FStar_Errors.raise_err uu____6011
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6023 =
            let uu____6029 =
              let uu____6031 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____6031
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6029)  in
          FStar_Errors.raise_err uu____6023
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6036 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____6036
      | FStar_Syntax_Syntax.Tm_delayed uu____6039 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_6071  ->
    match uu___3_6071 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_6082  ->
                match uu___2_6082 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6085 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6095 =
      let uu____6096 = FStar_Syntax_Subst.compress t  in
      uu____6096.FStar_Syntax_Syntax.n  in
    match uu____6095 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6128 =
            let uu____6129 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6129  in
          is_C uu____6128  in
        if r
        then
          ((let uu____6153 =
              let uu____6155 =
                FStar_List.for_all
                  (fun uu____6166  ->
                     match uu____6166 with | (h,uu____6175) -> is_C h) args
                 in
              Prims.op_Negation uu____6155  in
            if uu____6153 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6188 =
              let uu____6190 =
                FStar_List.for_all
                  (fun uu____6202  ->
                     match uu____6202 with
                     | (h,uu____6211) ->
                         let uu____6216 = is_C h  in
                         Prims.op_Negation uu____6216) args
                 in
              Prims.op_Negation uu____6190  in
            if uu____6188 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6245 = nm_of_comp comp  in
        (match uu____6245 with
         | M t1 ->
             ((let uu____6249 = is_C t1  in
               if uu____6249 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6258) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6264) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6270,uu____6271) -> is_C t1
    | uu____6312 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____6348 =
            let uu____6349 =
              let uu____6366 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6369 =
                let uu____6380 =
                  let uu____6389 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6389)  in
                [uu____6380]  in
              (uu____6366, uu____6369)  in
            FStar_Syntax_Syntax.Tm_app uu____6349  in
          mk1 uu____6348  in
        let uu____6425 =
          let uu____6426 = FStar_Syntax_Syntax.mk_binder p  in [uu____6426]
           in
        FStar_Syntax_Util.abs uu____6425 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6451  ->
    match uu___4_6451 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6454 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6692 =
          match uu____6692 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6729 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6732 =
                       let uu____6734 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6734  in
                     Prims.op_Negation uu____6732)
                   in
                if uu____6729
                then
                  let uu____6736 =
                    let uu____6742 =
                      let uu____6744 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6746 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6748 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6744 uu____6746 uu____6748
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6742)  in
                  FStar_Errors.raise_err uu____6736
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6773 = mk_return env t1 s_e  in
                     ((M t1), uu____6773, u_e)))
               | (M t1,N t2) ->
                   let uu____6780 =
                     let uu____6786 =
                       let uu____6788 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6790 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6792 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6788 uu____6790 uu____6792
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6786)
                      in
                   FStar_Errors.raise_err uu____6780)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6844 =
            match uu___5_6844 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6860 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6881 =
                let uu____6887 =
                  let uu____6889 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6889
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6887)  in
              FStar_Errors.raise_error uu____6881 e2.FStar_Syntax_Syntax.pos
          | M uu____6899 ->
              let uu____6900 = check env1 e2 context_nm  in
              strip_m uu____6900
           in
        let uu____6907 =
          let uu____6908 = FStar_Syntax_Subst.compress e  in
          uu____6908.FStar_Syntax_Syntax.n  in
        match uu____6907 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6917 ->
            let uu____6918 = infer env e  in return_if uu____6918
        | FStar_Syntax_Syntax.Tm_name uu____6925 ->
            let uu____6926 = infer env e  in return_if uu____6926
        | FStar_Syntax_Syntax.Tm_fvar uu____6933 ->
            let uu____6934 = infer env e  in return_if uu____6934
        | FStar_Syntax_Syntax.Tm_abs uu____6941 ->
            let uu____6960 = infer env e  in return_if uu____6960
        | FStar_Syntax_Syntax.Tm_constant uu____6967 ->
            let uu____6968 = infer env e  in return_if uu____6968
        | FStar_Syntax_Syntax.Tm_quoted uu____6975 ->
            let uu____6982 = infer env e  in return_if uu____6982
        | FStar_Syntax_Syntax.Tm_app uu____6989 ->
            let uu____7006 = infer env e  in return_if uu____7006
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____7014 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____7014 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7079) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7085) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7091,uu____7092) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7133 ->
            let uu____7147 =
              let uu____7149 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7149  in
            failwith uu____7147
        | FStar_Syntax_Syntax.Tm_type uu____7158 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7166 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7188 ->
            let uu____7195 =
              let uu____7197 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7197  in
            failwith uu____7195
        | FStar_Syntax_Syntax.Tm_uvar uu____7206 ->
            let uu____7219 =
              let uu____7221 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7221  in
            failwith uu____7219
        | FStar_Syntax_Syntax.Tm_delayed uu____7230 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7260 =
              let uu____7262 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7262  in
            failwith uu____7260

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.tcenv
         in
      let uu____7292 =
        let uu____7293 = FStar_Syntax_Subst.compress e  in
        uu____7293.FStar_Syntax_Syntax.n  in
      match uu____7292 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7312 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7312
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7363;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7364;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7370 =
                  let uu___776_7371 = rc  in
                  let uu____7372 =
                    let uu____7377 =
                      let uu____7380 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7380  in
                    FStar_Pervasives_Native.Some uu____7377  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___776_7371.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7372;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___776_7371.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7370
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___782_7392 = env  in
            let uu____7393 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7393;
              subst = (uu___782_7392.subst);
              tc_const = (uu___782_7392.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7419  ->
                 match uu____7419 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___789_7442 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___789_7442.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___789_7442.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7443 =
            FStar_List.fold_left
              (fun uu____7474  ->
                 fun uu____7475  ->
                   match (uu____7474, uu____7475) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7533 = is_C c  in
                       if uu____7533
                       then
                         let xw =
                           let uu____7543 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7543
                            in
                         let x =
                           let uu___801_7546 = bv  in
                           let uu____7547 =
                             let uu____7550 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7550  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___801_7546.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___801_7546.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7547
                           }  in
                         let env3 =
                           let uu___804_7552 = env2  in
                           let uu____7553 =
                             let uu____7556 =
                               let uu____7557 =
                                 let uu____7564 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7564)  in
                               FStar_Syntax_Syntax.NT uu____7557  in
                             uu____7556 :: (env2.subst)  in
                           {
                             tcenv = (uu___804_7552.tcenv);
                             subst = uu____7553;
                             tc_const = (uu___804_7552.tc_const)
                           }  in
                         let uu____7569 =
                           let uu____7572 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7573 =
                             let uu____7576 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7576 :: acc  in
                           uu____7572 :: uu____7573  in
                         (env3, uu____7569)
                       else
                         (let x =
                            let uu___807_7582 = bv  in
                            let uu____7583 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___807_7582.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___807_7582.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7583
                            }  in
                          let uu____7586 =
                            let uu____7589 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7589 :: acc  in
                          (env2, uu____7586))) (env1, []) binders1
             in
          (match uu____7443 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7609 =
                 let check_what =
                   let uu____7635 = is_monadic rc_opt1  in
                   if uu____7635 then check_m else check_n  in
                 let uu____7652 = check_what env2 body1  in
                 match uu____7652 with
                 | (t,s_body,u_body) ->
                     let uu____7672 =
                       let uu____7675 =
                         let uu____7676 = is_monadic rc_opt1  in
                         if uu____7676 then M t else N t  in
                       comp_of_nm uu____7675  in
                     (uu____7672, s_body, u_body)
                  in
               (match uu____7609 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____7716 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7722  ->
                                           match uu___6_7722 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7725 -> false))
                                    in
                                 if uu____7716
                                 then
                                   let uu____7728 =
                                     FStar_List.filter
                                       (fun uu___7_7732  ->
                                          match uu___7_7732 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7735 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7728
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7746 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7752  ->
                                         match uu___8_7752 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7755 -> false))
                                  in
                               if uu____7746
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7764  ->
                                        match uu___9_7764 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7767 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7769 =
                                   let uu____7770 =
                                     let uu____7775 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7775
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7770 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7769
                               else
                                 (let uu____7782 =
                                    let uu___848_7783 = rc  in
                                    let uu____7784 =
                                      let uu____7789 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7789
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___848_7783.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7784;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___848_7783.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7782))
                       in
                    let uu____7794 =
                      let comp1 =
                        let uu____7802 = is_monadic rc_opt1  in
                        let uu____7804 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7802 uu____7804
                         in
                      let uu____7805 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7805,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7794 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7843 =
                             let uu____7844 =
                               let uu____7863 =
                                 let uu____7866 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7866 s_rc_opt  in
                               (s_binders1, s_body1, uu____7863)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7844  in
                           mk1 uu____7843  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7886 =
                             let uu____7887 =
                               let uu____7906 =
                                 let uu____7909 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7909 u_rc_opt  in
                               (u_binders2, u_body2, uu____7906)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7887  in
                           mk1 uu____7886  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7925;_};
            FStar_Syntax_Syntax.fv_delta = uu____7926;
            FStar_Syntax_Syntax.fv_qual = uu____7927;_}
          ->
          let uu____7930 =
            let uu____7935 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7935  in
          (match uu____7930 with
           | (uu____7966,t) ->
               let uu____7968 =
                 let uu____7969 = normalize1 t  in N uu____7969  in
               (uu____7968, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7970;
             FStar_Syntax_Syntax.vars = uu____7971;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8050 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8050 with
           | (unary_op1,uu____8074) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8145;
             FStar_Syntax_Syntax.vars = uu____8146;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8242 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8242 with
           | (unary_op1,uu____8266) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8345;
             FStar_Syntax_Syntax.vars = uu____8346;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8384 = infer env a  in
          (match uu____8384 with
           | (t,s,u) ->
               let uu____8400 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8400 with
                | (head1,uu____8424) ->
                    let uu____8449 =
                      let uu____8450 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8450  in
                    let uu____8451 =
                      let uu____8452 =
                        let uu____8453 =
                          let uu____8470 =
                            let uu____8481 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8481]  in
                          (head1, uu____8470)  in
                        FStar_Syntax_Syntax.Tm_app uu____8453  in
                      mk1 uu____8452  in
                    let uu____8518 =
                      let uu____8519 =
                        let uu____8520 =
                          let uu____8537 =
                            let uu____8548 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8548]  in
                          (head1, uu____8537)  in
                        FStar_Syntax_Syntax.Tm_app uu____8520  in
                      mk1 uu____8519  in
                    (uu____8449, uu____8451, uu____8518)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8585;
             FStar_Syntax_Syntax.vars = uu____8586;_},(a1,uu____8588)::a2::[])
          ->
          let uu____8644 = infer env a1  in
          (match uu____8644 with
           | (t,s,u) ->
               let uu____8660 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8660 with
                | (head1,uu____8684) ->
                    let uu____8709 =
                      let uu____8710 =
                        let uu____8711 =
                          let uu____8728 =
                            let uu____8739 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8739; a2]  in
                          (head1, uu____8728)  in
                        FStar_Syntax_Syntax.Tm_app uu____8711  in
                      mk1 uu____8710  in
                    let uu____8784 =
                      let uu____8785 =
                        let uu____8786 =
                          let uu____8803 =
                            let uu____8814 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8814; a2]  in
                          (head1, uu____8803)  in
                        FStar_Syntax_Syntax.Tm_app uu____8786  in
                      mk1 uu____8785  in
                    (t, uu____8709, uu____8784)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8859;
             FStar_Syntax_Syntax.vars = uu____8860;_},uu____8861)
          ->
          let uu____8886 =
            let uu____8892 =
              let uu____8894 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8894
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8892)  in
          FStar_Errors.raise_error uu____8886 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8904;
             FStar_Syntax_Syntax.vars = uu____8905;_},uu____8906)
          ->
          let uu____8931 =
            let uu____8937 =
              let uu____8939 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8939
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8937)  in
          FStar_Errors.raise_error uu____8931 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8975 = check_n env head1  in
          (match uu____8975 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8998 =
                   let uu____8999 = FStar_Syntax_Subst.compress t  in
                   uu____8999.FStar_Syntax_Syntax.n  in
                 match uu____8998 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____9003 -> true
                 | uu____9019 -> false  in
               let rec flatten1 t =
                 let uu____9041 =
                   let uu____9042 = FStar_Syntax_Subst.compress t  in
                   uu____9042.FStar_Syntax_Syntax.n  in
                 match uu____9041 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9061);
                                FStar_Syntax_Syntax.pos = uu____9062;
                                FStar_Syntax_Syntax.vars = uu____9063;_})
                     when is_arrow t1 ->
                     let uu____9092 = flatten1 t1  in
                     (match uu____9092 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9192,uu____9193)
                     -> flatten1 e1
                 | uu____9234 ->
                     let uu____9235 =
                       let uu____9241 =
                         let uu____9243 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9243
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9241)  in
                     FStar_Errors.raise_err uu____9235
                  in
               let uu____9261 = flatten1 t_head  in
               (match uu____9261 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9336 =
                          let uu____9342 =
                            let uu____9344 = FStar_Util.string_of_int n1  in
                            let uu____9346 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9348 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9344 uu____9346 uu____9348
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9342)
                           in
                        FStar_Errors.raise_err uu____9336)
                     else ();
                     (let uu____9354 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9354 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9407 args1 =
                            match uu____9407 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9507 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9507
                                 | (binders3,[]) ->
                                     let uu____9545 =
                                       let uu____9546 =
                                         let uu____9549 =
                                           let uu____9550 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9550
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9549
                                          in
                                       uu____9546.FStar_Syntax_Syntax.n  in
                                     (match uu____9545 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9583 =
                                            let uu____9584 =
                                              let uu____9585 =
                                                let uu____9600 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9600)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9585
                                               in
                                            mk1 uu____9584  in
                                          N uu____9583
                                      | uu____9613 -> failwith "wat?")
                                 | ([],uu____9615::uu____9616) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9669)::binders3,(arg,uu____9672)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9759 = FStar_List.splitAt n' binders1  in
                          (match uu____9759 with
                           | (binders2,uu____9793) ->
                               let uu____9826 =
                                 let uu____9849 =
                                   FStar_List.map2
                                     (fun uu____9911  ->
                                        fun uu____9912  ->
                                          match (uu____9911, uu____9912) with
                                          | ((bv,uu____9960),(arg,q)) ->
                                              let uu____9989 =
                                                let uu____9990 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9990.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9989 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____10011 ->
                                                   let uu____10012 =
                                                     let uu____10019 =
                                                       star_type' env arg  in
                                                     (uu____10019, q)  in
                                                   (uu____10012, [(arg, q)])
                                               | uu____10056 ->
                                                   let uu____10057 =
                                                     check_n env arg  in
                                                   (match uu____10057 with
                                                    | (uu____10082,s_arg,u_arg)
                                                        ->
                                                        let uu____10085 =
                                                          let uu____10094 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10094
                                                          then
                                                            let uu____10105 =
                                                              let uu____10112
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10112,
                                                                q)
                                                               in
                                                            [uu____10105;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10085))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9849  in
                               (match uu____9826 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10240 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10253 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10240, uu____10253)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10322) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10328) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10334,uu____10335) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10377 =
            let uu____10378 = env.tc_const c  in N uu____10378  in
          (uu____10377, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10385 ->
          let uu____10399 =
            let uu____10401 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10401  in
          failwith uu____10399
      | FStar_Syntax_Syntax.Tm_type uu____10410 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10418 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10440 ->
          let uu____10447 =
            let uu____10449 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10449  in
          failwith uu____10447
      | FStar_Syntax_Syntax.Tm_uvar uu____10458 ->
          let uu____10471 =
            let uu____10473 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10473  in
          failwith uu____10471
      | FStar_Syntax_Syntax.Tm_delayed uu____10482 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10512 =
            let uu____10514 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10514  in
          failwith uu____10512

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____10563 = check_n env e0  in
          match uu____10563 with
          | (uu____10576,s_e0,u_e0) ->
              let uu____10579 =
                let uu____10608 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10669 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10669 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1123_10711 = env  in
                             let uu____10712 =
                               let uu____10713 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10713
                                in
                             {
                               tcenv = uu____10712;
                               subst = (uu___1123_10711.subst);
                               tc_const = (uu___1123_10711.tc_const)
                             }  in
                           let uu____10716 = f env1 body  in
                           (match uu____10716 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10788 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10608  in
              (match uu____10579 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10894 = FStar_List.hd nms  in
                     match uu____10894 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10903  ->
                          match uu___10_10903 with
                          | M uu____10905 -> true
                          | uu____10907 -> false) nms
                      in
                   let uu____10909 =
                     let uu____10946 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____11036  ->
                              match uu____11036 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11220 =
                                         check env original_body (M t2)  in
                                       (match uu____11220 with
                                        | (uu____11257,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11296,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10946  in
                   (match uu____10909 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____11485  ->
                                 match uu____11485 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11536 =
                                         let uu____11537 =
                                           let uu____11554 =
                                             let uu____11565 =
                                               let uu____11574 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11577 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11574, uu____11577)  in
                                             [uu____11565]  in
                                           (s_body, uu____11554)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11537
                                          in
                                       mk1 uu____11536  in
                                     (pat, guard, s_body1)) s_branches
                             in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1
                             in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let uu____11712 =
                              let uu____11713 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11713]  in
                            let uu____11732 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11712 uu____11732
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11756 =
                              let uu____11765 =
                                let uu____11772 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11772
                                 in
                              [uu____11765]  in
                            let uu____11791 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11756 uu____11791
                             in
                          let uu____11794 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11833 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11794, uu____11833)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let uu____11943 =
                             let uu____11944 =
                               let uu____11945 =
                                 let uu____11972 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11972,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11945
                                in
                             mk1 uu____11944  in
                           let uu____12031 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11943, uu____12031))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
                 FStar_Syntax_Syntax.term))
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____12096 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12096]  in
            let uu____12115 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12115 with
            | (x_binders1,e21) ->
                let uu____12128 = infer env e1  in
                (match uu____12128 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12145 = is_C t1  in
                       if uu____12145
                       then
                         let uu___1209_12148 = binding  in
                         let uu____12149 =
                           let uu____12152 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12152  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1209_12148.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1209_12148.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12149;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1209_12148.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1209_12148.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1209_12148.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1209_12148.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1212_12156 = env  in
                       let uu____12157 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1214_12159 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1214_12159.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1214_12159.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12157;
                         subst = (uu___1212_12156.subst);
                         tc_const = (uu___1212_12156.tc_const)
                       }  in
                     let uu____12160 = proceed env1 e21  in
                     (match uu____12160 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1221_12177 = binding  in
                            let uu____12178 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1221_12177.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1221_12177.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12178;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1221_12177.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1221_12177.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1221_12177.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1221_12177.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12181 =
                            let uu____12182 =
                              let uu____12183 =
                                let uu____12197 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1224_12214 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1224_12214.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1224_12214.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1224_12214.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1224_12214.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1224_12214.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1224_12214.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12197)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12183  in
                            mk1 uu____12182  in
                          let uu____12215 =
                            let uu____12216 =
                              let uu____12217 =
                                let uu____12231 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1226_12248 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1226_12248.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1226_12248.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1226_12248.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1226_12248.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1226_12248.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1226_12248.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12231)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12217  in
                            mk1 uu____12216  in
                          (nm_rec, uu____12181, uu____12215))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1233_12253 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1233_12253.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1233_12253.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1233_12253.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1233_12253.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1233_12253.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1236_12255 = env  in
                       let uu____12256 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1238_12258 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1238_12258.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1238_12258.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12256;
                         subst = (uu___1236_12255.subst);
                         tc_const = (uu___1236_12255.tc_const)
                       }  in
                     let uu____12259 = ensure_m env1 e21  in
                     (match uu____12259 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12283 =
                              let uu____12284 =
                                let uu____12301 =
                                  let uu____12312 =
                                    let uu____12321 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12324 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12321, uu____12324)  in
                                  [uu____12312]  in
                                (s_e2, uu____12301)  in
                              FStar_Syntax_Syntax.Tm_app uu____12284  in
                            mk1 uu____12283  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12366 =
                              let uu____12367 =
                                let uu____12384 =
                                  let uu____12395 =
                                    let uu____12404 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12404)  in
                                  [uu____12395]  in
                                (s_e1, uu____12384)  in
                              FStar_Syntax_Syntax.Tm_app uu____12367  in
                            mk1 uu____12366  in
                          let uu____12440 =
                            let uu____12441 =
                              let uu____12442 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12442]  in
                            FStar_Syntax_Util.abs uu____12441 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12461 =
                            let uu____12462 =
                              let uu____12463 =
                                let uu____12477 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1250_12494 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1250_12494.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1250_12494.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1250_12494.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1250_12494.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1250_12494.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1250_12494.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12477)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12463  in
                            mk1 uu____12462  in
                          ((M t2), uu____12440, uu____12461)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12504 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12504  in
      let uu____12505 = check env e mn  in
      match uu____12505 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12521 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12544 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12544  in
      let uu____12545 = check env e mn  in
      match uu____12545 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12561 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid;
        FStar_Syntax_Syntax.result_typ = t;
        FStar_Syntax_Syntax.effect_args = [];
        FStar_Syntax_Syntax.flags =
          [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
      }

and (type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun t  -> FStar_Syntax_Util.comp_result t

and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____12594 =
           let uu____12596 = is_C c  in Prims.op_Negation uu____12596  in
         if uu____12594 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12610 =
           let uu____12611 = FStar_Syntax_Subst.compress c  in
           uu____12611.FStar_Syntax_Syntax.n  in
         match uu____12610 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12640 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12640 with
              | (wp_head,wp_args) ->
                  ((let uu____12684 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12703 =
                           let uu____12705 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12705
                            in
                         Prims.op_Negation uu____12703)
                       in
                    if uu____12684 then failwith "mismatch" else ());
                   (let uu____12718 =
                      let uu____12719 =
                        let uu____12736 =
                          FStar_List.map2
                            (fun uu____12774  ->
                               fun uu____12775  ->
                                 match (uu____12774, uu____12775) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12837 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12837
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12846 =
                                         let uu____12848 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12848 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12846
                                       then
                                         let uu____12850 =
                                           let uu____12856 =
                                             let uu____12858 =
                                               print_implicit q  in
                                             let uu____12860 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12858 uu____12860
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12856)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12850
                                       else ());
                                      (let uu____12866 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12866, q)))) args wp_args
                           in
                        (head1, uu____12736)  in
                      FStar_Syntax_Syntax.Tm_app uu____12719  in
                    mk1 uu____12718)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12912 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12912 with
              | (binders_orig,comp1) ->
                  let uu____12919 =
                    let uu____12936 =
                      FStar_List.map
                        (fun uu____12976  ->
                           match uu____12976 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____13004 = is_C h  in
                               if uu____13004
                               then
                                 let w' =
                                   let uu____13020 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____13020
                                    in
                                 let uu____13022 =
                                   let uu____13031 =
                                     let uu____13040 =
                                       let uu____13047 =
                                         let uu____13048 =
                                           let uu____13049 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____13049  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____13048
                                          in
                                       (uu____13047, q)  in
                                     [uu____13040]  in
                                   (w', q) :: uu____13031  in
                                 (w', uu____13022)
                               else
                                 (let x =
                                    let uu____13083 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13083
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12936  in
                  (match uu____12919 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13157 =
                           let uu____13160 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13160
                            in
                         FStar_Syntax_Subst.subst_comp uu____13157 comp1  in
                       let app =
                         let uu____13164 =
                           let uu____13165 =
                             let uu____13182 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13201 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13202 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13201, uu____13202)) bvs
                                in
                             (wp, uu____13182)  in
                           FStar_Syntax_Syntax.Tm_app uu____13165  in
                         mk1 uu____13164  in
                       let comp3 =
                         let uu____13217 = type_of_comp comp2  in
                         let uu____13218 = is_monadic_comp comp2  in
                         trans_G env uu____13217 uu____13218 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13221,uu____13222) ->
             trans_F_ env e wp
         | uu____13263 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____13271 =
              let uu____13272 = star_type' env h  in
              let uu____13275 =
                let uu____13286 =
                  let uu____13295 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13295)  in
                [uu____13286]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13272;
                FStar_Syntax_Syntax.effect_args = uu____13275;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13271
          else
            (let uu____13321 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13321)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____13342 = n env.tcenv t  in star_type' env uu____13342
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13362 = n env.tcenv t  in check_n env uu____13362
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13379 = n env.tcenv c  in
        let uu____13380 = n env.tcenv wp  in
        trans_F_ env uu____13379 uu____13380
  