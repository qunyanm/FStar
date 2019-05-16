open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)) =
  let uu____12 = FStar_Syntax_Syntax.new_fv_set ()  in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____12)
  
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun fv  ->
    let uu____29 =
      let uu____32 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____32
       in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____29)
  
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___2_54 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___2_54.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___2_54.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___2_54.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_uv :
  FStar_Syntax_Syntax.ctx_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___5_74 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___5_74.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___5_74.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___5_74.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___8_94 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___8_94.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___8_94.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___8_94.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___11_114 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___11_114.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___11_114.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___11_114.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun f1  ->
    fun f2  ->
      let uu____136 =
        FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
          (FStar_Pervasives_Native.snd f2)
         in
      ({
         FStar_Syntax_Syntax.free_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names);
         FStar_Syntax_Syntax.free_uvars =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars);
         FStar_Syntax_Syntax.free_univs =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs);
         FStar_Syntax_Syntax.free_univ_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)
       }, uu____136)
  
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u  ->
    let uu____167 = FStar_Syntax_Subst.compress_univ u  in
    match uu____167 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____168 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____180 = free_univs x  in union out uu____180)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
  
let rec (free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars) =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1  ->
                  fun uu____321  ->
                    match uu____321 with
                    | (x,uu____329) ->
                        let uu____334 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____334) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____336 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv,uu____362) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____380 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____382 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____383 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____396 = free_univs u  in union out uu____396)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____399) ->
          let uu____424 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____424
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____447 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____447
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____454 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____454
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____495 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____495 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____540 =
            let uu____559 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____582  ->
                   match uu____582 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____620 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____620
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____630 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____630) n1)
                          in
                       let uu____631 = union n11 n2  in union n3 uu____631)
              uu____559
             in
          FStar_All.pipe_right pats uu____540
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____648) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____736 = union u1 u2  in
               let uu____737 = free_names_and_uvars tac use_cache  in
               union uu____736 uu____737)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____758 =
            let uu____765 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____771 =
                     let uu____772 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____773 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____772 uu____773  in
                   union n1 uu____771) uu____765
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____758
      | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static  -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____792,uu____793,args) ->
               FStar_List.fold_right
                 (fun a  ->
                    fun acc  -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____867,t') ->
               let uu____873 = free_names_and_uvars t' use_cache  in
               union u1 uu____873
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____874,uu____875,t')
               ->
               let uu____881 = free_names_and_uvars t' use_cache  in
               union u1 uu____881
           | FStar_Syntax_Syntax.Meta_labeled uu____882 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____891 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____892 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____899 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____899 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____926 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____926 ->
          let uu____928 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____928)
      | uu____933 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache  in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))

and (free_names_and_uvars_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1037  ->
                  match uu____1037 with
                  | (x,uu____1047) ->
                      let uu____1056 = free_names_and_uvars x use_cache  in
                      union n1 uu____1056) acc)

and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1081  ->
                  match uu____1081 with
                  | (x,uu____1089) ->
                      let uu____1094 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____1094) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1100 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____1100 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1127 = should_invalidate_cache n1 use_cache  in
          if uu____1127
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1156 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____1156))
      | uu____1161 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1199 = free_univs u  in
                let uu____1200 = free_names_and_uvars t use_cache  in
                union uu____1199 uu____1200
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1209 = free_univs u  in
                let uu____1210 = free_names_and_uvars t use_cache  in
                union uu____1209 uu____1210
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1219 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1219 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1231 = free_univs u  in union us1 uu____1231)
                  us ct.FStar_Syntax_Syntax.comp_univs
             in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)

and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun u  ->
                  let uu____1268 =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head
                     in
                  match uu____1268 with
                  | FStar_Pervasives_Native.Some uu____1272 -> true
                  | uu____1274 -> false)))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1285 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____1285 with
                    | FStar_Pervasives_Native.Some uu____1289 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1304 =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head
         in
      let uu____1306 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head
         in
      uu____1304 - uu____1306
  
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1313  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____1326 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____1328 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____1326 - uu____1328
  
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1337  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1351 =
      let uu____1354 =
        let uu____1355 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1355  in
      uu____1354.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1351 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t  ->
    let uu____1373 =
      let uu____1376 =
        let uu____1377 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1377  in
      uu____1376.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1373 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____1395 =
      let uu____1398 =
        let uu____1399 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1399  in
      uu____1398.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____1395 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____1417 =
      let uu____1420 =
        let uu____1421 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1421  in
      uu____1420.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1417 FStar_Syntax_Syntax.order_univ_name
  
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c  ->
    let uu____1439 =
      let uu____1442 =
        let uu____1443 = free_names_and_uvars_comp c true  in
        FStar_Pervasives_Native.fst uu____1443  in
      uu____1442.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1439 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____1461 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____1461
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____1479 =
      let uu____1482 =
        let uu____1483 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____1483  in
      uu____1482.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1479 FStar_Syntax_Syntax.order_bv
  