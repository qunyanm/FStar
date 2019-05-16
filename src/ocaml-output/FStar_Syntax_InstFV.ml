open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____14 'Auu____15 .
    'Auu____14 FStar_Syntax_Syntax.syntax ->
      'Auu____15 -> 'Auu____15 FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
  
let rec (inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let mk1 = mk t1  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____145 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____169 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____170 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____183 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____196 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____197 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____198 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____199 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____206 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____213 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____244 =
            let uu____245 =
              let uu____264 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____264)  in
            FStar_Syntax_Syntax.Tm_abs uu____245  in
          mk1 uu____244
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___47_322 = bv  in
            let uu____323 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___47_322.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___47_322.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____323
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____355 =
            let uu____356 =
              let uu____373 = inst s t2  in
              let uu____376 = inst_args s args  in (uu____373, uu____376)  in
            FStar_Syntax_Syntax.Tm_app uu____356  in
          mk1 uu____355
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____508  ->
                    match uu____508 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____546 = inst s w  in
                              FStar_Pervasives_Native.Some uu____546
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____552 =
            let uu____553 = let uu____576 = inst s t2  in (uu____576, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____553  in
          mk1 uu____552
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____669 =
            match uu____669 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____731 = inst s t2  in FStar_Util.Inl uu____731
                  | FStar_Util.Inr c ->
                      let uu____739 = inst_comp s c  in
                      FStar_Util.Inr uu____739
                   in
                (annot1, topt1)
             in
          let uu____752 =
            let uu____753 =
              let uu____780 = inst s t11  in
              let uu____783 = inst_asc asc  in (uu____780, uu____783, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____753  in
          mk1 uu____752
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____848 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___89_863 = lb  in
                      let uu____864 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____867 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___89_863.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___89_863.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____864;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___89_863.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____867;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___89_863.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___89_863.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____848)  in
          let uu____876 =
            let uu____877 = let uu____891 = inst s t2  in (lbs1, uu____891)
               in
            FStar_Syntax_Syntax.Tm_let uu____877  in
          mk1 uu____876
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (attr,bvs,args)) ->
          let uu____947 =
            let uu____948 =
              let uu____955 = inst s t2  in
              let uu____958 =
                let uu____959 =
                  let uu____984 =
                    FStar_All.pipe_right args (FStar_List.map (inst_args s))
                     in
                  (attr, bvs, uu____984)  in
                FStar_Syntax_Syntax.Meta_pattern uu____959  in
              (uu____955, uu____958)  in
            FStar_Syntax_Syntax.Tm_meta uu____948  in
          mk1 uu____947
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____1072 =
            let uu____1073 =
              let uu____1080 = inst s t2  in
              let uu____1083 =
                let uu____1084 =
                  let uu____1091 = inst s t'  in (m, uu____1091)  in
                FStar_Syntax_Syntax.Meta_monadic uu____1084  in
              (uu____1080, uu____1083)  in
            FStar_Syntax_Syntax.Tm_meta uu____1073  in
          mk1 uu____1072
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____1104 =
            let uu____1105 = let uu____1112 = inst s t2  in (uu____1112, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____1105  in
          mk1 uu____1104

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1147  ->
              match uu____1147 with
              | (x,imp) ->
                  let uu____1166 =
                    let uu___116_1167 = x  in
                    let uu____1168 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___116_1167.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___116_1167.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1168
                    }  in
                  (uu____1166, imp)))

and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list)
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1223  ->
              match uu____1223 with
              | (a,imp) -> let uu____1242 = inst s a  in (uu____1242, imp)))

and (inst_comp :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____1265 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1265 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1276 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1276 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___135_1279 = ct  in
            let uu____1280 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1283 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1294 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___0_1304  ->
                      match uu___0_1304 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1308 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1308
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___135_1279.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___135_1279.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1280;
              FStar_Syntax_Syntax.effect_args = uu____1283;
              FStar_Syntax_Syntax.flags = uu____1294
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and (inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____1323 =
            let uu___147_1324 = rc  in
            let uu____1325 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___147_1324.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1325;
              FStar_Syntax_Syntax.residual_flags =
                (uu___147_1324.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1323

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1349 ->
          let inst_fv t1 fv =
            let uu____1361 =
              FStar_Util.find_opt
                (fun uu____1375  ->
                   match uu____1375 with
                   | (x,uu____1382) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1361 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1387,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  