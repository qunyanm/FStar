open Prims
let mkForall_fuel' :
  'Auu____14 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____14 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____45  ->
          match uu____45 with
          | (pats,vars,body) ->
              let fallback uu____73 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____78 = FStar_Options.unthrottle_inductives ()  in
              if uu____78
              then fallback ()
              else
                (let uu____83 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____83 with
                 | (fsym,fterm) ->
                     let add_fuel1 tms =
                       FStar_All.pipe_right tms
                         (FStar_List.map
                            (fun p  ->
                               match p.FStar_SMTEncoding_Term.tm with
                               | FStar_SMTEncoding_Term.App
                                   (FStar_SMTEncoding_Term.Var
                                    "HasType",args)
                                   ->
                                   FStar_SMTEncoding_Util.mkApp
                                     ("HasTypeFuel", (fterm :: args))
                               | uu____123 -> p))
                        in
                     let pats1 = FStar_List.map add_fuel1 pats  in
                     let body1 =
                       match body.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                           let guard1 =
                             match guard.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.And ,guards) ->
                                 let uu____144 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____144
                             | uu____147 ->
                                 let uu____148 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____148 FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____153 -> body  in
                     let vars1 =
                       let uu____165 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____165 :: vars  in
                     FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
  
let (mkForall_fuel :
  Prims.string ->
    FStar_Range.range ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
        FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
        FStar_SMTEncoding_Term.term)
  = fun mname  -> fun r  -> mkForall_fuel' mname r (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____229 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____245 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____253 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____255 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____269 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____289 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____292 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____292 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____311;
             FStar_Syntax_Syntax.vars = uu____312;_},uu____313)
          ->
          let uu____338 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____338 FStar_Option.isNone
      | uu____356 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____370 =
        let uu____371 = FStar_Syntax_Util.un_uinst t  in
        uu____371.FStar_Syntax_Syntax.n  in
      match uu____370 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____375,uu____376,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_401  ->
                  match uu___0_401 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____404 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____407 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____407 FStar_Option.isSome
      | uu____425 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____438 = head_normal env t  in
      if uu____438
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses]
          env.FStar_SMTEncoding_Env.tcenv t
  
let (norm :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Env.Beta;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
        FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.EraseUniverses] env.FStar_SMTEncoding_Env.tcenv
        t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____460 =
      let uu____461 = FStar_Syntax_Syntax.null_binder t  in [uu____461]  in
    let uu____480 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____460 uu____480 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.fvs -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                let uu____502 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____502 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____503 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____503
                | s ->
                    let uu____505 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____505) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'a . Prims.string -> Prims.int -> Prims.int -> FStar_Range.range -> 'a =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____561 =
            let uu____567 =
              let uu____569 = FStar_Util.string_of_int arity  in
              let uu____571 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____569 uu____571
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____567)  in
          FStar_Errors.raise_error uu____561 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term) FStar_Util.either
      ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          match head1 with
          | FStar_Util.Inr head2 -> mk_Apply_args head2 args
          | FStar_Util.Inl head2 ->
              if n_args = arity
              then FStar_SMTEncoding_Util.mkApp' (head2, args)
              else
                if n_args > arity
                then
                  (let uu____620 = FStar_Util.first_N arity args  in
                   match uu____620 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____644 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____644 arity n_args rng)
  
let (maybe_curry_fvb :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.fvar_binding ->
      FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun fvb  ->
      fun args  ->
        if fvb.FStar_SMTEncoding_Env.fvb_thunked
        then
          let uu____667 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____667 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_676  ->
    match uu___1_676 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____682 -> false
  
let (is_an_eta_expansion :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____730;
                       FStar_SMTEncoding_Term.rng = uu____731;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____762) ->
              let uu____772 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____789 -> false) args (FStar_List.rev xs))
                 in
              if uu____772
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____796,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____800 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____808 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____808))
                 in
              if uu____800
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____815 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____833 'Auu____834 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____833) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____834) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____892  ->
                  match uu____892 with
                  | (x,uu____898) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x))
           in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____906 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____918 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____918) uu____906 tl1
               in
            let uu____921 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____948  ->
                      match uu____948 with
                      | (b,uu____955) ->
                          let uu____956 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____956))
               in
            (match uu____921 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____963) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____977 =
                   let uu____983 =
                     let uu____985 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____985
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____983)  in
                 FStar_Errors.log_issue pos uu____977)
  
type label = (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list ;
  pat_term:
    unit -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list
    }
let (__proj__Mkpattern__item__pat_vars :
  pattern -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> projections
  
let (as_function_typ :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1271 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1286 ->
            let uu____1293 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1293
        | uu____1295 ->
            if norm1
            then let uu____1297 = whnf env t1  in aux false uu____1297
            else
              (let uu____1301 =
                 let uu____1303 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1305 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1303 uu____1305
                  in
               failwith uu____1301)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1347) ->
        let uu____1352 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1352 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1373 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1373)
              | uu____1380 -> (args, res)))
    | uu____1381 ->
        let uu____1382 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1382)
  
let is_arithmetic_primitive :
  'Auu____1396 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1396 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1419::uu____1420::[]) ->
          ((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.op_Addition)
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Subtraction))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Multiply))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.op_Division))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.op_Modulus))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.real_op_LT))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.real_op_LTE))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.real_op_GT))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.real_op_GTE))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.real_op_Addition))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.real_op_Subtraction))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.real_op_Multiply))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.real_op_Division)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1424::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1427 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1458 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1481 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1491 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1491)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1533)::uu____1534::uu____1535::[]) ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1586)::uu____1587::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1624 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____1955 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1955, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1957 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1957, [])
      | FStar_Const.Const_char c1 ->
          let uu____1960 =
            let uu____1961 =
              let uu____1969 =
                let uu____1972 =
                  let uu____1973 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1973  in
                [uu____1972]  in
              ("FStar.Char.__char_of_int", uu____1969)  in
            FStar_SMTEncoding_Util.mkApp uu____1961  in
          (uu____1960, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1991 =
            let uu____1992 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1992  in
          (uu____1991, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2013) ->
          let uu____2016 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2016, [])
      | FStar_Const.Const_range uu____2017 ->
          let uu____2018 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2018, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2021 =
            let uu____2022 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2022  in
          (uu____2021, [])
      | c1 ->
          let uu____2024 =
            let uu____2026 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2026  in
          failwith uu____2024

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term
          Prims.list * FStar_SMTEncoding_Env.env_t *
          FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list))
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2055 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2055
         then
           let uu____2058 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2058
         else ());
        (let uu____2064 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2146  ->
                   fun b  ->
                     match uu____2146 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2211 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2227 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2227 with
                           | (xxsym,xx,env') ->
                               let uu____2252 =
                                 let uu____2257 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2257 env1 xx
                                  in
                               (match uu____2252 with
                                | (guard_x_t,decls') ->
                                    let uu____2272 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2272, guard_x_t, env', decls', x))
                            in
                         (match uu____2211 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2064 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2372 = encode_term t env  in
          match uu____2372 with
          | (t1,decls) ->
              let uu____2383 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2383, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2394 = encode_term t env  in
          match uu____2394 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2409 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2409, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2411 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2411, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2417 = encode_args args_e env  in
        match uu____2417 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2436 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2458 = FStar_List.hd arg_tms1  in unbox uu____2458
               in
            let binary unbox arg_tms1 =
              let uu____2483 =
                let uu____2484 = FStar_List.hd arg_tms1  in unbox uu____2484
                 in
              let uu____2485 =
                let uu____2486 =
                  let uu____2487 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2487  in
                unbox uu____2486  in
              (uu____2483, uu____2485)  in
            let mk_default uu____2495 =
              let uu____2496 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2496 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____2585 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2585
              then
                let uu____2588 =
                  let uu____2589 = mk_args ts  in op uu____2589  in
                FStar_All.pipe_right uu____2588 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____2647 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2647
              then
                let uu____2650 = binary unbox ts  in
                match uu____2650 with
                | (t1,t2) ->
                    let uu____2657 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2657 box
              else
                (let uu____2663 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2663
                 then
                   let uu____2666 =
                     let uu____2667 = binary unbox ts  in op uu____2667  in
                   FStar_All.pipe_right uu____2666 box
                 else mk_default ())
               in
            let add1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkAdd (binary unbox)  in
            let sub1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkSub (binary unbox)  in
            let minus1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkMinus (unary unbox)  in
            let mul1 box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkMul  in
            let div1 box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkDiv  in
            let modulus box unbox =
              mk_nl box unbox "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition,
                 (add1 FStar_SMTEncoding_Term.boxInt
                    FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Subtraction,
                (sub1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Multiply,
                (mul1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_mul"));
              (FStar_Parser_Const.op_Division,
                (div1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_div"));
              (FStar_Parser_Const.op_Modulus,
                (modulus FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Minus,
                (minus1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.real_op_Addition,
                (add1 FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Subtraction,
                (sub1 FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Multiply,
                (mul1 FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal "_rmul"));
              (FStar_Parser_Const.real_op_Division,
                (mk_nl FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal "_rdiv"
                   FStar_SMTEncoding_Util.mkRealDiv));
              (FStar_Parser_Const.real_op_LT,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkLT
                   (binary FStar_SMTEncoding_Term.unboxReal)));
              (FStar_Parser_Const.real_op_LTE,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkLTE
                   (binary FStar_SMTEncoding_Term.unboxReal)));
              (FStar_Parser_Const.real_op_GT,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkGT
                   (binary FStar_SMTEncoding_Term.unboxReal)));
              (FStar_Parser_Const.real_op_GTE,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkGTE
                   (binary FStar_SMTEncoding_Term.unboxReal)))]
               in
            let uu____3102 =
              let uu____3112 =
                FStar_List.tryFind
                  (fun uu____3136  ->
                     match uu____3136 with
                     | (l,uu____3147) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3112 FStar_Util.must  in
            (match uu____3102 with
             | (uu____3191,op) ->
                 let uu____3203 = op arg_tms  in (uu____3203, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_elt
          Prims.list))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____3219 = FStar_List.hd args_e  in
        match uu____3219 with
        | (tm_sz,uu____3235) ->
            let uu____3244 = uu____3219  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____3255 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3281::(sz_arg,uu____3283)::uu____3284::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3351 =
                    let uu____3352 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3352  in
                  let uu____3379 =
                    let uu____3383 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3383  in
                  (uu____3351, uu____3379)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3390::(sz_arg,uu____3392)::uu____3393::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3460 =
                    let uu____3462 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3462
                     in
                  failwith uu____3460
              | uu____3472 ->
                  let uu____3487 = FStar_List.tail args_e  in
                  (uu____3487, FStar_Pervasives_Native.None)
               in
            (match uu____3255 with
             | (arg_tms,ext_sz) ->
                 let uu____3514 = encode_args arg_tms env  in
                 (match uu____3514 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3535 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3547 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3547  in
                      let unary_arith arg_tms2 =
                        let uu____3558 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3558  in
                      let binary arg_tms2 =
                        let uu____3573 =
                          let uu____3574 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3574
                           in
                        let uu____3575 =
                          let uu____3576 =
                            let uu____3577 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3577  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3576
                           in
                        (uu____3573, uu____3575)  in
                      let binary_arith arg_tms2 =
                        let uu____3594 =
                          let uu____3595 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3595
                           in
                        let uu____3596 =
                          let uu____3597 =
                            let uu____3598 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3598  in
                          FStar_SMTEncoding_Term.unboxInt uu____3597  in
                        (uu____3594, uu____3596)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3656 =
                          let uu____3657 = mk_args ts  in op uu____3657  in
                        FStar_All.pipe_right uu____3656 resBox  in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____3789 =
                          let uu____3794 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3794  in
                        let uu____3803 =
                          let uu____3808 =
                            let uu____3810 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3810  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3808  in
                        mk_bv uu____3789 unary uu____3803 arg_tms2  in
                      let to_int1 =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____4050 =
                        let uu____4060 =
                          FStar_List.tryFind
                            (fun uu____4084  ->
                               match uu____4084 with
                               | (l,uu____4095) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4060 FStar_Util.must  in
                      (match uu____4050 with
                       | (uu____4141,op) ->
                           let uu____4153 = op arg_tms1  in
                           (uu____4153, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___539_4163 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___539_4163.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___539_4163.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___539_4163.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___539_4163.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___539_4163.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___539_4163.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___539_4163.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___539_4163.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___539_4163.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___539_4163.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4165 = encode_term t env1  in
      match uu____4165 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          (match tm.FStar_SMTEncoding_Term.tm with
           | FStar_SMTEncoding_Term.App
               (uu____4191,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4192;
                             FStar_SMTEncoding_Term.freevars = uu____4193;
                             FStar_SMTEncoding_Term.rng = uu____4194;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4195;
                  FStar_SMTEncoding_Term.freevars = uu____4196;
                  FStar_SMTEncoding_Term.rng = uu____4197;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4243 ->
               let uu____4244 =
                 encode_formula FStar_Pervasives_Native.None t env1  in
               (match uu____4244 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4265 =
                            let uu____4270 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4270, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4265
                      | uu____4271 ->
                          let uu____4272 =
                            let uu____4283 =
                              let uu____4284 =
                                let uu____4289 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4289, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4284  in
                            ([[valid_tm]], vars, uu____4283)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4272
                       in
                    let ax =
                      let uu____4299 =
                        let uu____4307 =
                          let uu____4309 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4309  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4307)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4299  in
                    let uu____4315 =
                      let uu____4316 =
                        let uu____4319 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4319  in
                      FStar_List.append decls uu____4316  in
                    (tm, uu____4315)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4331 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4331
       then
         let uu____4336 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4338 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4340 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4336 uu____4338
           uu____4340
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4349 ->
           let uu____4372 =
             let uu____4374 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4377 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4379 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4381 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4374
               uu____4377 uu____4379 uu____4381
              in
           failwith uu____4372
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4388 =
             let uu____4390 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4393 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4395 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4397 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4390
               uu____4393 uu____4395 uu____4397
              in
           failwith uu____4388
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4407 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4407
             then
               let uu____4412 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4414 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4412
                 uu____4414
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4420 =
             let uu____4422 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4422
              in
           failwith uu____4420
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4431),uu____4432) ->
           let uu____4481 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4491 -> false  in
           if uu____4481
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4509) ->
           let tv =
             let uu____4515 =
               let uu____4522 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4522
                in
             uu____4515 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4526 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4526
             then
               let uu____4531 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4533 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4531
                 uu____4533
             else ());
            (let t1 =
               let uu____4541 =
                 let uu____4552 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4552]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4541
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4578) ->
           encode_term t1
             (let uu___611_4604 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___611_4604.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___611_4604.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___611_4604.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___611_4604.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___611_4604.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___611_4604.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___611_4604.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___611_4604.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___611_4604.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___611_4604.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4607) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4615 = head_redex env t  in
           if uu____4615
           then let uu____4622 = whnf env t  in encode_term uu____4622 env
           else
             (let fvb =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              let tok =
                FStar_SMTEncoding_Env.lookup_free_var env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
              let uu____4629 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____4653 ->
                      let sym_name =
                        let uu____4664 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4664  in
                      let uu____4667 =
                        let uu____4670 =
                          let uu____4671 =
                            let uu____4679 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4679,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4671  in
                        [uu____4670]  in
                      (uu____4667, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____4686,[]) ->
                      let sym_name =
                        let uu____4691 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4691  in
                      let uu____4694 =
                        let uu____4697 =
                          let uu____4698 =
                            let uu____4706 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4706,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4698  in
                        [uu____4697]  in
                      (uu____4694, sym_name)
                  | uu____4713 -> ([], "")
                else ([], "")  in
              match uu____4629 with
              | (aux_decls,sym_name) ->
                  let uu____4736 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____4736))
       | FStar_Syntax_Syntax.Tm_type uu____4744 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4746) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4776 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4776 with
            | (binders1,res) ->
                let uu____4787 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4787
                then
                  let uu____4794 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4794 with
                   | (vars,guards,env',decls,uu____4819) ->
                       let fsym =
                         let uu____4833 =
                           let uu____4839 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____4839, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4833  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4845 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___665_4854 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___665_4854.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___665_4854.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___665_4854.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___665_4854.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___665_4854.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___665_4854.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___665_4854.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___665_4854.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___665_4854.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___665_4854.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___665_4854.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___665_4854.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___665_4854.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___665_4854.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___665_4854.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___665_4854.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___665_4854.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___665_4854.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___665_4854.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___665_4854.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___665_4854.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___665_4854.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___665_4854.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___665_4854.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___665_4854.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___665_4854.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___665_4854.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___665_4854.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___665_4854.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___665_4854.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___665_4854.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___665_4854.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___665_4854.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___665_4854.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___665_4854.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___665_4854.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___665_4854.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___665_4854.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___665_4854.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___665_4854.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___665_4854.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___665_4854.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4845 with
                        | (pre_opt,res_t) ->
                            let uu____4866 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4866 with
                             | (res_pred,decls') ->
                                 let uu____4877 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4890 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4890, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4894 =
                                         encode_formula
                                           FStar_Pervasives_Native.None pre
                                           env'
                                          in
                                       (match uu____4894 with
                                        | (guard,decls0) ->
                                            let uu____4908 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4908, decls0))
                                    in
                                 (match uu____4877 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4922 =
                                          let uu____4933 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4933)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4922
                                         in
                                      let cvars =
                                        let uu____4953 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4953
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4972 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4974 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4972 <> uu____4974))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let tsym =
                                        let uu____4996 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____4996
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5011 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5011
                                        then
                                          let uu____5014 =
                                            let uu____5016 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5016 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5014
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____5029 =
                                          let uu____5037 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5037)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5029
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5056 =
                                          let uu____5064 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5064,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5056
                                         in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t1
                                         in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t1
                                         in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym  in
                                        let uu____5081 =
                                          let uu____5089 =
                                            let uu____5090 =
                                              let uu____5101 =
                                                let uu____5102 =
                                                  let uu____5107 =
                                                    let uu____5108 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5108
                                                     in
                                                  (f_has_t, uu____5107)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5102
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5101)
                                               in
                                            let uu____5126 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5126 uu____5090  in
                                          (uu____5089,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5081
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5149 =
                                          let uu____5157 =
                                            let uu____5158 =
                                              let uu____5169 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5169)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5158
                                             in
                                          (uu____5157,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5149
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____5192 =
                                        let uu____5193 =
                                          let uu____5196 =
                                            let uu____5199 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5199
                                             in
                                          FStar_List.append decls' uu____5196
                                           in
                                        FStar_List.append decls uu____5193
                                         in
                                      (t1, uu____5192)))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       module_name "Non_total_Tm_arrow"
                      in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.op_Hat "non_total_function_typing_" tsym  in
                     let uu____5220 =
                       let uu____5228 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5228,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5220  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5241 =
                       let uu____5249 =
                         let uu____5250 =
                           let uu____5261 =
                             let uu____5262 =
                               let uu____5267 =
                                 let uu____5268 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5268
                                  in
                               (f_has_t, uu____5267)  in
                             FStar_SMTEncoding_Util.mkImp uu____5262  in
                           ([[f_has_t]], [fsym], uu____5261)  in
                         let uu____5294 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5294 uu____5250  in
                       (uu____5249, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5241  in
                   let uu____5311 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5311)))
       | FStar_Syntax_Syntax.Tm_refine uu____5314 ->
           let uu____5321 =
             let uu____5326 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5326 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5333;
                 FStar_Syntax_Syntax.vars = uu____5334;_} ->
                 let uu____5341 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5341 with
                  | (b,f1) ->
                      let uu____5366 =
                        let uu____5367 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5367  in
                      (uu____5366, f1))
             | uu____5382 -> failwith "impossible"  in
           (match uu____5321 with
            | (x,f) ->
                let uu____5394 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5394 with
                 | (base_t,decls) ->
                     let uu____5405 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5405 with
                      | (x1,xtm,env') ->
                          let uu____5422 =
                            encode_formula FStar_Pervasives_Native.None f
                              env'
                             in
                          (match uu____5422 with
                           | (refinement,decls') ->
                               let uu____5434 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5434 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____5462 =
                                        let uu____5473 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5484 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5473
                                          uu____5484
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5462
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5538 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5538 <> x1) &&
                                                (let uu____5542 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5542 <> fsym)))
                                       in
                                    let xfv =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (x1,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (fsym,
                                          FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Term.mkForall
                                        t0.FStar_Syntax_Syntax.pos
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let module_name =
                                      env.FStar_SMTEncoding_Env.current_module_name
                                       in
                                    let tsym =
                                      let uu____5578 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____5578
                                       in
                                    let cvar_sorts =
                                      FStar_List.map
                                        FStar_SMTEncoding_Term.fv_sort cvars1
                                       in
                                    let tdecl =
                                      FStar_SMTEncoding_Term.DeclFun
                                        (tsym, cvar_sorts,
                                          FStar_SMTEncoding_Term.Term_sort,
                                          FStar_Pervasives_Native.None)
                                       in
                                    let t1 =
                                      let uu____5598 =
                                        let uu____5606 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____5606)  in
                                      FStar_SMTEncoding_Util.mkApp uu____5598
                                       in
                                    let x_has_base_t =
                                      FStar_SMTEncoding_Term.mk_HasType xtm
                                        base_t
                                       in
                                    let x_has_t =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm t1
                                       in
                                    let t_has_kind =
                                      FStar_SMTEncoding_Term.mk_HasType t1
                                        FStar_SMTEncoding_Term.mk_Term_type
                                       in
                                    let t_haseq_base =
                                      FStar_SMTEncoding_Term.mk_haseq base_t
                                       in
                                    let t_haseq_ref =
                                      FStar_SMTEncoding_Term.mk_haseq t1  in
                                    let t_haseq1 =
                                      let uu____5626 =
                                        let uu____5634 =
                                          let uu____5635 =
                                            let uu____5646 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____5646)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5635
                                           in
                                        (uu____5634,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5626
                                       in
                                    let t_kinding =
                                      let uu____5660 =
                                        let uu____5668 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____5668,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5660
                                       in
                                    let t_interp =
                                      let uu____5682 =
                                        let uu____5690 =
                                          let uu____5691 =
                                            let uu____5702 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____5702)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5691
                                           in
                                        (uu____5690,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5682
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____5734 =
                                      let uu____5735 =
                                        let uu____5738 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____5738
                                         in
                                      FStar_List.append decls uu____5735  in
                                    (t1, uu____5734))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5742) ->
           let ttm =
             let uu____5760 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5760  in
           let uu____5762 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5762 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5774 =
                    let uu____5782 =
                      let uu____5784 =
                        let uu____5786 =
                          let uu____5788 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5788  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5786  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5784
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5782)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5774  in
                let uu____5794 =
                  let uu____5795 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5795  in
                (ttm, uu____5794))
       | FStar_Syntax_Syntax.Tm_app uu____5802 ->
           let uu____5819 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5819 with
            | (head1,args_e) ->
                let uu____5866 =
                  let uu____5881 =
                    let uu____5882 = FStar_Syntax_Subst.compress head1  in
                    uu____5882.FStar_Syntax_Syntax.n  in
                  (uu____5881, args_e)  in
                (match uu____5866 with
                 | uu____5899 when head_redex env head1 ->
                     let uu____5914 = whnf env t  in
                     encode_term uu____5914 env
                 | uu____5915 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5938 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5956) when
                     (Prims.op_Negation
                        env.FStar_SMTEncoding_Env.encoding_quantifier)
                       &&
                       ((FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.forall_lid)
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.exists_lid))
                     -> encode_deeply_embedded_quantifier t0 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____5978;
                       FStar_Syntax_Syntax.vars = uu____5979;_},uu____5980),uu____5981)
                     when
                     (Prims.op_Negation
                        env.FStar_SMTEncoding_Env.encoding_quantifier)
                       &&
                       ((FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.forall_lid)
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.exists_lid))
                     -> encode_deeply_embedded_quantifier t0 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6007;
                       FStar_Syntax_Syntax.vars = uu____6008;_},uu____6009),
                    (v0,uu____6011)::(v1,uu____6013)::(v2,uu____6015)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6086 = encode_term v0 env  in
                     (match uu____6086 with
                      | (v01,decls0) ->
                          let uu____6097 = encode_term v1 env  in
                          (match uu____6097 with
                           | (v11,decls1) ->
                               let uu____6108 = encode_term v2 env  in
                               (match uu____6108 with
                                | (v21,decls2) ->
                                    let uu____6119 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6119,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____6122)::(v1,uu____6124)::(v2,uu____6126)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6193 = encode_term v0 env  in
                     (match uu____6193 with
                      | (v01,decls0) ->
                          let uu____6204 = encode_term v1 env  in
                          (match uu____6204 with
                           | (v11,decls1) ->
                               let uu____6215 = encode_term v2 env  in
                               (match uu____6215 with
                                | (v21,decls2) ->
                                    let uu____6226 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6226,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6228)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6264)::(rng,uu____6266)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6317) ->
                     let e0 =
                       let uu____6339 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6339
                        in
                     ((let uu____6349 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6349
                       then
                         let uu____6354 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6354
                       else ());
                      (let e =
                         let uu____6362 =
                           let uu____6367 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6368 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6367
                             uu____6368
                            in
                         uu____6362 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6377),(arg,uu____6379)::[]) -> encode_term arg env
                 | uu____6414 ->
                     let uu____6429 = encode_args args_e env  in
                     (match uu____6429 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6490 = encode_term head1 env  in
                            match uu____6490 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6562 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6562 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6660  ->
                                                 fun uu____6661  ->
                                                   match (uu____6660,
                                                           uu____6661)
                                                   with
                                                   | ((bv,uu____6691),
                                                      (a,uu____6693)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6723 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6723
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6724 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6724 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let tkey_hash =
                                                 FStar_SMTEncoding_Term.hash_of_term
                                                   app_tm
                                                  in
                                               let e_typing =
                                                 let uu____6741 =
                                                   let uu____6749 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6758 =
                                                     let uu____6760 =
                                                       let uu____6762 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____6762
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____6760
                                                      in
                                                   (uu____6749,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6758)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6741
                                                  in
                                               let uu____6768 =
                                                 let uu____6771 =
                                                   let uu____6774 =
                                                     let uu____6777 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____6777
                                                      in
                                                   FStar_List.append decls'
                                                     uu____6774
                                                    in
                                                 FStar_List.append decls
                                                   uu____6771
                                                  in
                                               (app_tm, uu____6768))))
                             in
                          let encode_full_app fv =
                            let uu____6797 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6797 with
                            | (fname,fuel_args,arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args)
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____6840;
                                   FStar_Syntax_Syntax.vars = uu____6841;_},uu____6842)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____6849;
                                   FStar_Syntax_Syntax.vars = uu____6850;_},uu____6851)
                                ->
                                let uu____6856 =
                                  let uu____6857 =
                                    let uu____6862 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6862
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6857
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6856
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6892 =
                                  let uu____6893 =
                                    let uu____6898 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6898
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6893
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6892
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6927,(FStar_Util.Inl t1,uu____6929),uu____6930)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6977,(FStar_Util.Inr c,uu____6979),uu____6980)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7027 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7048 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7048
                                  in
                               let uu____7049 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7049 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7065;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7066;_},uu____7067)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____7085 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____7164 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7164 with
            | (bs1,body1,opening) ->
                let fallback uu____7187 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      env.FStar_SMTEncoding_Env.current_module_name "Tm_abs"
                     in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7197 =
                    let uu____7198 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____7198
                     in
                  let uu____7200 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____7197, uu____7200)  in
                let is_impure rc =
                  let uu____7210 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7210 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7225 =
                          let uu____7238 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____7238
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____7225 with
                         | (t1,uu____7241,uu____7242) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7260 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7260
                  then
                    let uu____7265 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7265
                  else
                    (let uu____7268 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7268
                     then
                       let uu____7273 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7273
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7281 =
                         let uu____7287 =
                           let uu____7289 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7289
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7287)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7281);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7294 =
                       (is_impure rc) &&
                         (let uu____7297 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7297)
                        in
                     if uu____7294
                     then fallback ()
                     else
                       (let uu____7306 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7306 with
                        | (vars,guards,envbody,decls,uu____7331) ->
                            let body2 =
                              let uu____7345 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7345
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7350 = encode_term body2 envbody  in
                            (match uu____7350 with
                             | (body3,decls') ->
                                 let uu____7361 =
                                   let uu____7370 = codomain_eff rc  in
                                   match uu____7370 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7389 = encode_term tfun env
                                          in
                                       (match uu____7389 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7361 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7423 =
                                          let uu____7434 =
                                            let uu____7435 =
                                              let uu____7440 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7440, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7435
                                             in
                                          ([], vars, uu____7434)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7423
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7448 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7464 =
                                              let uu____7467 =
                                                let uu____7478 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7478
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7467
                                               in
                                            let uu____7505 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7464, uu____7505)
                                         in
                                      (match uu____7448 with
                                       | (cvars1,key_body1) ->
                                           let tkey =
                                             FStar_SMTEncoding_Term.mkForall
                                               t0.FStar_Syntax_Syntax.pos
                                               ([], cvars1, key_body1)
                                              in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey
                                              in
                                           let uu____7527 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7527 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Term.fv_sort
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let uu____7543 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____7543
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____7552 =
                                                    let uu____7560 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7560)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7552
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.op_Hat
                                                          "typing_" fsym
                                                         in
                                                      let uu____7577 =
                                                        let uu____7578 =
                                                          let uu____7586 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7586,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7578
                                                         in
                                                      [uu____7577]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____7601 =
                                                    let uu____7609 =
                                                      let uu____7610 =
                                                        let uu____7621 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____7621)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____7610
                                                       in
                                                    (uu____7609,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____7601
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____7635 =
                                                  let uu____7636 =
                                                    let uu____7639 =
                                                      let uu____7642 =
                                                        FStar_SMTEncoding_Term.mk_decls
                                                          fsym tkey_hash
                                                          f_decls
                                                          (FStar_List.append
                                                             decls
                                                             (FStar_List.append
                                                                decls'
                                                                decls''))
                                                         in
                                                      FStar_List.append
                                                        decls'' uu____7642
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7639
                                                     in
                                                  FStar_List.append decls
                                                    uu____7636
                                                   in
                                                (f, uu____7635))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7645,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7646;
                          FStar_Syntax_Syntax.lbunivs = uu____7647;
                          FStar_Syntax_Syntax.lbtyp = uu____7648;
                          FStar_Syntax_Syntax.lbeff = uu____7649;
                          FStar_Syntax_Syntax.lbdef = uu____7650;
                          FStar_Syntax_Syntax.lbattrs = uu____7651;
                          FStar_Syntax_Syntax.lbpos = uu____7652;_}::uu____7653),uu____7654)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7688;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7690;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7692;
                FStar_Syntax_Syntax.lbpos = uu____7693;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7720 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise FStar_SMTEncoding_Env.Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and (encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_SMTEncoding_Env.env_t ->
            (FStar_Syntax_Syntax.term ->
               FStar_SMTEncoding_Env.env_t ->
                 (FStar_SMTEncoding_Term.term *
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____7792 =
                let uu____7797 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7797 env  in
              match uu____7792 with
              | (ee1,decls1) ->
                  let uu____7822 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7822 with
                   | (xs,e21) ->
                       let uu____7847 = FStar_List.hd xs  in
                       (match uu____7847 with
                        | (x1,uu____7865) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7871 = encode_body e21 env'  in
                            (match uu____7871 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Env.env_t ->
          (FStar_Syntax_Syntax.term ->
             FStar_SMTEncoding_Env.env_t ->
               (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____7901 =
              let uu____7909 =
                let uu____7910 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7910  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7909  in
            match uu____7901 with
            | (scrsym,scr',env1) ->
                let uu____7920 = encode_term e env1  in
                (match uu____7920 with
                 | (scr,decls) ->
                     let uu____7931 =
                       let encode_branch b uu____7960 =
                         match uu____7960 with
                         | (else_case,decls1) ->
                             let uu____7979 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7979 with
                              | (p,w,br) ->
                                  let uu____8005 = encode_pat env1 p  in
                                  (match uu____8005 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8042  ->
                                                   match uu____8042 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____8049 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8071 =
                                               encode_term w1 env2  in
                                             (match uu____8071 with
                                              | (w2,decls2) ->
                                                  let uu____8084 =
                                                    let uu____8085 =
                                                      let uu____8090 =
                                                        let uu____8091 =
                                                          let uu____8096 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8096)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8091
                                                         in
                                                      (guard, uu____8090)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8085
                                                     in
                                                  (uu____8084, decls2))
                                          in
                                       (match uu____8049 with
                                        | (guard1,decls2) ->
                                            let uu____8111 =
                                              encode_br br env2  in
                                            (match uu____8111 with
                                             | (br1,decls3) ->
                                                 let uu____8124 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8124,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7931 with
                      | (match_tm,decls1) ->
                          let uu____8145 =
                            let uu____8146 =
                              let uu____8157 =
                                let uu____8164 =
                                  let uu____8169 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____8169, scr)  in
                                [uu____8164]  in
                              (uu____8157, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____8146
                              FStar_Range.dummyRange
                             in
                          (uu____8145, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____8192 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____8192
       then
         let uu____8195 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8195
       else ());
      (let uu____8200 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8200 with
       | (vars,pat_term) ->
           let uu____8217 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8259  ->
                     fun v1  ->
                       match uu____8259 with
                       | (env1,vars1) ->
                           let uu____8295 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8295 with
                            | (xx,uu____8314,env2) ->
                                let uu____8318 =
                                  let uu____8325 =
                                    let uu____8330 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____8330)  in
                                  uu____8325 :: vars1  in
                                (env2, uu____8318))) (env, []))
              in
           (match uu____8217 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8385 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8386 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8387 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8395 = encode_const c env1  in
                      (match uu____8395 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8403::uu____8404 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8408 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8431 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8431 with
                        | (uu____8439,uu____8440::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8445 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8481  ->
                                  match uu____8481 with
                                  | (arg,uu____8491) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8500 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8500))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8532) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8563 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8588 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8634  ->
                                  match uu____8634 with
                                  | (arg,uu____8650) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8659 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8659))
                         in
                      FStar_All.pipe_right uu____8588 FStar_List.flatten
                   in
                let pat_term1 uu____8690 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun l  ->
    fun env  ->
      let uu____8700 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8748  ->
                fun uu____8749  ->
                  match (uu____8748, uu____8749) with
                  | ((tms,decls),(t,uu____8789)) ->
                      let uu____8816 = encode_term t env  in
                      (match uu____8816 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8700 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____8894  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1240_8903 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1240_8903.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1240_8903.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1240_8903.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1240_8903.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1240_8903.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1240_8903.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1240_8903.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1240_8903.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1240_8903.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1240_8903.FStar_SMTEncoding_Env.global_cache)
        }  in
      encode_formula FStar_Pervasives_Native.None quant env1

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1245_8921 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1245_8921.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1245_8921.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1245_8921.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1245_8921.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1245_8921.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1245_8921.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1245_8921.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1245_8921.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1245_8921.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1245_8921.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____8937 = FStar_Syntax_Util.head_and_args t  in
        match uu____8937 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9000::(x,uu____9002)::(t1,uu____9004)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9071 = encode_term x env1  in
                 (match uu____9071 with
                  | (x1,decls) ->
                      let uu____9082 = encode_term t1 env1  in
                      (match uu____9082 with
                       | (t2,decls') ->
                           let uu____9093 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9093, (FStar_List.append decls decls'))))
             | uu____9094 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9137  ->
             match uu____9137 with
             | (pats_l1,decls) ->
                 let uu____9182 =
                   FStar_List.fold_right
                     (fun uu____9217  ->
                        fun uu____9218  ->
                          match (uu____9217, uu____9218) with
                          | ((p,uu____9260),(pats1,decls1)) ->
                              let uu____9295 = encode_smt_pattern p  in
                              (match uu____9295 with
                               | (t,d) ->
                                   let uu____9310 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9310 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9327 =
                                            let uu____9333 =
                                              let uu____9335 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9337 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9335 uu____9337
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____9333)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9327);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9182 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun prev_msg  ->
    fun phi  ->
      fun env  ->
        let debug1 phi1 =
          let uu____9401 =
            FStar_All.pipe_left
              (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
              (FStar_Options.Other "SMTEncoding")
             in
          if uu____9401
          then
            let uu____9406 = FStar_Syntax_Print.tag_of_term phi1  in
            let uu____9408 = FStar_Syntax_Print.term_to_string phi1  in
            FStar_Util.print2 "Formula (%s)  %s\n" uu____9406 uu____9408
          else ()  in
        let enc f r l =
          let uu____9450 =
            FStar_Util.fold_map
              (fun decls  ->
                 fun x  ->
                   let uu____9482 =
                     encode_term (FStar_Pervasives_Native.fst x) env  in
                   match uu____9482 with
                   | (t,decls') -> ((FStar_List.append decls decls'), t)) []
              l
             in
          match uu____9450 with
          | (decls,args) ->
              let uu____9513 =
                let uu___1310_9514 = f args  in
                {
                  FStar_SMTEncoding_Term.tm =
                    (uu___1310_9514.FStar_SMTEncoding_Term.tm);
                  FStar_SMTEncoding_Term.freevars =
                    (uu___1310_9514.FStar_SMTEncoding_Term.freevars);
                  FStar_SMTEncoding_Term.rng = r
                }  in
              (uu____9513, decls)
           in
        let const_op f msg r uu____9557 =
          let uu____9573 = f r  in (uu____9573, [])  in
        let un_op f l =
          let uu____9596 = FStar_List.hd l  in
          FStar_All.pipe_left f uu____9596  in
        let bin_op f uu___2_9616 =
          match uu___2_9616 with
          | t1::t2::[] -> f (t1, t2)
          | uu____9627 -> failwith "Impossible"  in
        let enc_prop_c f msg r l =
          let uu____9684 =
            FStar_Util.fold_map
              (fun decls  ->
                 fun uu____9709  ->
                   match uu____9709 with
                   | (t,uu____9725) ->
                       let uu____9730 = encode_formula msg t env  in
                       (match uu____9730 with
                        | (phi1,decls') ->
                            ((FStar_List.append decls decls'), phi1))) [] l
             in
          match uu____9684 with
          | (decls,phis) ->
              let uu____9759 =
                let uu___1342_9760 = f phis  in
                {
                  FStar_SMTEncoding_Term.tm =
                    (uu___1342_9760.FStar_SMTEncoding_Term.tm);
                  FStar_SMTEncoding_Term.freevars =
                    (uu___1342_9760.FStar_SMTEncoding_Term.freevars);
                  FStar_SMTEncoding_Term.rng = r
                }  in
              (uu____9759, decls)
           in
        let eq_op msg r args =
          let rf =
            FStar_List.filter
              (fun uu____9834  ->
                 match uu____9834 with
                 | (a,q) ->
                     (match q with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____9855) -> false
                      | uu____9858 -> true)) args
             in
          if (FStar_List.length rf) <> (Prims.parse_int "2")
          then
            let uu____9877 =
              FStar_Util.format1
                "eq_op: got %s non-implicit arguments instead of 2?"
                (Prims.string_of_int (FStar_List.length rf))
               in
            failwith uu____9877
          else
            (let uu____9894 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
             uu____9894 r rf)
           in
        let eq3_op msg r args =
          let n1 = FStar_List.length args  in
          if n1 = (Prims.parse_int "4")
          then
            let uu____9973 =
              enc
                (fun terms  ->
                   match terms with
                   | t0::t1::v0::v1::[] ->
                       let uu____10005 =
                         let uu____10010 =
                           FStar_SMTEncoding_Util.mkEq (t0, t1)  in
                         let uu____10011 =
                           FStar_SMTEncoding_Util.mkEq (v0, v1)  in
                         (uu____10010, uu____10011)  in
                       FStar_SMTEncoding_Util.mkAnd uu____10005
                   | uu____10012 -> failwith "Impossible")
               in
            uu____9973 r args
          else
            (let uu____10018 =
               FStar_Util.format1
                 "eq3_op: got %s non-implicit arguments instead of 4?"
                 (Prims.string_of_int n1)
                in
             failwith uu____10018)
           in
        let h_equals_op msg r args =
          let n1 = FStar_List.length args  in
          if n1 = (Prims.parse_int "4")
          then
            let uu____10091 =
              enc
                (fun terms  ->
                   match terms with
                   | t0::v0::t1::v1::[] ->
                       let uu____10123 =
                         let uu____10128 =
                           FStar_SMTEncoding_Util.mkEq (t0, t1)  in
                         let uu____10129 =
                           FStar_SMTEncoding_Util.mkEq (v0, v1)  in
                         (uu____10128, uu____10129)  in
                       FStar_SMTEncoding_Util.mkAnd uu____10123
                   | uu____10130 -> failwith "Impossible")
               in
            uu____10091 r args
          else
            (let uu____10136 =
               FStar_Util.format1
                 "eq3_op: got %s non-implicit arguments instead of 4?"
                 (Prims.string_of_int n1)
                in
             failwith uu____10136)
           in
        let mk_imp1 msg r uu___3_10176 =
          match uu___3_10176 with
          | (lhs,uu____10182)::(rhs,uu____10184)::[] ->
              let uu____10225 = encode_formula msg rhs env  in
              (match uu____10225 with
               | (l1,decls1) ->
                   (match l1.FStar_SMTEncoding_Term.tm with
                    | FStar_SMTEncoding_Term.App
                        (FStar_SMTEncoding_Term.TrueOp ,uu____10240) ->
                        (l1, decls1)
                    | uu____10245 ->
                        let uu____10246 = encode_formula msg lhs env  in
                        (match uu____10246 with
                         | (l2,decls2) ->
                             let uu____10257 =
                               FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                             (uu____10257, (FStar_List.append decls1 decls2)))))
          | uu____10258 -> failwith "impossible"  in
        let mk_ite msg r uu___4_10297 =
          match uu___4_10297 with
          | (guard,uu____10303)::(_then,uu____10305)::(_else,uu____10307)::[]
              ->
              let uu____10364 = encode_formula msg guard env  in
              (match uu____10364 with
               | (g,decls1) ->
                   let uu____10375 = encode_formula msg _then env  in
                   (match uu____10375 with
                    | (t,decls2) ->
                        let uu____10386 = encode_formula msg _else env  in
                        (match uu____10386 with
                         | (e,decls3) ->
                             let res =
                               FStar_SMTEncoding_Term.mkITE (g, t, e) r  in
                             (res,
                               (FStar_List.append decls1
                                  (FStar_List.append decls2 decls3))))))
          | uu____10398 -> failwith "impossible"  in
        let unboxInt_l f l =
          let uu____10428 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
             in
          f uu____10428  in
        let connectives =
          let uu____10464 =
            let uu____10495 =
              enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)  in
            (FStar_Parser_Const.and_lid, uu____10495)  in
          let uu____10551 =
            let uu____10584 =
              let uu____10615 =
                enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)  in
              (FStar_Parser_Const.or_lid, uu____10615)  in
            let uu____10671 =
              let uu____10704 =
                let uu____10737 =
                  let uu____10768 =
                    enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                  (FStar_Parser_Const.iff_lid, uu____10768)  in
                let uu____10824 =
                  let uu____10857 =
                    let uu____10890 =
                      let uu____10921 =
                        enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                      (FStar_Parser_Const.not_lid, uu____10921)  in
                    [uu____10890;
                    (FStar_Parser_Const.eq2_lid, eq_op);
                    (FStar_Parser_Const.c_eq2_lid, eq_op);
                    (FStar_Parser_Const.eq3_lid, eq3_op);
                    (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                    (FStar_Parser_Const.true_lid,
                      (const_op FStar_SMTEncoding_Term.mkTrue));
                    (FStar_Parser_Const.false_lid,
                      (const_op FStar_SMTEncoding_Term.mkFalse))]
                     in
                  (FStar_Parser_Const.ite_lid, mk_ite) :: uu____10857  in
                uu____10737 :: uu____10824  in
              (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____10704  in
            uu____10584 :: uu____10671  in
          uu____10464 :: uu____10551  in
        let rec fallback phi1 =
          match phi1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_meta
              (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
              let s =
                if msg = "could not prove post-condition"
                then FStar_Pervasives_Native.None
                else
                  (let uu____11618 =
                     let uu____11620 = FStar_Range.string_of_range r  in
                     FStar_Util.format2 "(%s) %s" uu____11620 msg  in
                   FStar_Pervasives_Native.Some uu____11618)
                 in
              let uu____11624 = encode_formula s phi' env  in
              (match uu____11624 with
               | (phi2,decls) ->
                   let uu____11635 =
                     FStar_SMTEncoding_Term.mk
                       (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                      in
                   (uu____11635, decls))
          | FStar_Syntax_Syntax.Tm_meta uu____11637 ->
              let uu____11644 = FStar_Syntax_Util.unmeta phi1  in
              encode_formula prev_msg uu____11644 env
          | FStar_Syntax_Syntax.Tm_match (e,pats) ->
              let uu____11683 =
                encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                  (encode_formula prev_msg)
                 in
              (match uu____11683 with | (t,decls) -> (t, decls))
          | FStar_Syntax_Syntax.Tm_let
              ((false
                ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                   FStar_Syntax_Syntax.lbunivs = uu____11695;
                   FStar_Syntax_Syntax.lbtyp = t1;
                   FStar_Syntax_Syntax.lbeff = uu____11697;
                   FStar_Syntax_Syntax.lbdef = e1;
                   FStar_Syntax_Syntax.lbattrs = uu____11699;
                   FStar_Syntax_Syntax.lbpos = uu____11700;_}::[]),e2)
              ->
              let uu____11727 =
                encode_let x t1 e1 e2 env (encode_formula prev_msg)  in
              (match uu____11727 with | (t,decls) -> (t, decls))
          | FStar_Syntax_Syntax.Tm_app (head1,args) ->
              let head2 = FStar_Syntax_Util.un_uinst head1  in
              (match ((head2.FStar_Syntax_Syntax.n), args) with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____11780::(x,uu____11782)::(t,uu____11784)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.has_type_lid
                   ->
                   let uu____11851 = encode_term x env  in
                   (match uu____11851 with
                    | (x1,decls) ->
                        let uu____11862 = encode_term t env  in
                        (match uu____11862 with
                         | (t1,decls') ->
                             let uu____11873 =
                               FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                             (uu____11873, (FStar_List.append decls decls'))))
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,(r,uu____11876)::(msg,uu____11878)::(phi2,uu____11880)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.labeled_lid
                   ->
                   let uu____11947 =
                     let uu____11952 =
                       let uu____11953 = FStar_Syntax_Subst.compress r  in
                       uu____11953.FStar_Syntax_Syntax.n  in
                     let uu____11956 =
                       let uu____11957 = FStar_Syntax_Subst.compress msg  in
                       uu____11957.FStar_Syntax_Syntax.n  in
                     (uu____11952, uu____11956)  in
                   (match uu____11947 with
                    | (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range
                       r1),FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string (s,uu____11966))) ->
                        let s1 =
                          match prev_msg with
                          | FStar_Pervasives_Native.Some msg1 ->
                              Prims.op_Hat msg1 (Prims.op_Hat ": " s)
                          | FStar_Pervasives_Native.None  -> s  in
                        let phi3 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_meta
                               (phi2,
                                 (FStar_Syntax_Syntax.Meta_labeled
                                    (s1, r1, false))))
                            FStar_Pervasives_Native.None r1
                           in
                        fallback phi3
                    | uu____11985 -> fallback phi2)
               | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11992)::[]) when
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.squash_lid)
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.auto_squash_lid)
                   -> encode_formula prev_msg t env
               | uu____12027 when head_redex env head2 ->
                   let uu____12042 = whnf env phi1  in
                   encode_formula prev_msg uu____12042 env
               | uu____12043 ->
                   let uu____12058 = encode_term phi1 env  in
                   (match uu____12058 with
                    | (tt,decls) ->
                        let tt1 =
                          let uu____12070 =
                            let uu____12072 =
                              FStar_Range.use_range
                                tt.FStar_SMTEncoding_Term.rng
                               in
                            let uu____12073 =
                              FStar_Range.use_range
                                phi1.FStar_Syntax_Syntax.pos
                               in
                            FStar_Range.rng_included uu____12072 uu____12073
                             in
                          if uu____12070
                          then tt
                          else
                            (let uu___1540_12077 = tt  in
                             {
                               FStar_SMTEncoding_Term.tm =
                                 (uu___1540_12077.FStar_SMTEncoding_Term.tm);
                               FStar_SMTEncoding_Term.freevars =
                                 (uu___1540_12077.FStar_SMTEncoding_Term.freevars);
                               FStar_SMTEncoding_Term.rng =
                                 (phi1.FStar_Syntax_Syntax.pos)
                             })
                           in
                        let uu____12078 = FStar_SMTEncoding_Term.mk_Valid tt1
                           in
                        (uu____12078, decls)))
          | uu____12079 ->
              let uu____12080 = encode_term phi1 env  in
              (match uu____12080 with
               | (tt,decls) ->
                   let tt1 =
                     let uu____12092 =
                       let uu____12094 =
                         FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                          in
                       let uu____12095 =
                         FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos
                          in
                       FStar_Range.rng_included uu____12094 uu____12095  in
                     if uu____12092
                     then tt
                     else
                       (let uu___1548_12099 = tt  in
                        {
                          FStar_SMTEncoding_Term.tm =
                            (uu___1548_12099.FStar_SMTEncoding_Term.tm);
                          FStar_SMTEncoding_Term.freevars =
                            (uu___1548_12099.FStar_SMTEncoding_Term.freevars);
                          FStar_SMTEncoding_Term.rng =
                            (phi1.FStar_Syntax_Syntax.pos)
                        })
                      in
                   let uu____12100 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                   (uu____12100, decls))
           in
        let encode_q_body env1 bs ps body =
          let uu____12144 =
            encode_binders FStar_Pervasives_Native.None bs env1  in
          match uu____12144 with
          | (vars,guards,env2,decls,uu____12183) ->
              let uu____12196 = encode_smt_patterns ps env2  in
              (match uu____12196 with
               | (pats,decls') ->
                   let uu____12233 =
                     encode_formula FStar_Pervasives_Native.None body env2
                      in
                   (match uu____12233 with
                    | (body1,decls'') ->
                        let guards1 =
                          match pats with
                          | ({
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Var gf,p::[]);
                               FStar_SMTEncoding_Term.freevars = uu____12266;
                               FStar_SMTEncoding_Term.rng = uu____12267;_}::[])::[]
                              when
                              let uu____12287 =
                                FStar_Ident.text_of_lid
                                  FStar_Parser_Const.guard_free
                                 in
                              uu____12287 = gf -> []
                          | uu____12290 -> guards  in
                        let uu____12295 =
                          FStar_SMTEncoding_Util.mk_and_l guards1  in
                        (vars, pats, uu____12295, body1,
                          (FStar_List.append decls
                             (FStar_List.append decls' decls'')))))
           in
        debug1 phi;
        (let phi1 = FStar_Syntax_Util.unascribe phi  in
         let uu____12306 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
         match uu____12306 with
         | FStar_Pervasives_Native.None  -> fallback phi1
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
             (op,arms)) ->
             let uu____12315 =
               FStar_All.pipe_right connectives
                 (FStar_List.tryFind
                    (fun uu____12445  ->
                       match uu____12445 with
                       | (l,uu____12475) -> FStar_Ident.lid_equals op l))
                in
             (match uu____12315 with
              | FStar_Pervasives_Native.None  -> fallback phi1
              | FStar_Pervasives_Native.Some (uu____12562,f) ->
                  f prev_msg phi1.FStar_Syntax_Syntax.pos arms)
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
             (vars,pats,body)) ->
             (FStar_All.pipe_right pats
                (FStar_List.iter (check_pattern_vars env vars));
              (let uu____12672 = encode_q_body env vars pats body  in
               match uu____12672 with
               | (vars1,pats1,guard,body1,decls) ->
                   let tm =
                     let uu____12717 =
                       let uu____12728 =
                         FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                       (pats1, vars1, uu____12728)  in
                     FStar_SMTEncoding_Term.mkForall
                       phi1.FStar_Syntax_Syntax.pos uu____12717
                      in
                   (tm, decls)))
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
             (vars,pats,body)) ->
             (FStar_All.pipe_right pats
                (FStar_List.iter (check_pattern_vars env vars));
              (let uu____12759 = encode_q_body env vars pats body  in
               match uu____12759 with
               | (vars1,pats1,guard,body1,decls) ->
                   let uu____12803 =
                     let uu____12804 =
                       let uu____12815 =
                         FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                       (pats1, vars1, uu____12815)  in
                     FStar_SMTEncoding_Term.mkExists
                       phi1.FStar_Syntax_Syntax.pos uu____12804
                      in
                   (uu____12803, decls))))
