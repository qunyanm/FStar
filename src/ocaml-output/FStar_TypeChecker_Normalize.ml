open Prims
let cases :
  'Auu____10 'Auu____11 .
    ('Auu____10 -> 'Auu____11) ->
      'Auu____11 -> 'Auu____10 FStar_Pervasives_Native.option -> 'Auu____11
  =
  fun f  ->
    fun d  ->
      fun uu___0_31  ->
        match uu___0_31 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
type closure =
  | Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure) Prims.list * FStar_Syntax_Syntax.term *
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____129 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____241 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____259 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)) =
  (FStar_Pervasives_Native.None, Dummy) 
type branches =
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list
type stack_elt =
  | Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  
  | MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo 
  | Match of (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range)
  
  | Abs of (env * FStar_Syntax_Syntax.binders * env *
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStar_Range.range) 
  | App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Cfg of FStar_TypeChecker_Cfg.cfg 
  | Debug of (FStar_Syntax_Syntax.term * FStar_Util.time) 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____428 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____471 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____514 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____559 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____614 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____677 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____726 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____771 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____814 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____837 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____866 = FStar_Syntax_Util.head_and_args' t  in
    match uu____866 with | (hd1,uu____882) -> hd1
  
let mk :
  'Auu____910 .
    'Auu____910 ->
      FStar_Range.range -> 'Auu____910 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____953 = FStar_ST.op_Bang r  in
          match uu____953 with
          | FStar_Pervasives_Native.Some uu____979 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1034 =
      FStar_List.map
        (fun uu____1050  ->
           match uu____1050 with
           | (bopt,c) ->
               let uu____1064 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1069 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1064 uu____1069) env
       in
    FStar_All.pipe_right uu____1034 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___1_1077  ->
    match uu___1_1077 with
    | Clos (env,t,uu____1081,uu____1082) ->
        let uu____1129 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1139 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1129 uu____1139
    | Univ uu____1142 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1151  ->
    match uu___2_1151 with
    | Arg (c,uu____1154,uu____1155) ->
        let uu____1156 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1156
    | MemoLazy uu____1159 -> "MemoLazy"
    | Abs (uu____1167,bs,uu____1169,uu____1170,uu____1171) ->
        let uu____1176 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1176
    | UnivArgs uu____1187 -> "UnivArgs"
    | Match uu____1195 -> "Match"
    | App (uu____1205,t,uu____1207,uu____1208) ->
        let uu____1209 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1209
    | Meta (uu____1212,m,uu____1214) -> "Meta"
    | Let uu____1216 -> "Let"
    | Cfg uu____1226 -> "Cfg"
    | Debug (t,uu____1229) ->
        let uu____1230 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1230
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1244 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1244 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1259 . 'Auu____1259 Prims.list -> Prims.bool =
  fun uu___3_1267  ->
    match uu___3_1267 with | [] -> true | uu____1271 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___115_1304  ->
           match () with
           | () ->
               let uu____1305 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1305) ()
      with
      | uu___114_1322 ->
          let uu____1323 =
            let uu____1325 = FStar_Syntax_Print.db_to_string x  in
            let uu____1327 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1325
              uu____1327
             in
          failwith uu____1323
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1338 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1338
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1345 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1345
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1352 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1352
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____1390 =
            FStar_List.fold_left
              (fun uu____1416  ->
                 fun u1  ->
                   match uu____1416 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1441 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1441 with
                        | (k_u,n1) ->
                            let uu____1459 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1459
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1390 with
          | (uu____1480,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___149_1506  ->
                    match () with
                    | () ->
                        let uu____1509 =
                          let uu____1510 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1510  in
                        (match uu____1509 with
                         | Univ u3 ->
                             ((let uu____1529 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1529
                               then
                                 let uu____1534 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1534
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1539 ->
                             let uu____1540 =
                               let uu____1542 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1542
                                in
                             failwith uu____1540)) ()
               with
               | uu____1552 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1558 =
                        let uu____1560 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1560
                         in
                      failwith uu____1558))
          | FStar_Syntax_Syntax.U_unif uu____1565 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1574 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1583 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1590 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1590 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1607 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1607 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1618 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1628 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1628 with
                                  | (uu____1635,m) -> n1 <= m))
                           in
                        if uu____1618 then rest1 else us1
                    | uu____1644 -> us1)
               | uu____1650 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1654 = aux u3  in
              FStar_List.map (fun _1657  -> FStar_Syntax_Syntax.U_succ _1657)
                uu____1654
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1661 = aux u  in
           match uu____1661 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____1830  ->
               let uu____1831 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1833 = env_to_string env  in
               let uu____1835 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1831 uu____1833 uu____1835);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1848 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1851 ->
                    let uu____1874 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1874
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1875 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1876 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1877 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1878 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1903 ->
                           let uu____1916 =
                             let uu____1918 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1920 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1918 uu____1920
                              in
                           failwith uu____1916
                       | uu____1925 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_1961  ->
                                         match uu___4_1961 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1968 =
                                               let uu____1975 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1975)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1968
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___243_1987 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___243_1987.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___243_1987.FStar_Syntax_Syntax.sort)
                                                  })
                                                in
                                             let t1 =
                                               inline_closure_env cfg env []
                                                 x_i
                                                in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____1993 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1996 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___252_2001 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___252_2001.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___252_2001.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2022 =
                        let uu____2023 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____2023  in
                      mk uu____2022 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2031 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2031  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2033 = lookup_bvar env x  in
                    (match uu____2033 with
                     | Univ uu____2036 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___268_2041 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___268_2041.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___268_2041.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____2047,uu____2048) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2139  ->
                              fun stack1  ->
                                match uu____2139 with
                                | (a,aq) ->
                                    let uu____2151 =
                                      let uu____2152 =
                                        let uu____2159 =
                                          let uu____2160 =
                                            let uu____2192 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2192, false)  in
                                          Clos uu____2160  in
                                        (uu____2159, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2152  in
                                    uu____2151 :: stack1) args)
                       in
                    inline_closure_env cfg env stack1 head1
                | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                    let env' =
                      FStar_All.pipe_right env
                        (FStar_List.fold_right
                           (fun _b  ->
                              fun env1  ->
                                (FStar_Pervasives_Native.None, Dummy) :: env1)
                           bs)
                       in
                    let stack1 =
                      (Abs (env, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env' stack1 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____2360 = close_binders cfg env bs  in
                    (match uu____2360 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2410) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2421 =
                      let uu____2434 =
                        let uu____2443 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2443]  in
                      close_binders cfg env uu____2434  in
                    (match uu____2421 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2488 =
                             let uu____2489 =
                               let uu____2496 =
                                 let uu____2497 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2497
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2496, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2489  in
                           mk uu____2488 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2596 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2596
                      | FStar_Util.Inr c ->
                          let uu____2610 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2610
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2629 =
                        let uu____2630 =
                          let uu____2657 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2657, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2630  in
                      mk uu____2629 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2703 =
                            let uu____2704 =
                              let uu____2711 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2711, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2704  in
                          mk uu____2703 t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack1 = (Meta (env, m, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env  in
                    let env1 =
                      FStar_List.fold_left
                        (fun env1  -> fun uu____2766  -> dummy :: env1) env
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    let typ =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let def =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    let uu____2787 =
                      let uu____2798 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2798
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2820 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___360_2836 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___360_2836.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___360_2836.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2820))
                       in
                    (match uu____2787 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___365_2854 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___365_2854.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___365_2854.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___365_2854.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___365_2854.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2871,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2937  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2954 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2954
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2969  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2993 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2993
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___388_3004 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___388_3004.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___388_3004.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___391_3005 = lb  in
                      let uu____3006 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___391_3005.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___391_3005.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3006;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___391_3005.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___391_3005.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3038  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 head1))

and (non_tail_inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg  -> fun env  -> fun t  -> inline_closure_env cfg env [] t

and (rebuild_closure :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____3130  ->
               let uu____3131 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3133 = env_to_string env  in
               let uu____3135 = stack_to_string stack  in
               let uu____3137 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3131 uu____3133 uu____3135 uu____3137);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3144,uu____3145),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3226 = close_binders cfg env' bs  in
               (match uu____3226 with
                | (bs1,uu____3242) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3262 =
                      let uu___449_3265 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___449_3265.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___449_3265.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3262)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3321 =
                 match uu____3321 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3436 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3467 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3556  ->
                                     fun uu____3557  ->
                                       match (uu____3556, uu____3557) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3707 = norm_pat env4 p1
                                              in
                                           (match uu____3707 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3467 with
                            | (pats1,env4) ->
                                ((let uu___486_3877 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___486_3877.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___490_3898 = x  in
                             let uu____3899 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___490_3898.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___490_3898.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3899
                             }  in
                           ((let uu___493_3913 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___493_3913.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___497_3924 = x  in
                             let uu____3925 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___497_3924.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___497_3924.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3925
                             }  in
                           ((let uu___500_3939 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___500_3939.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___506_3955 = x  in
                             let uu____3956 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_3955.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_3955.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3956
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___510_3973 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___510_3973.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3978 = norm_pat env2 pat  in
                     (match uu____3978 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4047 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____4047
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4066 =
                   let uu____4067 =
                     let uu____4090 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____4090)  in
                   FStar_Syntax_Syntax.Tm_match uu____4067  in
                 mk uu____4066 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (attr,names1,args) ->
                     let uu____4231 =
                       let uu____4256 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4273 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4382  ->
                                         match uu____4382 with
                                         | (a,q) ->
                                             let uu____4409 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4409, q)))))
                          in
                       (attr, uu____4256, uu____4273)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4231
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4440 =
                       let uu____4447 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4447)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4440
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4459 =
                       let uu____4468 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4468)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4459
                 | uu____4473 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4479 -> failwith "Impossible: unexpected stack element")

and (close_imp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun imp  ->
        match imp with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
            let uu____4495 =
              let uu____4496 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4496  in
            FStar_Pervasives_Native.Some uu____4495
        | i -> i

and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list * env))
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4513 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4597  ->
                  fun uu____4598  ->
                    match (uu____4597, uu____4598) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___566_4738 = b  in
                          let uu____4739 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___566_4738.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___566_4738.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4739
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4513 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
            -> c
        | uu____4881 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4894 = inline_closure_env cfg env [] t  in
                 let uu____4895 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4894 uu____4895
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4908 = inline_closure_env cfg env [] t  in
                 let uu____4909 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4908 uu____4909
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4963  ->
                           match uu____4963 with
                           | (a,q) ->
                               let uu____4984 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4984, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5001  ->
                           match uu___5_5001 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5005 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5005
                           | f -> f))
                    in
                 let uu____5009 =
                   let uu___599_5010 = c1  in
                   let uu____5011 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5011;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___599_5010.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5009)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___6_5021  ->
            match uu___6_5021 with
            | FStar_Syntax_Syntax.DECREASES uu____5023 -> false
            | uu____5027 -> true))

and (close_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___7_5046  ->
                      match uu___7_5046 with
                      | FStar_Syntax_Syntax.DECREASES uu____5048 -> false
                      | uu____5052 -> true))
               in
            let rc1 =
              let uu___616_5055 = rc  in
              let uu____5056 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___616_5055.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5056;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5065 -> lopt

let (closure_as_term :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5113 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5113 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5152 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5152 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____5172 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____5172) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5234  ->
           fun subst1  ->
             match uu____5234 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5275,uu____5276)) ->
                      let uu____5337 = b  in
                      (match uu____5337 with
                       | (bv,uu____5345) ->
                           let uu____5346 =
                             let uu____5348 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5348  in
                           if uu____5346
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5356 = unembed_binder term1  in
                              match uu____5356 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5363 =
                                      let uu___651_5364 = bv  in
                                      let uu____5365 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___651_5364.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___651_5364.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5365
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5363
                                     in
                                  let b_for_x =
                                    let uu____5371 =
                                      let uu____5378 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5378)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5371  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_5394  ->
                                         match uu___8_5394 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5396,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5398;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5399;_})
                                             ->
                                             let uu____5404 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5404
                                         | uu____5406 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5408 -> subst1)) env []
  
let reduce_primops :
  'Auu____5430 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5430)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun env  ->
        fun tm  ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5482 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5482 with
             | (head1,args) ->
                 let uu____5527 =
                   let uu____5528 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5528.FStar_Syntax_Syntax.n  in
                 (match uu____5527 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5534 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5534 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok
                             ||
                             (Prims.op_Negation
                                cfg.FStar_TypeChecker_Cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.FStar_TypeChecker_Cfg.arity
                           then
                             (FStar_TypeChecker_Cfg.log_primops cfg
                                (fun uu____5557  ->
                                   let uu____5558 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5560 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5562 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5558 uu____5560 uu____5562);
                              tm)
                           else
                             (let uu____5567 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5567 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5653  ->
                                        let uu____5654 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5654);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5659  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let r =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1
                                       in
                                    match r with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5673  ->
                                              let uu____5674 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5674);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5682  ->
                                              let uu____5683 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5685 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5683 uu____5685);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5688 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5692  ->
                                 let uu____5693 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5693);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5699  ->
                            let uu____5700 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5700);
                       (match args with
                        | (a1,uu____5706)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5731 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5745  ->
                            let uu____5746 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5746);
                       (match args with
                        | (t,uu____5752)::(r,uu____5754)::[] ->
                            let uu____5795 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5795 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5801 -> tm))
                  | uu____5812 -> tm))
  
let reduce_equality :
  'Auu____5823 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5823)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___739_5872 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___741_5875 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___741_5875.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___741_5875.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___741_5875.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___741_5875.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___741_5875.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___741_5875.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___741_5875.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___741_5875.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___741_5875.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___741_5875.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___741_5875.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___741_5875.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___741_5875.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___741_5875.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___741_5875.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___741_5875.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___741_5875.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___741_5875.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___741_5875.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___739_5872.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___739_5872.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___739_5872.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___739_5872.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___739_5872.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___739_5872.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___739_5872.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5886 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____5897 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____5908 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____5929 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____5929
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____5961 =
        let uu____5962 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5962.FStar_Syntax_Syntax.n  in
      match uu____5961 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____5971 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5980 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____5980)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____5993 =
        let uu____5994 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5994.FStar_Syntax_Syntax.n  in
      match uu____5993 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____6052 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6052 rest
           | uu____6079 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____6119 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____6119 rest
           | uu____6138 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____6212 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6212 rest
           | uu____6247 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6249 ->
          let uu____6250 =
            let uu____6252 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6252
             in
          failwith uu____6250
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6273  ->
    match uu___9_6273 with
    | FStar_Syntax_Embeddings.Zeta  -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF  -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops  -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.Reify  -> [FStar_TypeChecker_Env.Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____6280 =
          let uu____6283 =
            let uu____6284 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6284  in
          [uu____6283]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6280
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6292 =
          let uu____6295 =
            let uu____6296 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6296  in
          [uu____6295]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6292
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6304 =
          let uu____6307 =
            let uu____6308 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6308  in
          [uu____6307]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6304
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____6333 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____6333) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6384 =
            let uu____6389 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6389 s  in
          match uu____6384 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6405 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6405
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
             then [FStar_TypeChecker_Env.EraseUniverses]
             else [])
            (FStar_List.append
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                then [FStar_TypeChecker_Env.AllowUnboundUniverses]
                else [])
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.nbe_step
                then [FStar_TypeChecker_Env.NBE]
                else []))
           in
        match args with
        | uu____6440::(tm,uu____6442)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____6471)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____6492)::uu____6493::(tm,uu____6495)::[] ->
            let add_exclude s z =
              let uu____6533 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____6533
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____6540 =
              let uu____6545 = full_norm steps  in parse_steps uu____6545  in
            (match uu____6540 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6584 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6616 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6623  ->
                    match uu___10_6623 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6625 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6627 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6631 -> true
                    | uu____6635 -> false))
             in
          if uu____6616
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6645  ->
             let uu____6646 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6646);
        (let tm_norm =
           let uu____6650 =
             let uu____6665 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6665.FStar_TypeChecker_Env.nbe  in
           uu____6650 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6669  ->
              let uu____6670 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6670);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___11_6681  ->
    match uu___11_6681 with
    | (App
        (uu____6685,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6686;
                      FStar_Syntax_Syntax.vars = uu____6687;_},uu____6688,uu____6689))::uu____6690
        -> true
    | uu____6696 -> false
  
let firstn :
  'Auu____6707 .
    Prims.int ->
      'Auu____6707 Prims.list ->
        ('Auu____6707 Prims.list * 'Auu____6707 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___12_6764 =
        match uu___12_6764 with
        | (MemoLazy uu____6769)::s -> drop_irrel s
        | (UnivArgs uu____6779)::s -> drop_irrel s
        | s -> s  in
      let uu____6792 = drop_irrel stack  in
      match uu____6792 with
      | (App
          (uu____6796,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6797;
                        FStar_Syntax_Syntax.vars = uu____6798;_},uu____6799,uu____6800))::uu____6801
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6806 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6835) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6845) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6866  ->
                  match uu____6866 with
                  | (a,uu____6877) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6888 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6913 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6915 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6929 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6931 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6933 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6935 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6937 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6940 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6948 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6956 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6971 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6991 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7007 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7015 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7087  ->
                   match uu____7087 with
                   | (a,uu____7098) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7109) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Util.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern (uu____7209,uu____7210,args)
                ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7269  ->
                        match uu____7269 with
                        | (a,uu____7280) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7289,uu____7290,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7296,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7302 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7312 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7314 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7325 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7336 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7347 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7358 -> false
  
let (should_unfold :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_TypeChecker_Cfg.cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg  ->
    fun should_reify1  ->
      fun fv  ->
        fun qninfo  ->
          let attrs =
            let uu____7391 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7391 with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some ats -> ats  in
          let yes = (true, false, false)  in
          let no = (false, false, false)  in
          let fully = (true, true, false)  in
          let reif = (true, false, true)  in
          let yesno b = if b then yes else no  in
          let fullyno b = if b then fully else no  in
          let comb_or l =
            FStar_List.fold_right
              (fun uu____7590  ->
                 fun uu____7591  ->
                   match (uu____7590, uu____7591) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7697 =
            match uu____7697 with
            | (x,y,z) ->
                let uu____7717 = FStar_Util.string_of_bool x  in
                let uu____7719 = FStar_Util.string_of_bool y  in
                let uu____7721 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7717 uu____7719
                  uu____7721
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7749  ->
                    let uu____7750 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7752 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7750 uu____7752);
               if b then reif else no)
            else
              if
                (let uu____7767 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7767)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7772  ->
                      FStar_Util.print_string
                        " >> It's a primop, not unfolding\n");
                 no)
              else
                (match (qninfo,
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr))
                 with
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7807),uu____7808);
                        FStar_Syntax_Syntax.sigrng = uu____7809;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7811;
                        FStar_Syntax_Syntax.sigattrs = uu____7812;_},uu____7813),uu____7814),uu____7815,uu____7816,uu____7817)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7924  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7926,uu____7927,uu____7928,uu____7929) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7996  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7999),uu____8000);
                        FStar_Syntax_Syntax.sigrng = uu____8001;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8003;
                        FStar_Syntax_Syntax.sigattrs = uu____8004;_},uu____8005),uu____8006),uu____8007,uu____8008,uu____8009)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8116  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8118,FStar_Pervasives_Native.Some
                    uu____8119,uu____8120,uu____8121) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8189  ->
                           let uu____8190 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8190);
                      (let uu____8193 =
                         let uu____8205 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8231 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8231
                            in
                         let uu____8243 =
                           let uu____8255 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8281 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8281
                              in
                           let uu____8297 =
                             let uu____8309 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8335 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8335
                                in
                             [uu____8309]  in
                           uu____8255 :: uu____8297  in
                         uu____8205 :: uu____8243  in
                       comb_or uu____8193))
                 | (uu____8383,uu____8384,FStar_Pervasives_Native.Some
                    uu____8385,uu____8386) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8454  ->
                           let uu____8455 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8455);
                      (let uu____8458 =
                         let uu____8470 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8496 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8496
                            in
                         let uu____8508 =
                           let uu____8520 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8546 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8546
                              in
                           let uu____8562 =
                             let uu____8574 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8600 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8600
                                in
                             [uu____8574]  in
                           uu____8520 :: uu____8562  in
                         uu____8470 :: uu____8508  in
                       comb_or uu____8458))
                 | (uu____8648,uu____8649,uu____8650,FStar_Pervasives_Native.Some
                    uu____8651) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8719  ->
                           let uu____8720 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8720);
                      (let uu____8723 =
                         let uu____8735 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8761 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8761
                            in
                         let uu____8773 =
                           let uu____8785 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8811 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8811
                              in
                           let uu____8827 =
                             let uu____8839 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8865 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8865
                                in
                             [uu____8839]  in
                           uu____8785 :: uu____8827  in
                         uu____8735 :: uu____8773  in
                       comb_or uu____8723))
                 | uu____8913 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8959  ->
                           let uu____8960 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8962 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8964 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8960 uu____8962 uu____8964);
                      (let uu____8967 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___13_8973  ->
                                 match uu___13_8973 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8979 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8979 l))
                          in
                       FStar_All.pipe_left yesno uu____8967)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8995  ->
               let uu____8996 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8998 =
                 let uu____9000 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9000  in
               let uu____9001 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8996 uu____8998 uu____9001);
          (match res with
           | (false ,uu____9004,uu____9005) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9030 ->
               let uu____9040 =
                 let uu____9042 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9042
                  in
               FStar_All.pipe_left failwith uu____9040)
  
let decide_unfolding :
  'Auu____9061 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9061 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list)
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              let res =
                should_unfold cfg (fun cfg1  -> should_reify cfg1 stack) fv
                  qninfo
                 in
              match res with
              | Should_unfold_no  -> FStar_Pervasives_Native.None
              | Should_unfold_yes  ->
                  FStar_Pervasives_Native.Some (cfg, stack)
              | Should_unfold_fully  ->
                  let cfg' =
                    let uu___1161_9130 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1163_9133 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.delta_constant);
                           FStar_TypeChecker_Cfg.unfold_only =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_fully =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_attr =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1163_9133.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1161_9130.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs (us,r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let rec push1 e s =
                    match s with
                    | [] -> [e]
                    | (UnivArgs (us,r))::t ->
                        let uu____9195 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9195
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9207 =
                      let uu____9214 =
                        let uu____9215 =
                          let uu____9216 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9216  in
                        FStar_Syntax_Syntax.Tm_constant uu____9215  in
                      FStar_Syntax_Syntax.mk uu____9214  in
                    uu____9207 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let stack1 =
                    push1
                      (App
                         (env, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack
                     in
                  FStar_Pervasives_Native.Some (cfg, stack1)
  
let (is_fext_on_domain :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let fext_lid s =
      FStar_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
        FStar_Range.dummyRange
       in
    let on_domain_lids =
      FStar_All.pipe_right ["on_domain"; "on_dom"; "on_domain_g"; "on_dom_g"]
        (FStar_List.map fext_lid)
       in
    let is_on_dom fv =
      FStar_All.pipe_right on_domain_lids
        (FStar_List.existsb (fun l  -> FStar_Syntax_Syntax.fv_eq_lid fv l))
       in
    let uu____9282 =
      let uu____9283 = FStar_Syntax_Subst.compress t  in
      uu____9283.FStar_Syntax_Syntax.n  in
    match uu____9282 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9314 =
          let uu____9315 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9315.FStar_Syntax_Syntax.n  in
        (match uu____9314 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____9332 =
                 let uu____9339 =
                   let uu____9350 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9350 FStar_List.tl  in
                 FStar_All.pipe_right uu____9339 FStar_List.hd  in
               FStar_All.pipe_right uu____9332 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9449 -> FStar_Pervasives_Native.None)
    | uu____9450 -> FStar_Pervasives_Native.None
  
let rec (norm :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if
              (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____9719 ->
                   let uu____9742 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9742
               | uu____9745 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9755  ->
               let uu____9756 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9758 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9760 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9762 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9770 =
                 let uu____9772 =
                   let uu____9775 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9775
                    in
                 stack_to_string uu____9772  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9756 uu____9758 uu____9760 uu____9762 uu____9770);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9803  ->
               let uu____9804 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9804);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9810  ->
                     let uu____9811 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9811);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9814 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9818  ->
                     let uu____9819 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9819);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9822 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9826  ->
                     let uu____9827 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9827);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9830 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9834  ->
                     let uu____9835 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9835);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9838;
                 FStar_Syntax_Syntax.fv_delta = uu____9839;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9843  ->
                     let uu____9844 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9844);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9847;
                 FStar_Syntax_Syntax.fv_delta = uu____9848;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9849);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9859  ->
                     let uu____9860 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9860);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9866 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9866 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9869) when
                    _9869 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9873  ->
                          let uu____9874 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9874);
                     rebuild cfg env stack t1)
                | uu____9877 ->
                    let uu____9880 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9880 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____9907 ->
               let uu____9914 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____9914
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9942 = is_norm_request hd1 args  in
                  uu____9942 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9948 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9948))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9976 = is_norm_request hd1 args  in
                  uu____9976 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1271_9983 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1273_9986 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1273_9986.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1271_9983.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1271_9983.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1271_9983.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1271_9983.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1271_9983.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1271_9983.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____9993 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____9993 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10029  ->
                                 fun stack1  ->
                                   match uu____10029 with
                                   | (a,aq) ->
                                       let uu____10041 =
                                         let uu____10042 =
                                           let uu____10049 =
                                             let uu____10050 =
                                               let uu____10082 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10082, false)
                                                in
                                             Clos uu____10050  in
                                           (uu____10049, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10042  in
                                       uu____10041 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10150  ->
                            let uu____10151 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10151);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10178 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____10178)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____10189 =
                            let uu____10191 =
                              let uu____10193 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____10193  in
                            FStar_Util.string_of_int uu____10191  in
                          let uu____10200 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____10202 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____10189 uu____10200 uu____10202)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10221 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____10221)
                      else ();
                      (let delta_level =
                         let uu____10229 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___14_10236  ->
                                   match uu___14_10236 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____10238 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____10240 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____10244 -> true
                                   | uu____10248 -> false))
                            in
                         if uu____10229
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1314_10256 = cfg  in
                         let uu____10257 =
                           let uu___1316_10258 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1316_10258.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____10257;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1314_10256.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1314_10256.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1314_10256.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1314_10256.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1314_10256.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1314_10256.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____10266 =
                             let uu____10267 =
                               let uu____10272 = FStar_Util.now ()  in
                               (t1, uu____10272)  in
                             Debug uu____10267  in
                           uu____10266 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10277 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10277
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10288 =
                      let uu____10295 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10295, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10288  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10304 = lookup_bvar env x  in
               (match uu____10304 with
                | Univ uu____10305 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10359 = FStar_ST.op_Bang r  in
                      (match uu____10359 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10455  ->
                                 let uu____10456 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10458 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10456
                                   uu____10458);
                            (let uu____10461 = maybe_weakly_reduced t'  in
                             if uu____10461
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10464 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10508)::uu____10509 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10520,uu____10521))::stack_rest ->
                    (match c with
                     | Univ uu____10525 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10534 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10564  ->
                                    let uu____10565 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10565);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10601  ->
                                    let uu____10602 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10602);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10650  ->
                          let uu____10651 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10651);
                     norm cfg env stack1 t1)
                | (Match uu____10654)::uu____10655 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10670 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10670 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10706  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10750 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10750)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_10758 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_10758.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_10758.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10759 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10765  ->
                                 let uu____10766 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10766);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_10781 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_10781.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10785)::uu____10786 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10797 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10797 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10833  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10877 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10877)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_10885 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_10885.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_10885.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10886 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10892  ->
                                 let uu____10893 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10893);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_10908 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_10908.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10912)::uu____10913 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10926 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10926 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10962  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11006 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11006)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11014 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11014.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11014.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11015 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11021  ->
                                 let uu____11022 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11022);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11037 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11037.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11041)::uu____11042 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11057 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11057 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11093  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11137 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11137)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11145 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11145.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11145.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11146 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11152  ->
                                 let uu____11153 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11153);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11168 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11168.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11172)::uu____11173 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11188 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11188 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11224  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11268 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11268)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11276 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11276.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11276.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11277 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11283  ->
                                 let uu____11284 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11284);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11299 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11299.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11303)::uu____11304 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11323 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11323 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11359  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11403 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11403)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11411 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11411.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11411.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11412 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11418  ->
                                 let uu____11419 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11419);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11434 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11434.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11442 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11442 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11478  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11522 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11522)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11530 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11530.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11530.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11531 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11537  ->
                                 let uu____11538 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11538);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11553 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11553.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____11597  ->
                         fun stack1  ->
                           match uu____11597 with
                           | (a,aq) ->
                               let uu____11609 =
                                 let uu____11610 =
                                   let uu____11617 =
                                     let uu____11618 =
                                       let uu____11650 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11650, false)  in
                                     Clos uu____11618  in
                                   (uu____11617, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11610  in
                               uu____11609 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____11718  ->
                     let uu____11719 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11719);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____11733) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
               -> norm cfg env stack x.FStar_Syntax_Syntax.sort
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___1468_11778 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1468_11778.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1468_11778.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11779 ->
                      let uu____11794 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11794)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11798 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11798 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11829 =
                          let uu____11830 =
                            let uu____11837 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1477_11843 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1477_11843.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1477_11843.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11837)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11830  in
                        mk uu____11829 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____11867 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11867
               else
                 (let uu____11870 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11870 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11878 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11904  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11878 c1  in
                      let t2 =
                        let uu____11928 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11928 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12041)::uu____12042 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12055  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12057)::uu____12058 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12069  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12071,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12072;
                                   FStar_Syntax_Syntax.vars = uu____12073;_},uu____12074,uu____12075))::uu____12076
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12083  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12085)::uu____12086 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12097  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12099 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12102  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12107  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12133 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12133
                         | FStar_Util.Inr c ->
                             let uu____12147 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12147
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12170 =
                               let uu____12171 =
                                 let uu____12198 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12198, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12171
                                in
                             mk uu____12170 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12233 ->
                           let uu____12234 =
                             let uu____12235 =
                               let uu____12236 =
                                 let uu____12263 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12263, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12236
                                in
                             mk uu____12235 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12234))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   let uu___1556_12341 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1558_12344 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1558_12344.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1556_12341.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 norm cfg' env ((Cfg cfg) :: stack1) head1
               else norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____12385 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12385 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1571_12405 = cfg  in
                               let uu____12406 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12406;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1571_12405.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12413 =
                                 let uu____12414 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12414  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12413
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1578_12417 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1578_12417.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1578_12417.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1578_12417.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1578_12417.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12418 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12418
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12431,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12432;
                               FStar_Syntax_Syntax.lbunivs = uu____12433;
                               FStar_Syntax_Syntax.lbtyp = uu____12434;
                               FStar_Syntax_Syntax.lbeff = uu____12435;
                               FStar_Syntax_Syntax.lbdef = uu____12436;
                               FStar_Syntax_Syntax.lbattrs = uu____12437;
                               FStar_Syntax_Syntax.lbpos = uu____12438;_}::uu____12439),uu____12440)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12486 =
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.do_not_unfold_pure_lets)
                   &&
                   ((((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                        &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.FStar_TypeChecker_Cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)))
                  in
               if uu____12486
               then
                 let binder =
                   let uu____12490 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12490  in
                 let env1 =
                   let uu____12500 =
                     let uu____12507 =
                       let uu____12508 =
                         let uu____12540 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12540,
                           false)
                          in
                       Clos uu____12508  in
                     ((FStar_Pervasives_Native.Some binder), uu____12507)  in
                   uu____12500 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12615  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12622  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12624 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12624))
                 else
                   (let uu____12627 =
                      let uu____12632 =
                        let uu____12633 =
                          let uu____12640 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12640
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12633]  in
                      FStar_Syntax_Subst.open_term uu____12632 body  in
                    match uu____12627 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12667  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12676 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12676  in
                            FStar_Util.Inl
                              (let uu___1620_12692 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1620_12692.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1620_12692.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____12695  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1625_12698 = lb  in
                             let uu____12699 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1625_12698.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1625_12698.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12699;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1625_12698.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1625_12698.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12728  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1632_12753 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1632_12753.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____12757  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                 ||
                 ((Prims.op_Negation
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)
               ->
               let uu____12778 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12778 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12814 =
                               let uu___1648_12815 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1648_12815.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1648_12815.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12814  in
                           let uu____12816 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12816 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12842 =
                                   FStar_List.map (fun uu____12858  -> dummy)
                                     lbs1
                                    in
                                 let uu____12859 =
                                   let uu____12868 =
                                     FStar_List.map
                                       (fun uu____12890  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12868 env  in
                                 FStar_List.append uu____12842 uu____12859
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12916 =
                                       let uu___1662_12917 = rc  in
                                       let uu____12918 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1662_12917.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12918;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1662_12917.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12916
                                 | uu____12927 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1667_12933 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1667_12933.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1667_12933.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1667_12933.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1667_12933.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12943 =
                        FStar_List.map (fun uu____12959  -> dummy) lbs2  in
                      FStar_List.append uu____12943 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12967 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12967 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1676_12983 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1676_12983.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1676_12983.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13017 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13017
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13038 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13116  ->
                        match uu____13116 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1692_13241 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1692_13241.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1692_13241.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____13038 with
                | (rec_env,memos,uu____13432) ->
                    let uu____13487 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____13736 =
                               let uu____13743 =
                                 let uu____13744 =
                                   let uu____13776 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13776, false)
                                    in
                                 Clos uu____13744  in
                               (FStar_Pervasives_Native.None, uu____13743)
                                in
                             uu____13736 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____13861  ->
                     let uu____13862 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13862);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13886 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13890::uu____13891 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13896) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern
                                 (attr,names1,args) ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 let names2 =
                                   FStar_All.pipe_right names1
                                     (FStar_List.map (norm cfg env []))
                                    in
                                 let args2 =
                                   FStar_TypeChecker_PatternInference.remove_invalid_pattern
                                     names2 args1
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (attr, names2, args2)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____13975 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (attr,names1,args) ->
                                  let names2 =
                                    FStar_All.pipe_right names1
                                      (FStar_List.map (norm cfg env []))
                                     in
                                  let uu____14028 =
                                    let uu____14053 =
                                      norm_pattern_args cfg env args  in
                                    (attr, names2, uu____14053)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14028
                              | uu____14084 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14090 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14114 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14128 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14142 =
                        let uu____14144 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14146 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14144 uu____14146
                         in
                      failwith uu____14142
                    else
                      (let uu____14151 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14151)
                | uu____14152 -> norm cfg env stack t2))

and (do_unfold_fv :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let uu____14161 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14161 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14175  ->
                        let uu____14176 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14176);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14189  ->
                        let uu____14190 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14192 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14190 uu____14192);
                   (let t1 =
                      if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_until
                          =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14205))::stack1 ->
                          ((let uu____14214 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14214
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14222 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14222) us'
                            else ());
                           (let env1 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env1  ->
                                      fun u  ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env1) env)
                               in
                            norm cfg env1 stack1 t1))
                      | uu____14258 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14261 ->
                          let uu____14264 =
                            let uu____14266 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14266
                             in
                          failwith uu____14264
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name *
                                            FStar_Syntax_Syntax.monad_name))
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                then
                  let new_steps =
                    [FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.AllowUnboundUniverses;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.Inlining]  in
                  let uu___1807_14294 = cfg  in
                  let uu____14295 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14295;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1807_14294.FStar_TypeChecker_Cfg.reifying)
                  }
                else cfg  in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (env, metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                (match stack with
                 | (App
                     (uu____14326,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14327;
                                    FStar_Syntax_Syntax.vars = uu____14328;_},uu____14329,uu____14330))::uu____14331
                     -> ()
                 | uu____14336 ->
                     let uu____14339 =
                       let uu____14341 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14341
                        in
                     failwith uu____14339);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14350  ->
                      let uu____14351 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14353 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14351
                        uu____14353);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14357 =
                    let uu____14358 = FStar_Syntax_Subst.compress head3  in
                    uu____14358.FStar_Syntax_Syntax.n  in
                  match uu____14357 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14379 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14379
                         in
                      let uu____14380 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____14380 with
                       | (uu____14381,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14391 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14402 =
                                    let uu____14403 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14403.FStar_Syntax_Syntax.n  in
                                  match uu____14402 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14409,uu____14410))
                                      ->
                                      let uu____14419 =
                                        let uu____14420 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14420.FStar_Syntax_Syntax.n  in
                                      (match uu____14419 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14426,msrc,uu____14428))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14437 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14437
                                       | uu____14438 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14439 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14440 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14440 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1879_14445 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1879_14445.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1879_14445.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1879_14445.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1879_14445.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1879_14445.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14446 = FStar_List.tl stack
                                        in
                                     let uu____14447 =
                                       let uu____14448 =
                                         let uu____14455 =
                                           let uu____14456 =
                                             let uu____14470 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14470)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14456
                                            in
                                         FStar_Syntax_Syntax.mk uu____14455
                                          in
                                       uu____14448
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14446 uu____14447
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14486 =
                                       let uu____14488 = is_return body  in
                                       match uu____14488 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14493;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14494;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14497 -> false  in
                                     if uu____14486
                                     then
                                       norm cfg env stack
                                         lb.FStar_Syntax_Syntax.lbdef
                                     else
                                       (let rng =
                                          head3.FStar_Syntax_Syntax.pos  in
                                        let head4 =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify
                                            lb.FStar_Syntax_Syntax.lbdef
                                           in
                                        let body1 =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify body
                                           in
                                        let body_rc =
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              = m;
                                            FStar_Syntax_Syntax.residual_typ
                                              =
                                              (FStar_Pervasives_Native.Some t);
                                            FStar_Syntax_Syntax.residual_flags
                                              = []
                                          }  in
                                        let body2 =
                                          let uu____14521 =
                                            let uu____14528 =
                                              let uu____14529 =
                                                let uu____14548 =
                                                  let uu____14557 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14557]  in
                                                (uu____14548, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14529
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14528
                                             in
                                          uu____14521
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14596 =
                                            let uu____14597 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14597.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14596 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14603::uu____14604::[])
                                              ->
                                              let uu____14609 =
                                                let uu____14616 =
                                                  let uu____14617 =
                                                    let uu____14624 =
                                                      let uu____14625 =
                                                        let uu____14626 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14626
                                                         in
                                                      let uu____14627 =
                                                        let uu____14630 =
                                                          let uu____14631 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14631
                                                           in
                                                        [uu____14630]  in
                                                      uu____14625 ::
                                                        uu____14627
                                                       in
                                                    (bind1, uu____14624)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14617
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14616
                                                 in
                                              uu____14609
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14634 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____14649 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14649
                                          then
                                            let uu____14662 =
                                              let uu____14671 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____14671
                                               in
                                            let uu____14672 =
                                              let uu____14683 =
                                                let uu____14692 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____14692
                                                 in
                                              [uu____14683]  in
                                            uu____14662 :: uu____14672
                                          else []  in
                                        let reified =
                                          let uu____14730 =
                                            let uu____14737 =
                                              let uu____14738 =
                                                let uu____14755 =
                                                  let uu____14766 =
                                                    let uu____14777 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____14786 =
                                                      let uu____14797 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____14797]  in
                                                    uu____14777 ::
                                                      uu____14786
                                                     in
                                                  let uu____14830 =
                                                    let uu____14841 =
                                                      let uu____14852 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____14861 =
                                                        let uu____14872 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____14881 =
                                                          let uu____14892 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____14901 =
                                                            let uu____14912 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____14912]  in
                                                          uu____14892 ::
                                                            uu____14901
                                                           in
                                                        uu____14872 ::
                                                          uu____14881
                                                         in
                                                      uu____14852 ::
                                                        uu____14861
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____14841
                                                     in
                                                  FStar_List.append
                                                    uu____14766 uu____14830
                                                   in
                                                (bind_inst, uu____14755)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____14738
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14737
                                             in
                                          uu____14730
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____14993  ->
                                             let uu____14994 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____14996 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____14994 uu____14996);
                                        (let uu____14999 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____14999 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15027 = FStar_Options.defensive ()  in
                        if uu____15027
                        then
                          let is_arg_impure uu____15042 =
                            match uu____15042 with
                            | (e,q) ->
                                let uu____15056 =
                                  let uu____15057 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15057.FStar_Syntax_Syntax.n  in
                                (match uu____15056 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15073 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15073
                                 | uu____15075 -> false)
                             in
                          let uu____15077 =
                            let uu____15079 =
                              let uu____15090 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15090 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15079  in
                          (if uu____15077
                           then
                             let uu____15116 =
                               let uu____15122 =
                                 let uu____15124 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15124
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15122)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15116
                           else ())
                        else ());
                       (let fallback1 uu____15137 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15141  ->
                               let uu____15142 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15142 "");
                          (let uu____15146 = FStar_List.tl stack  in
                           let uu____15147 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15146 uu____15147)
                           in
                        let fallback2 uu____15153 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15157  ->
                               let uu____15158 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15158 "");
                          (let uu____15162 = FStar_List.tl stack  in
                           let uu____15163 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15162 uu____15163)
                           in
                        let uu____15168 =
                          let uu____15169 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15169.FStar_Syntax_Syntax.n  in
                        match uu____15168 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15175 =
                              let uu____15177 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15177  in
                            if uu____15175
                            then fallback1 ()
                            else
                              (let uu____15182 =
                                 let uu____15184 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15184  in
                               if uu____15182
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15201 =
                                      let uu____15206 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15206 args
                                       in
                                    uu____15201 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15207 = FStar_List.tl stack  in
                                  norm cfg env uu____15207 t1))
                        | uu____15208 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15210) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____15234 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15234  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15238  ->
                            let uu____15239 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15239);
                       (let uu____15242 = FStar_List.tl stack  in
                        norm cfg env uu____15242 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____15363  ->
                                match uu____15363 with
                                | (pat,wopt,tm) ->
                                    let uu____15411 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____15411)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____15443 = FStar_List.tl stack  in
                      norm cfg env uu____15443 tm
                  | uu____15444 -> fallback ()))

and (reify_lift :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.FStar_TypeChecker_Cfg.tcenv  in
            FStar_TypeChecker_Cfg.log cfg
              (fun uu____15458  ->
                 let uu____15459 = FStar_Ident.string_of_lid msrc  in
                 let uu____15461 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15463 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15459
                   uu____15461 uu____15463);
            (let uu____15466 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15466
             then
               let ed =
                 let uu____15470 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15470  in
               let uu____15471 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15471 with
               | (uu____15472,return_repr) ->
                   let return_inst =
                     let uu____15485 =
                       let uu____15486 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15486.FStar_Syntax_Syntax.n  in
                     match uu____15485 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15492::[]) ->
                         let uu____15497 =
                           let uu____15504 =
                             let uu____15505 =
                               let uu____15512 =
                                 let uu____15513 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15513]  in
                               (return_tm, uu____15512)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15505  in
                           FStar_Syntax_Syntax.mk uu____15504  in
                         uu____15497 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15516 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15520 =
                     let uu____15527 =
                       let uu____15528 =
                         let uu____15545 =
                           let uu____15556 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15565 =
                             let uu____15576 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15576]  in
                           uu____15556 :: uu____15565  in
                         (return_inst, uu____15545)  in
                       FStar_Syntax_Syntax.Tm_app uu____15528  in
                     FStar_Syntax_Syntax.mk uu____15527  in
                   uu____15520 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15623 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15623 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15626 =
                      let uu____15628 = FStar_Ident.text_of_lid msrc  in
                      let uu____15630 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15628 uu____15630
                       in
                    failwith uu____15626
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15633;
                      FStar_TypeChecker_Env.mtarget = uu____15634;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15635;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15657 =
                      let uu____15659 = FStar_Ident.text_of_lid msrc  in
                      let uu____15661 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15659 uu____15661
                       in
                    failwith uu____15657
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15664;
                      FStar_TypeChecker_Env.mtarget = uu____15665;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15666;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15701 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15702 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15701 t FStar_Syntax_Syntax.tun uu____15702))

and (norm_pattern_args :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list -> FStar_Syntax_Syntax.args Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____15762  ->
                   match uu____15762 with
                   | (a,imp) ->
                       let uu____15781 = norm cfg env [] a  in
                       (uu____15781, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____15791  ->
             let uu____15792 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____15794 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____15792 uu____15794);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15820 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _15823  -> FStar_Pervasives_Native.Some _15823)
                     uu____15820
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2029_15824 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2029_15824.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2029_15824.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15846 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _15849  -> FStar_Pervasives_Native.Some _15849)
                     uu____15846
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2040_15850 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2040_15850.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2040_15850.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15895  ->
                      match uu____15895 with
                      | (a,i) ->
                          let uu____15915 = norm cfg env [] a  in
                          (uu____15915, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___15_15937  ->
                       match uu___15_15937 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15941 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15941
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2057_15949 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2059_15952 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2059_15952.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2057_15949.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2057_15949.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____15956 = b  in
        match uu____15956 with
        | (x,imp) ->
            let x1 =
              let uu___2067_15964 = x  in
              let uu____15965 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2067_15964.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2067_15964.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15965
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____15976 =
                    let uu____15977 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____15977  in
                  FStar_Pervasives_Native.Some uu____15976
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15988 =
          FStar_List.fold_left
            (fun uu____16022  ->
               fun b  ->
                 match uu____16022 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15988 with | (nbs,uu____16102) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____16134 =
              let uu___2092_16135 = rc  in
              let uu____16136 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2092_16135.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16136;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2092_16135.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16134
        | uu____16145 -> lopt

and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu____16155 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16157 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____16155 uu____16157)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___16_16169  ->
      match uu___16_16169 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____16182 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____16182 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____16186 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____16186)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____16194 = norm_cb cfg  in
            reduce_primops uu____16194 cfg env tm  in
          let uu____16199 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____16199
          then tm1
          else
            (let w t =
               let uu___2120_16218 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2120_16218.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2120_16218.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16230 =
                 let uu____16231 = FStar_Syntax_Util.unmeta t  in
                 uu____16231.FStar_Syntax_Syntax.n  in
               match uu____16230 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16243 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16307)::args1,(bv,uu____16310)::bs1) ->
                   let uu____16364 =
                     let uu____16365 = FStar_Syntax_Subst.compress t  in
                     uu____16365.FStar_Syntax_Syntax.n  in
                   (match uu____16364 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16370 -> false)
               | ([],[]) -> true
               | (uu____16401,uu____16402) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16453 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16455 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16453
                    uu____16455)
               else ();
               (let uu____16460 = FStar_Syntax_Util.head_and_args' t  in
                match uu____16460 with
                | (hd1,args) ->
                    let uu____16499 =
                      let uu____16500 = FStar_Syntax_Subst.compress hd1  in
                      uu____16500.FStar_Syntax_Syntax.n  in
                    (match uu____16499 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____16508 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____16510 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____16512 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16508 uu____16510 uu____16512)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16517 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16535 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16537 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16535
                    uu____16537)
               else ();
               (let uu____16542 = FStar_Syntax_Util.is_squash t  in
                match uu____16542 with
                | FStar_Pervasives_Native.Some (uu____16553,t') ->
                    is_applied bs t'
                | uu____16565 ->
                    let uu____16574 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____16574 with
                     | FStar_Pervasives_Native.Some (uu____16585,t') ->
                         is_applied bs t'
                     | uu____16597 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____16621 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16621 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16628)::(q,uu____16630)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16673 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____16675 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____16673 uu____16675)
                    else ();
                    (let uu____16680 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____16680 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16685 =
                           let uu____16686 = FStar_Syntax_Subst.compress p
                              in
                           uu____16686.FStar_Syntax_Syntax.n  in
                         (match uu____16685 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____16697 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____16697))
                          | uu____16700 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____16703)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____16728 =
                           let uu____16729 = FStar_Syntax_Subst.compress p1
                              in
                           uu____16729.FStar_Syntax_Syntax.n  in
                         (match uu____16728 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____16740 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____16740))
                          | uu____16743 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,attr,pats,phi1)) ->
                         let uu____16752 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____16752 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____16757 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____16757 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if
                                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 3\n"
                                    else ();
                                    (let ftrue =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_true
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____16771 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____16771))
                               | uu____16774 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____16779)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____16804 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____16804 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if
                                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 4\n"
                                    else ();
                                    (let ffalse =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_false
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____16818 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____16818))
                               | uu____16821 -> FStar_Pervasives_Native.None)
                          | uu____16824 -> FStar_Pervasives_Native.None)
                     | uu____16827 -> FStar_Pervasives_Native.None))
               | uu____16830 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____16843 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16843 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____16849)::[],uu____16850,uu____16851,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16875 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____16877 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____16875
                         uu____16877)
                    else ();
                    is_quantified_const bv phi')
               | uu____16882 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16897 =
                 let uu____16898 = FStar_Syntax_Subst.compress phi  in
                 uu____16898.FStar_Syntax_Syntax.n  in
               match uu____16897 with
               | FStar_Syntax_Syntax.Tm_match (uu____16904,br::brs) ->
                   let uu____16971 = br  in
                   (match uu____16971 with
                    | (uu____16989,uu____16990,e) ->
                        let r =
                          let uu____17012 = simp_t e  in
                          match uu____17012 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17024 =
                                FStar_List.for_all
                                  (fun uu____17043  ->
                                     match uu____17043 with
                                     | (uu____17057,uu____17058,e') ->
                                         let uu____17072 = simp_t e'  in
                                         uu____17072 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17024
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17088 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17098 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17098
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17136 =
                 match uu____17136 with
                 | (t1,q) ->
                     let uu____17157 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17157 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17189 -> (t1, q))
                  in
               let uu____17202 = FStar_Syntax_Util.head_and_args t  in
               match uu____17202 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____17282 =
                 let uu____17283 = FStar_Syntax_Util.unmeta ty  in
                 uu____17283.FStar_Syntax_Syntax.n  in
               match uu____17282 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17288) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17293,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17317 -> false  in
             let simplify1 arg =
               let uu____17350 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17350, arg)  in
             let uu____17365 = is_forall_const tm1  in
             match uu____17365 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____17371 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____17373 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17371
                       uu____17373)
                  else ();
                  (let uu____17378 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____17378))
             | FStar_Pervasives_Native.None  ->
                 let uu____17379 =
                   let uu____17380 = FStar_Syntax_Subst.compress tm1  in
                   uu____17380.FStar_Syntax_Syntax.n  in
                 (match uu____17379 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17384;
                              FStar_Syntax_Syntax.vars = uu____17385;_},uu____17386);
                         FStar_Syntax_Syntax.pos = uu____17387;
                         FStar_Syntax_Syntax.vars = uu____17388;_},args)
                      ->
                      let uu____17418 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17418
                      then
                        let uu____17421 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17421 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17479)::
                             (uu____17480,(arg,uu____17482))::[] ->
                             maybe_auto_squash arg
                         | (uu____17555,(arg,uu____17557))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17558)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17631)::uu____17632::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17702::(FStar_Pervasives_Native.Some (false
                                         ),uu____17703)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17773 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17791 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17791
                         then
                           let uu____17794 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17794 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17852)::uu____17853::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17923::(FStar_Pervasives_Native.Some (true
                                           ),uu____17924)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17994)::(uu____17995,(arg,uu____17997))::[]
                               -> maybe_auto_squash arg
                           | (uu____18070,(arg,uu____18072))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18073)::[]
                               -> maybe_auto_squash arg
                           | uu____18146 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18164 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18164
                            then
                              let uu____18167 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18167 with
                              | uu____18225::(FStar_Pervasives_Native.Some
                                              (true ),uu____18226)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18296)::uu____18297::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18367)::(uu____18368,(arg,uu____18370))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18443,(p,uu____18445))::(uu____18446,
                                                                (q,uu____18448))::[]
                                  ->
                                  let uu____18520 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18520
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18525 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18543 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18543
                               then
                                 let uu____18546 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18546 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18604)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18605)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18679)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18680)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18754)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18755)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18829)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18830)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18904,(arg,uu____18906))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18907)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18980)::(uu____18981,(arg,uu____18983))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19056,(arg,uu____19058))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19059)::[]
                                     ->
                                     let uu____19132 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19132
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19133)::(uu____19134,(arg,uu____19136))::[]
                                     ->
                                     let uu____19209 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19209
                                 | (uu____19210,(p,uu____19212))::(uu____19213,
                                                                   (q,uu____19215))::[]
                                     ->
                                     let uu____19287 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19287
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19292 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19310 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19310
                                  then
                                    let uu____19313 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19313 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19371)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19415)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19459 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19477 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19477
                                     then
                                       match args with
                                       | (t,uu____19481)::[] ->
                                           let uu____19506 =
                                             let uu____19507 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19507.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19506 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19510::[],body,uu____19512)
                                                ->
                                                let uu____19547 = simp_t body
                                                   in
                                                (match uu____19547 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19553 -> tm1)
                                            | uu____19557 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19559))::(t,uu____19561)::[]
                                           ->
                                           let uu____19601 =
                                             let uu____19602 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19602.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19601 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19605::[],body,uu____19607)
                                                ->
                                                let uu____19642 = simp_t body
                                                   in
                                                (match uu____19642 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19650 -> tm1)
                                            | uu____19654 -> tm1)
                                       | uu____19655 -> tm1
                                     else
                                       (let uu____19668 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19668
                                        then
                                          match args with
                                          | (t,uu____19672)::[] ->
                                              let uu____19697 =
                                                let uu____19698 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19698.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19697 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19701::[],body,uu____19703)
                                                   ->
                                                   let uu____19738 =
                                                     simp_t body  in
                                                   (match uu____19738 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19744 -> tm1)
                                               | uu____19748 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19750))::(t,uu____19752)::[]
                                              ->
                                              let uu____19792 =
                                                let uu____19793 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19793.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19792 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19796::[],body,uu____19798)
                                                   ->
                                                   let uu____19833 =
                                                     simp_t body  in
                                                   (match uu____19833 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____19841 -> tm1)
                                               | uu____19845 -> tm1)
                                          | uu____19846 -> tm1
                                        else
                                          (let uu____19859 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19859
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19862;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19863;_},uu____19864)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19890;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19891;_},uu____19892)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19918 -> tm1
                                           else
                                             (let uu____19931 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____19931
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____19945 =
                                                    let uu____19946 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____19946.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____19945 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____19957 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____19971 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____19971
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____20010 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____20010
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____20016 =
                                                         let uu____20017 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____20017.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____20016 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____20020 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____20028 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____20028
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____20037
                                                                  =
                                                                  let uu____20038
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____20038.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____20037
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____20044)
                                                                    -> hd1
                                                                | uu____20069
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____20073
                                                                =
                                                                let uu____20084
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____20084]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____20073)
                                                       | uu____20117 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____20122 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____20122 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____20142 ->
                                                     let uu____20151 =
                                                       let uu____20158 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____20158 cfg env
                                                        in
                                                     uu____20151 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20164;
                         FStar_Syntax_Syntax.vars = uu____20165;_},args)
                      ->
                      let uu____20191 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20191
                      then
                        let uu____20194 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20194 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20252)::
                             (uu____20253,(arg,uu____20255))::[] ->
                             maybe_auto_squash arg
                         | (uu____20328,(arg,uu____20330))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20331)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20404)::uu____20405::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20475::(FStar_Pervasives_Native.Some (false
                                         ),uu____20476)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20546 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20564 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20564
                         then
                           let uu____20567 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20567 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20625)::uu____20626::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20696::(FStar_Pervasives_Native.Some (true
                                           ),uu____20697)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20767)::(uu____20768,(arg,uu____20770))::[]
                               -> maybe_auto_squash arg
                           | (uu____20843,(arg,uu____20845))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20846)::[]
                               -> maybe_auto_squash arg
                           | uu____20919 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20937 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20937
                            then
                              let uu____20940 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20940 with
                              | uu____20998::(FStar_Pervasives_Native.Some
                                              (true ),uu____20999)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21069)::uu____21070::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21140)::(uu____21141,(arg,uu____21143))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21216,(p,uu____21218))::(uu____21219,
                                                                (q,uu____21221))::[]
                                  ->
                                  let uu____21293 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21293
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21298 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21316 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21316
                               then
                                 let uu____21319 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21319 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21377)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21378)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21452)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21453)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21527)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21528)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21602)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21603)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21677,(arg,uu____21679))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21680)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21753)::(uu____21754,(arg,uu____21756))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21829,(arg,uu____21831))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21832)::[]
                                     ->
                                     let uu____21905 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21905
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21906)::(uu____21907,(arg,uu____21909))::[]
                                     ->
                                     let uu____21982 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21982
                                 | (uu____21983,(p,uu____21985))::(uu____21986,
                                                                   (q,uu____21988))::[]
                                     ->
                                     let uu____22060 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22060
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22065 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22083 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22083
                                  then
                                    let uu____22086 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22086 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22144)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22188)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22232 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22250 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22250
                                     then
                                       match args with
                                       | (t,uu____22254)::[] ->
                                           let uu____22279 =
                                             let uu____22280 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22280.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22279 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22283::[],body,uu____22285)
                                                ->
                                                let uu____22320 = simp_t body
                                                   in
                                                (match uu____22320 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22326 -> tm1)
                                            | uu____22330 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22332))::(t,uu____22334)::[]
                                           ->
                                           let uu____22374 =
                                             let uu____22375 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22375.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22374 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22378::[],body,uu____22380)
                                                ->
                                                let uu____22415 = simp_t body
                                                   in
                                                (match uu____22415 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22423 -> tm1)
                                            | uu____22427 -> tm1)
                                       | uu____22428 -> tm1
                                     else
                                       (let uu____22441 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22441
                                        then
                                          match args with
                                          | (t,uu____22445)::[] ->
                                              let uu____22470 =
                                                let uu____22471 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22471.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22470 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22474::[],body,uu____22476)
                                                   ->
                                                   let uu____22511 =
                                                     simp_t body  in
                                                   (match uu____22511 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22517 -> tm1)
                                               | uu____22521 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22523))::(t,uu____22525)::[]
                                              ->
                                              let uu____22565 =
                                                let uu____22566 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22566.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22565 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22569::[],body,uu____22571)
                                                   ->
                                                   let uu____22606 =
                                                     simp_t body  in
                                                   (match uu____22606 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____22614 -> tm1)
                                               | uu____22618 -> tm1)
                                          | uu____22619 -> tm1
                                        else
                                          (let uu____22632 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22632
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22635;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22636;_},uu____22637)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22663;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22664;_},uu____22665)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22691 -> tm1
                                           else
                                             (let uu____22704 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____22704
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____22718 =
                                                    let uu____22719 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____22719.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____22718 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____22730 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____22744 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____22744
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____22779 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____22779
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____22785 =
                                                         let uu____22786 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____22786.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____22785 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____22789 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____22797 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____22797
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____22806
                                                                  =
                                                                  let uu____22807
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____22807.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____22806
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____22813)
                                                                    -> hd1
                                                                | uu____22838
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____22842
                                                                =
                                                                let uu____22853
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____22853]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____22842)
                                                       | uu____22886 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22891 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____22891 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22911 ->
                                                     let uu____22920 =
                                                       let uu____22927 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____22927 cfg env
                                                        in
                                                     uu____22920 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22938 = simp_t t  in
                      (match uu____22938 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22947 ->
                      let uu____22970 = is_const_match tm1  in
                      (match uu____22970 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22979 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____22989  ->
               (let uu____22991 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22993 = FStar_Syntax_Print.term_to_string t  in
                let uu____22995 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23003 =
                  let uu____23005 =
                    let uu____23008 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23008
                     in
                  stack_to_string uu____23005  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22991 uu____22993 uu____22995 uu____23003);
               (let uu____23033 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23033
                then
                  let uu____23037 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23037 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23044 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23046 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23048 =
                          let uu____23050 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23050
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23044
                          uu____23046 uu____23048);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____23072 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____23080)::uu____23081 -> true
                | uu____23091 -> false)
              in
           if uu____23072
           then
             let uu____23094 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____23094 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____23108 =
                        let uu____23110 =
                          let uu____23112 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____23112  in
                        FStar_Util.string_of_int uu____23110  in
                      let uu____23119 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____23121 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____23108 uu____23119 uu____23121)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____23130,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23159  ->
                        let uu____23160 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____23160);
                   rebuild cfg env stack1 t1)
              | (Let (env',bs,lb,r))::stack1 ->
                  let body = FStar_Syntax_Subst.close bs t1  in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env' stack1 t2
              | (Abs (env',bs,env'',lopt,r))::stack1 ->
                  let bs1 = norm_binders cfg env' bs  in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt  in
                  let uu____23203 =
                    let uu___2751_23204 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2751_23204.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2751_23204.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____23203
              | (Arg (Univ uu____23207,uu____23208,uu____23209))::uu____23210
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____23214,uu____23215))::uu____23216 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____23232,uu____23233),aq,r))::stack1
                  when
                  let uu____23285 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23285 ->
                  let t2 =
                    let uu____23289 =
                      let uu____23294 =
                        let uu____23295 = closure_as_term cfg env_arg tm  in
                        (uu____23295, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____23294  in
                    uu____23289 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____23305),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23360  ->
                        let uu____23361 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____23361);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                      then
                        let arg = closure_as_term cfg env_arg tm  in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env_arg stack1 t2
                      else
                        (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                         norm cfg env_arg stack2 tm))
                   else
                     (let uu____23381 = FStar_ST.op_Bang m  in
                      match uu____23381 with
                      | FStar_Pervasives_Native.None  ->
                          if
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          then
                            let arg = closure_as_term cfg env_arg tm  in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                                FStar_Pervasives_Native.None r
                               in
                            rebuild cfg env_arg stack1 t2
                          else
                            (let stack2 = (MemoLazy m) ::
                               (App (env, t1, aq, r)) :: stack1  in
                             norm cfg env_arg stack2 tm)
                      | FStar_Pervasives_Native.Some (uu____23469,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____23525 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____23530  ->
                         let uu____23531 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____23531);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____23541 =
                    let uu____23542 = FStar_Syntax_Subst.compress t1  in
                    uu____23542.FStar_Syntax_Syntax.n  in
                  (match uu____23541 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____23570 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____23570  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____23574  ->
                             let uu____23575 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____23575);
                        (let uu____23578 = FStar_List.tl stack  in
                         norm cfg env1 uu____23578 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____23579);
                          FStar_Syntax_Syntax.pos = uu____23580;
                          FStar_Syntax_Syntax.vars = uu____23581;_},(e,uu____23583)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____23622 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____23639 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____23639 with
                        | (hd1,args) ->
                            let uu____23682 =
                              let uu____23683 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____23683.FStar_Syntax_Syntax.n  in
                            (match uu____23682 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____23687 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____23687 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____23690;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____23691;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____23692;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____23694;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____23695;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____23696;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____23697;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____23733 -> fallback " (3)" ())
                             | uu____23737 -> fallback " (4)" ()))
                   | uu____23739 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____23765  ->
                        let uu____23766 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____23766);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____23777 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____23782  ->
                           let uu____23783 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____23785 =
                             let uu____23787 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____23817  ->
                                       match uu____23817 with
                                       | (p,uu____23828,uu____23829) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____23787
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____23783 uu____23785);
                      (let whnf =
                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                           ||
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          in
                       let cfg_exclude_zeta =
                         let new_delta =
                           FStar_All.pipe_right
                             cfg1.FStar_TypeChecker_Cfg.delta_level
                             (FStar_List.filter
                                (fun uu___17_23851  ->
                                   match uu___17_23851 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____23855 -> false))
                            in
                         let steps =
                           let uu___2919_23858 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2919_23858.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2922_23865 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2922_23865.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2922_23865.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2922_23865.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2922_23865.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2922_23865.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2922_23865.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____23940 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____23971 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____24060  ->
                                       fun uu____24061  ->
                                         match (uu____24060, uu____24061)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____24211 =
                                               norm_pat env3 p1  in
                                             (match uu____24211 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____23971 with
                              | (pats1,env3) ->
                                  ((let uu___2950_24381 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2950_24381.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2954_24402 = x  in
                               let uu____24403 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2954_24402.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2954_24402.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24403
                               }  in
                             ((let uu___2957_24417 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2957_24417.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___2961_24428 = x  in
                               let uu____24429 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2961_24428.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2961_24428.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24429
                               }  in
                             ((let uu___2964_24443 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2964_24443.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___2970_24459 = x  in
                               let uu____24460 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2970_24459.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2970_24459.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24460
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___2974_24475 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___2974_24475.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____24519 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____24549 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____24549 with
                                     | (p,wopt,e) ->
                                         let uu____24569 = norm_pat env1 p
                                            in
                                         (match uu____24569 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____24624 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____24624
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____24641 =
                           ((((cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                                &&
                                (Prims.op_Negation
                                   (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak))
                               &&
                               (Prims.op_Negation
                                  (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars))
                              &&
                              (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                             && (maybe_weakly_reduced scrutinee)
                            in
                         if uu____24641
                         then
                           norm
                             (let uu___2993_24648 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___2995_24651 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___2995_24651.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___2993_24648.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____24655 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____24655)
                       in
                    let rec is_cons head1 =
                      let uu____24681 =
                        let uu____24682 = FStar_Syntax_Subst.compress head1
                           in
                        uu____24682.FStar_Syntax_Syntax.n  in
                      match uu____24681 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____24687) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____24692 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24694;
                            FStar_Syntax_Syntax.fv_delta = uu____24695;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24697;
                            FStar_Syntax_Syntax.fv_delta = uu____24698;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____24699);_}
                          -> true
                      | uu____24707 -> false  in
                    let guard_when_clause wopt b rest =
                      match wopt with
                      | FStar_Pervasives_Native.None  -> b
                      | FStar_Pervasives_Native.Some w ->
                          let then_branch = b  in
                          let else_branch =
                            mk
                              (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                              r
                             in
                          FStar_Syntax_Util.if_then_else w then_branch
                            else_branch
                       in
                    let rec matches_pat scrutinee_orig p =
                      let scrutinee1 =
                        FStar_Syntax_Util.unmeta scrutinee_orig  in
                      let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1
                         in
                      let uu____24876 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____24876 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____24973 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____25015 ->
                                    let uu____25016 =
                                      let uu____25018 = is_cons head1  in
                                      Prims.op_Negation uu____25018  in
                                    FStar_Util.Inr uu____25016)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____25047 =
                                 let uu____25048 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____25048.FStar_Syntax_Syntax.n  in
                               (match uu____25047 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____25067 ->
                                    let uu____25068 =
                                      let uu____25070 = is_cons head1  in
                                      Prims.op_Negation uu____25070  in
                                    FStar_Util.Inr uu____25068))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____25161)::rest_a,(p1,uu____25164)::rest_p)
                          ->
                          let uu____25223 = matches_pat t2 p1  in
                          (match uu____25223 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____25276 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____25399 = matches_pat scrutinee1 p1  in
                          (match uu____25399 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____25445  ->
                                     let uu____25446 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____25448 =
                                       let uu____25450 =
                                         FStar_List.map
                                           (fun uu____25462  ->
                                              match uu____25462 with
                                              | (uu____25468,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____25450
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____25446 uu____25448);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____25504  ->
                                          match uu____25504 with
                                          | (bv,t2) ->
                                              let uu____25527 =
                                                let uu____25534 =
                                                  let uu____25537 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____25537
                                                   in
                                                let uu____25538 =
                                                  let uu____25539 =
                                                    let uu____25571 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____25571,
                                                      false)
                                                     in
                                                  Clos uu____25539  in
                                                (uu____25534, uu____25538)
                                                 in
                                              uu____25527 :: env2) env1 s
                                    in
                                 let uu____25664 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____25664)))
                       in
                    if
                      (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    then matches scrutinee branches
                    else norm_and_rebuild_match ()))))

let (normalize_with_primitive_steps :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = FStar_TypeChecker_Cfg.config' ps s e  in
          FStar_TypeChecker_Cfg.log_cfg c
            (fun uu____25697  ->
               let uu____25698 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____25698);
          (let uu____25701 = is_nbe_request s  in
           if uu____25701
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25707  ->
                   let uu____25708 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____25708);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25714  ->
                   let uu____25715 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25715);
              (let uu____25718 =
                 FStar_Util.record_time (fun uu____25725  -> nbe_eval c s t)
                  in
               match uu____25718 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25734  ->
                         let uu____25735 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____25737 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25735 uu____25737);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25745  ->
                   let uu____25746 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____25746);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25752  ->
                   let uu____25753 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25753);
              (let uu____25756 =
                 FStar_Util.record_time (fun uu____25763  -> norm c [] [] t)
                  in
               match uu____25756 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25778  ->
                         let uu____25779 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____25781 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25779 uu____25781);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____25816 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____25816 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25834 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____25834 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.UnfoldUntil
             FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
        let uu____25860 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25860  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25867 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3151_25886 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3151_25886.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3151_25886.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25893 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25893
          then
            let ct1 =
              let uu____25897 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25897 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____25904 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25904
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3161_25911 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3161_25911.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3161_25911.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3161_25911.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3165_25913 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3165_25913.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3165_25913.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3165_25913.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3165_25913.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3168_25914 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3168_25914.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3168_25914.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25917 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
        let uu____25937 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25937  in
      let uu____25944 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25944
      then
        let uu____25947 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25947 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25953  ->
                 let uu____25954 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25954)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3184_25971  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3183_25974 ->
            ((let uu____25976 =
                let uu____25982 =
                  let uu____25984 = FStar_Util.message_of_exn uu___3183_25974
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25984
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25982)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25976);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3194_26003  ->
             match () with
             | () ->
                 let uu____26004 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____26004 [] c) ()
        with
        | uu___3193_26013 ->
            ((let uu____26015 =
                let uu____26021 =
                  let uu____26023 = FStar_Util.message_of_exn uu___3193_26013
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26023
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26021)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26015);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env t0
           in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____26072 =
                     let uu____26073 =
                       let uu____26080 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26080)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26073  in
                   mk uu____26072 t01.FStar_Syntax_Syntax.pos
               | uu____26085 -> t2)
          | uu____26086 -> t2  in
        aux t
  
let (whnf_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Weak;
  FStar_TypeChecker_Env.HNF;
  FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
  FStar_TypeChecker_Env.Beta] 
let (unfold_whnf' :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  -> normalize (FStar_List.append steps whnf_steps) env t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> unfold_whnf' [] env t 
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append
             (if remove then [FStar_TypeChecker_Env.CheckNoUvars] else [])
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.DoNotUnfoldPureLets;
             FStar_TypeChecker_Env.CompressUvars;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Iota;
             FStar_TypeChecker_Env.NoFullNorm]) env t
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____26180 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26180 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26217 ->
                 let uu____26226 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26226 with
                  | (actuals,uu____26236,uu____26237) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26257 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26257 with
                         | (binders,args) ->
                             let uu____26268 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26268
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____26283 ->
          let uu____26284 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26284 with
           | (head1,args) ->
               let uu____26327 =
                 let uu____26328 = FStar_Syntax_Subst.compress head1  in
                 uu____26328.FStar_Syntax_Syntax.n  in
               (match uu____26327 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26349 =
                      let uu____26364 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26364  in
                    (match uu____26349 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26404 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3264_26412 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3264_26412.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3264_26412.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3264_26412.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3264_26412.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3264_26412.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3264_26412.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3264_26412.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3264_26412.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3264_26412.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3264_26412.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3264_26412.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3264_26412.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3264_26412.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3264_26412.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3264_26412.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3264_26412.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3264_26412.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3264_26412.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3264_26412.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3264_26412.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3264_26412.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3264_26412.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3264_26412.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3264_26412.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3264_26412.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3264_26412.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3264_26412.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3264_26412.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3264_26412.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3264_26412.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3264_26412.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3264_26412.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3264_26412.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3264_26412.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3264_26412.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3264_26412.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3264_26412.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3264_26412.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3264_26412.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3264_26412.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____26404 with
                            | (uu____26415,ty,uu____26417) ->
                                eta_expand_with_type env t ty))
                | uu____26418 ->
                    let uu____26419 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3271_26427 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3271_26427.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3271_26427.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3271_26427.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3271_26427.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3271_26427.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3271_26427.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3271_26427.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3271_26427.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3271_26427.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3271_26427.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3271_26427.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3271_26427.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3271_26427.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3271_26427.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3271_26427.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3271_26427.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3271_26427.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3271_26427.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3271_26427.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3271_26427.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3271_26427.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3271_26427.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3271_26427.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3271_26427.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3271_26427.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3271_26427.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3271_26427.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3271_26427.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3271_26427.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3271_26427.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3271_26427.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3271_26427.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3271_26427.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3271_26427.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3271_26427.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3271_26427.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3271_26427.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3271_26427.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3271_26427.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3271_26427.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____26419 with
                     | (uu____26430,ty,uu____26432) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___3283_26514 = x  in
      let uu____26515 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3283_26514.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3283_26514.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26515
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26518 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26542 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26543 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26544 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26545 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26552 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26553 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26554 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3309_26588 = rc  in
          let uu____26589 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26598 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3309_26588.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26589;
            FStar_Syntax_Syntax.residual_flags = uu____26598
          }  in
        let uu____26601 =
          let uu____26602 =
            let uu____26621 = elim_delayed_subst_binders bs  in
            let uu____26630 = elim_delayed_subst_term t2  in
            let uu____26633 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26621, uu____26630, uu____26633)  in
          FStar_Syntax_Syntax.Tm_abs uu____26602  in
        mk1 uu____26601
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26670 =
          let uu____26671 =
            let uu____26686 = elim_delayed_subst_binders bs  in
            let uu____26695 = elim_delayed_subst_comp c  in
            (uu____26686, uu____26695)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26671  in
        mk1 uu____26670
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26714 =
          let uu____26715 =
            let uu____26722 = elim_bv bv  in
            let uu____26723 = elim_delayed_subst_term phi  in
            (uu____26722, uu____26723)  in
          FStar_Syntax_Syntax.Tm_refine uu____26715  in
        mk1 uu____26714
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26754 =
          let uu____26755 =
            let uu____26772 = elim_delayed_subst_term t2  in
            let uu____26775 = elim_delayed_subst_args args  in
            (uu____26772, uu____26775)  in
          FStar_Syntax_Syntax.Tm_app uu____26755  in
        mk1 uu____26754
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3331_26847 = p  in
              let uu____26848 =
                let uu____26849 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26849  in
              {
                FStar_Syntax_Syntax.v = uu____26848;
                FStar_Syntax_Syntax.p =
                  (uu___3331_26847.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3335_26851 = p  in
              let uu____26852 =
                let uu____26853 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26853  in
              {
                FStar_Syntax_Syntax.v = uu____26852;
                FStar_Syntax_Syntax.p =
                  (uu___3335_26851.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3341_26860 = p  in
              let uu____26861 =
                let uu____26862 =
                  let uu____26869 = elim_bv x  in
                  let uu____26870 = elim_delayed_subst_term t0  in
                  (uu____26869, uu____26870)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26862  in
              {
                FStar_Syntax_Syntax.v = uu____26861;
                FStar_Syntax_Syntax.p =
                  (uu___3341_26860.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3347_26895 = p  in
              let uu____26896 =
                let uu____26897 =
                  let uu____26911 =
                    FStar_List.map
                      (fun uu____26937  ->
                         match uu____26937 with
                         | (x,b) ->
                             let uu____26954 = elim_pat x  in
                             (uu____26954, b)) pats
                     in
                  (fv, uu____26911)  in
                FStar_Syntax_Syntax.Pat_cons uu____26897  in
              {
                FStar_Syntax_Syntax.v = uu____26896;
                FStar_Syntax_Syntax.p =
                  (uu___3347_26895.FStar_Syntax_Syntax.p)
              }
          | uu____26969 -> p  in
        let elim_branch uu____26993 =
          match uu____26993 with
          | (pat,wopt,t3) ->
              let uu____27019 = elim_pat pat  in
              let uu____27022 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27025 = elim_delayed_subst_term t3  in
              (uu____27019, uu____27022, uu____27025)
           in
        let uu____27030 =
          let uu____27031 =
            let uu____27054 = elim_delayed_subst_term t2  in
            let uu____27057 = FStar_List.map elim_branch branches  in
            (uu____27054, uu____27057)  in
          FStar_Syntax_Syntax.Tm_match uu____27031  in
        mk1 uu____27030
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____27188 =
          match uu____27188 with
          | (tc,topt) ->
              let uu____27223 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27233 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27233
                | FStar_Util.Inr c ->
                    let uu____27235 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27235
                 in
              let uu____27236 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27223, uu____27236)
           in
        let uu____27245 =
          let uu____27246 =
            let uu____27273 = elim_delayed_subst_term t2  in
            let uu____27276 = elim_ascription a  in
            (uu____27273, uu____27276, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27246  in
        mk1 uu____27245
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3377_27339 = lb  in
          let uu____27340 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27343 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3377_27339.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3377_27339.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27340;
            FStar_Syntax_Syntax.lbeff =
              (uu___3377_27339.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27343;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3377_27339.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3377_27339.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27346 =
          let uu____27347 =
            let uu____27361 =
              let uu____27369 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27369)  in
            let uu____27381 = elim_delayed_subst_term t2  in
            (uu____27361, uu____27381)  in
          FStar_Syntax_Syntax.Tm_let uu____27347  in
        mk1 uu____27346
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27426 =
          let uu____27427 =
            let uu____27434 = elim_delayed_subst_term tm  in
            (uu____27434, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27427  in
        mk1 uu____27426
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27445 =
          let uu____27446 =
            let uu____27453 = elim_delayed_subst_term t2  in
            let uu____27456 = elim_delayed_subst_meta md  in
            (uu____27453, uu____27456)  in
          FStar_Syntax_Syntax.Tm_meta uu____27446  in
        mk1 uu____27445

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___18_27465  ->
         match uu___18_27465 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27469 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27469
         | f -> f) flags

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____27492 =
          let uu____27493 =
            let uu____27502 = elim_delayed_subst_term t  in
            (uu____27502, uopt)  in
          FStar_Syntax_Syntax.Total uu____27493  in
        mk1 uu____27492
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27519 =
          let uu____27520 =
            let uu____27529 = elim_delayed_subst_term t  in
            (uu____27529, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27520  in
        mk1 uu____27519
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3410_27538 = ct  in
          let uu____27539 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27542 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27553 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3410_27538.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3410_27538.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27539;
            FStar_Syntax_Syntax.effect_args = uu____27542;
            FStar_Syntax_Syntax.flags = uu____27553
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___19_27556  ->
    match uu___19_27556 with
    | FStar_Syntax_Syntax.Meta_pattern (attr,names1,args) ->
        let uu____27596 =
          let uu____27621 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____27630 = FStar_List.map elim_delayed_subst_args args  in
          (attr, uu____27621, uu____27630)  in
        FStar_Syntax_Syntax.Meta_pattern uu____27596
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27687 =
          let uu____27694 = elim_delayed_subst_term t  in (m, uu____27694)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27687
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27706 =
          let uu____27715 = elim_delayed_subst_term t  in
          (m1, m2, uu____27715)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27706
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27748  ->
         match uu____27748 with
         | (t,q) ->
             let uu____27767 = elim_delayed_subst_term t  in (uu____27767, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27795  ->
         match uu____27795 with
         | (x,q) ->
             let uu____27814 =
               let uu___3437_27815 = x  in
               let uu____27816 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3437_27815.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3437_27815.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27816
               }  in
             (uu____27814, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list *
            (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                                    FStar_Syntax_Syntax.syntax)
            FStar_Util.either))
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____27924,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27956,FStar_Util.Inl t) ->
                let uu____27978 =
                  let uu____27985 =
                    let uu____27986 =
                      let uu____28001 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____28001)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27986  in
                  FStar_Syntax_Syntax.mk uu____27985  in
                uu____27978 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____28014 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____28014 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____28046 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____28119 ->
                    let uu____28120 =
                      let uu____28129 =
                        let uu____28130 = FStar_Syntax_Subst.compress t4  in
                        uu____28130.FStar_Syntax_Syntax.n  in
                      (uu____28129, tc)  in
                    (match uu____28120 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____28159) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____28206) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____28251,FStar_Util.Inl uu____28252) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____28283 -> failwith "Impossible")
                 in
              (match uu____28046 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list * FStar_Syntax_Syntax.term'
            FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____28422 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28422 with
          | (univ_names1,binders1,tc) ->
              let uu____28496 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28496)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list * FStar_Syntax_Syntax.comp'
            FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____28550 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28550 with
          | (univ_names1,binders1,tc) ->
              let uu____28624 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28624)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28666 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28666 with
           | (univ_names1,binders1,typ1) ->
               let uu___3520_28706 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3520_28706.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3520_28706.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3520_28706.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3520_28706.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3526_28721 = s  in
          let uu____28722 =
            let uu____28723 =
              let uu____28732 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28732, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28723  in
          {
            FStar_Syntax_Syntax.sigel = uu____28722;
            FStar_Syntax_Syntax.sigrng =
              (uu___3526_28721.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3526_28721.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3526_28721.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3526_28721.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28751 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28751 with
           | (univ_names1,uu____28775,typ1) ->
               let uu___3540_28797 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3540_28797.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3540_28797.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3540_28797.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3540_28797.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28804 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28804 with
           | (univ_names1,uu____28828,typ1) ->
               let uu___3551_28850 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3551_28850.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3551_28850.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3551_28850.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3551_28850.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28880 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28880 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28905 =
                            let uu____28906 =
                              let uu____28907 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28907  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28906
                             in
                          elim_delayed_subst_term uu____28905  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3567_28910 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3567_28910.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3567_28910.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3567_28910.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3567_28910.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3570_28911 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3570_28911.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3570_28911.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3570_28911.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3570_28911.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3574_28918 = s  in
          let uu____28919 =
            let uu____28920 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28920  in
          {
            FStar_Syntax_Syntax.sigel = uu____28919;
            FStar_Syntax_Syntax.sigrng =
              (uu___3574_28918.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3574_28918.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3574_28918.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3574_28918.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28924 = elim_uvars_aux_t env us [] t  in
          (match uu____28924 with
           | (us1,uu____28948,t1) ->
               let uu___3585_28970 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3585_28970.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3585_28970.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3585_28970.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3585_28970.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28971 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28974 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28974 with
           | (univs1,binders,signature) ->
               let uu____29014 =
                 let uu____29019 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____29019 with
                 | (univs_opening,univs2) ->
                     let uu____29042 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____29042)
                  in
               (match uu____29014 with
                | (univs_opening,univs_closing) ->
                    let uu____29045 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____29051 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____29052 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____29051, uu____29052)  in
                    (match uu____29045 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____29078 =
                           match uu____29078 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____29096 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____29096 with
                                | (us1,t1) ->
                                    let uu____29107 =
                                      let uu____29116 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____29121 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____29116, uu____29121)  in
                                    (match uu____29107 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____29144 =
                                           let uu____29153 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____29158 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____29153, uu____29158)  in
                                         (match uu____29144 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____29182 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____29182
                                                 in
                                              let uu____29183 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____29183 with
                                               | (uu____29210,uu____29211,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____29234 =
                                                       let uu____29235 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____29235
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____29234
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____29244 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____29244 with
                           | (uu____29263,uu____29264,t1) -> t1  in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____29340 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____29367 =
                               let uu____29368 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____29368.FStar_Syntax_Syntax.n  in
                             match uu____29367 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____29427 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29461 =
                               let uu____29462 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29462.FStar_Syntax_Syntax.n  in
                             match uu____29461 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29485) ->
                                 let uu____29510 = destruct_action_body body
                                    in
                                 (match uu____29510 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____29559 ->
                                 let uu____29560 = destruct_action_body t  in
                                 (match uu____29560 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29615 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____29615 with
                           | (action_univs,t) ->
                               let uu____29624 = destruct_action_typ_templ t
                                  in
                               (match uu____29624 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3671_29671 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3671_29671.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3671_29671.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___3674_29673 = ed  in
                           let uu____29674 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29675 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29676 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29677 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29678 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29679 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29680 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____29681 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____29682 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____29683 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29684 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____29685 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29686 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29687 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3674_29673.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3674_29673.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____29674;
                             FStar_Syntax_Syntax.bind_wp = uu____29675;
                             FStar_Syntax_Syntax.if_then_else = uu____29676;
                             FStar_Syntax_Syntax.ite_wp = uu____29677;
                             FStar_Syntax_Syntax.stronger = uu____29678;
                             FStar_Syntax_Syntax.close_wp = uu____29679;
                             FStar_Syntax_Syntax.assert_p = uu____29680;
                             FStar_Syntax_Syntax.assume_p = uu____29681;
                             FStar_Syntax_Syntax.null_wp = uu____29682;
                             FStar_Syntax_Syntax.trivial = uu____29683;
                             FStar_Syntax_Syntax.repr = uu____29684;
                             FStar_Syntax_Syntax.return_repr = uu____29685;
                             FStar_Syntax_Syntax.bind_repr = uu____29686;
                             FStar_Syntax_Syntax.actions = uu____29687;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3674_29673.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3677_29690 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3677_29690.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3677_29690.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3677_29690.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3677_29690.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___20_29711 =
            match uu___20_29711 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29742 = elim_uvars_aux_t env us [] t  in
                (match uu____29742 with
                 | (us1,uu____29774,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3692_29805 = sub_eff  in
            let uu____29806 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29809 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3692_29805.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3692_29805.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29806;
              FStar_Syntax_Syntax.lift = uu____29809
            }  in
          let uu___3695_29812 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3695_29812.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3695_29812.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3695_29812.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3695_29812.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____29822 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29822 with
           | (univ_names1,binders1,comp1) ->
               let uu___3708_29862 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3708_29862.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3708_29862.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3708_29862.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3708_29862.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29865 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29866 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  
let (unfold_head_once :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let aux f us args =
        let uu____29915 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____29915 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____29937 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____29937 with
             | (uu____29944,head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                    in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env t'
                    in
                 FStar_Pervasives_Native.Some t'1)
         in
      let uu____29950 = FStar_Syntax_Util.head_and_args t  in
      match uu____29950 with
      | (head1,args) ->
          let uu____29995 =
            let uu____29996 = FStar_Syntax_Subst.compress head1  in
            uu____29996.FStar_Syntax_Syntax.n  in
          (match uu____29995 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____30003;
                  FStar_Syntax_Syntax.vars = uu____30004;_},us)
               -> aux fv us args
           | uu____30010 -> FStar_Pervasives_Native.None)
  