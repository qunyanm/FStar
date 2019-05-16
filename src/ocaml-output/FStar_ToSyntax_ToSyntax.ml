open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____103  ->
                match uu____103 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____158  ->
                             match uu____158 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____176 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____176 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____183]  in
                                   FStar_Syntax_Subst.close uu____182 branch1
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___0_240  ->
        match uu___0_240 with
        | FStar_Parser_AST.Private  -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption  -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen  ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction  ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract  -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible  -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic  -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual  -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New  -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract  -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque  ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
  
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___1_260  ->
    match uu___1_260 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___2_278  ->
    match uu___2_278 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____281 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____289 .
    FStar_Parser_AST.imp ->
      'Auu____289 ->
        ('Auu____289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____315 .
    FStar_Parser_AST.imp ->
      'Auu____315 ->
        ('Auu____315 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____334 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____355 -> true
            | uu____361 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____370 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____377 =
      let uu____378 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____378  in
    FStar_Parser_AST.mk_term uu____377 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____388 =
      let uu____389 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____389  in
    FStar_Parser_AST.mk_term uu____388 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____405 =
        let uu____406 = unparen t  in uu____406.FStar_Parser_AST.tm  in
      match uu____405 with
      | FStar_Parser_AST.Name l ->
          let uu____409 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____409 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____416) ->
          let uu____429 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____429 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____436,uu____437) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____442,uu____443) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____448,t1) -> is_comp_type env t1
      | uu____450 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (desugar_name' :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env_t ->
      Prims.bool ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun setpos  ->
    fun env  ->
      fun resolve  ->
        fun l  ->
          let tm_attrs_opt =
            if resolve
            then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes env l
            else
              FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
                env l
             in
          match tm_attrs_opt with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (tm,attrs) ->
              let warn_if_deprecated attrs1 =
                FStar_List.iter
                  (fun a  ->
                     match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____551;
                            FStar_Syntax_Syntax.vars = uu____552;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____580 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____580 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____596 =
                               let uu____597 =
                                 let uu____600 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____600  in
                               uu____597.FStar_Syntax_Syntax.n  in
                             match uu____596 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____623))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____630 -> msg
                           else msg  in
                         let uu____633 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____633
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____638 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____638 " is deprecated"  in
                         let uu____641 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____641
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____643 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____659 .
    'Auu____659 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____712 =
          let uu____715 =
            let uu____716 =
              let uu____722 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____722, r)  in
            FStar_Ident.mk_ident uu____716  in
          [uu____715]  in
        FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____738 .
    env_t ->
      Prims.int ->
        'Auu____738 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____776 =
              let uu____777 =
                let uu____778 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____778 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____777 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____776  in
          let fallback uu____786 =
            let uu____787 = FStar_Ident.text_of_id op  in
            match uu____787 with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.delta_equational
            | "@" ->
                let uu____808 = FStar_Options.ml_ish ()  in
                if uu____808
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | uu____833 -> FStar_Pervasives_Native.None  in
          let uu____835 =
            let uu____838 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___205_844 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___205_844.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___205_844.FStar_Syntax_Syntax.vars)
                 }) env true uu____838
             in
          match uu____835 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____849 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____864 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____864
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____913 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____917 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____917 with | (env1,uu____929) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____932,term) ->
          let uu____934 = free_type_vars env term  in (env, uu____934)
      | FStar_Parser_AST.TAnnotated (id1,uu____940) ->
          let uu____941 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____941 with | (env1,uu____953) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____957 = free_type_vars env t  in (env, uu____957)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____964 =
        let uu____965 = unparen t  in uu____965.FStar_Parser_AST.tm  in
      match uu____964 with
      | FStar_Parser_AST.Labeled uu____968 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____981 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____981 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____986 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____989 -> []
      | FStar_Parser_AST.Uvar uu____990 -> []
      | FStar_Parser_AST.Var uu____991 -> []
      | FStar_Parser_AST.Projector uu____992 -> []
      | FStar_Parser_AST.Discrim uu____997 -> []
      | FStar_Parser_AST.Name uu____998 -> []
      | FStar_Parser_AST.Requires (t1,uu____1000) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1008) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1015,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1034,ts) ->
          FStar_List.collect
            (fun uu____1055  ->
               match uu____1055 with
               | (t1,uu____1063) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1064,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1072) ->
          let uu____1073 = free_type_vars env t1  in
          let uu____1076 = free_type_vars env t2  in
          FStar_List.append uu____1073 uu____1076
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1081 = free_type_vars_b env b  in
          (match uu____1081 with
           | (env1,f) ->
               let uu____1096 = free_type_vars env1 t1  in
               FStar_List.append f uu____1096)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1113 =
            FStar_List.fold_left
              (fun uu____1137  ->
                 fun bt  ->
                   match uu____1137 with
                   | (env1,free) ->
                       let uu____1161 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1176 = free_type_vars env1 body  in
                             (env1, uu____1176)
                          in
                       (match uu____1161 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1113 with
           | (env1,free) ->
               let uu____1205 = free_type_vars env1 body  in
               FStar_List.append free uu____1205)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1214 =
            FStar_List.fold_left
              (fun uu____1234  ->
                 fun binder  ->
                   match uu____1234 with
                   | (env1,free) ->
                       let uu____1254 = free_type_vars_b env1 binder  in
                       (match uu____1254 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1214 with
           | (env1,free) ->
               let uu____1285 = free_type_vars env1 body  in
               FStar_List.append free uu____1285)
      | FStar_Parser_AST.Project (t1,uu____1289) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1300 = free_type_vars env rel  in
          let uu____1303 =
            let uu____1306 = free_type_vars env init1  in
            let uu____1309 =
              FStar_List.collect
                (fun uu____1318  ->
                   match uu____1318 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1324 = free_type_vars env rel1  in
                       let uu____1327 =
                         let uu____1330 = free_type_vars env just  in
                         let uu____1333 = free_type_vars env next  in
                         FStar_List.append uu____1330 uu____1333  in
                       FStar_List.append uu____1324 uu____1327) steps
               in
            FStar_List.append uu____1306 uu____1309  in
          FStar_List.append uu____1300 uu____1303
      | FStar_Parser_AST.Abs uu____1336 -> []
      | FStar_Parser_AST.Let uu____1343 -> []
      | FStar_Parser_AST.LetOpen uu____1364 -> []
      | FStar_Parser_AST.If uu____1369 -> []
      | FStar_Parser_AST.QForall uu____1376 -> []
      | FStar_Parser_AST.QExists uu____1399 -> []
      | FStar_Parser_AST.Record uu____1422 -> []
      | FStar_Parser_AST.Match uu____1435 -> []
      | FStar_Parser_AST.TryWith uu____1450 -> []
      | FStar_Parser_AST.Bind uu____1465 -> []
      | FStar_Parser_AST.Quote uu____1472 -> []
      | FStar_Parser_AST.VQuote uu____1477 -> []
      | FStar_Parser_AST.Antiquote uu____1478 -> []
      | FStar_Parser_AST.Seq uu____1479 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1533 =
        let uu____1534 = unparen t1  in uu____1534.FStar_Parser_AST.tm  in
      match uu____1533 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1576 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1601 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1601  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1623 =
                     let uu____1624 =
                       let uu____1629 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1629)  in
                     FStar_Parser_AST.TAnnotated uu____1624  in
                   FStar_Parser_AST.mk_binder uu____1623
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1647 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1647  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1669 =
                     let uu____1670 =
                       let uu____1675 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1675)  in
                     FStar_Parser_AST.TAnnotated uu____1670  in
                   FStar_Parser_AST.mk_binder uu____1669
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1677 =
             let uu____1678 = unparen t  in uu____1678.FStar_Parser_AST.tm
              in
           match uu____1677 with
           | FStar_Parser_AST.Product uu____1679 -> t
           | uu____1686 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
            in
         result)
  
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1723 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1734 -> true
    | FStar_Parser_AST.PatTvar (uu____1738,uu____1739) -> true
    | FStar_Parser_AST.PatVar (uu____1745,uu____1746) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1753) -> is_var_pattern p1
    | uu____1766 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1777) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1790;
           FStar_Parser_AST.prange = uu____1791;_},uu____1792)
        -> true
    | uu____1804 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1820 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1893 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1893 with
             | (name,args,uu____1936) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1986);
               FStar_Parser_AST.prange = uu____1987;_},args)
            when is_top_level1 ->
            let uu____1997 =
              let uu____2002 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____2002  in
            (uu____1997, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2024);
               FStar_Parser_AST.prange = uu____2025;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2055 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  Prims.bool ->
    FStar_Ident.ident FStar_Util.set ->
      FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun acc  ->
      fun p  ->
        let gather_pattern_bound_vars_from_list =
          FStar_List.fold_left
            (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc
           in
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatWild uu____2114 -> acc
        | FStar_Parser_AST.PatName uu____2117 -> acc
        | FStar_Parser_AST.PatOp uu____2118 -> acc
        | FStar_Parser_AST.PatConst uu____2119 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____2136) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____2142) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____2151) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2168 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____2168
        | FStar_Parser_AST.PatAscribed (pat,uu____2176) ->
            gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat
  
let (gather_pattern_bound_vars :
  Prims.bool -> FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun p  ->
      let acc =
        FStar_Util.new_set
          (fun id1  ->
             fun id2  ->
               if id1.FStar_Ident.idText = id2.FStar_Ident.idText
               then (Prims.parse_int "0")
               else (Prims.parse_int "1"))
         in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
  
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2258 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2299 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2347  ->
    match uu___3_2347 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2354 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2387  ->
    match uu____2387 with
    | (attrs,n1,t,e,pos) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs;
          FStar_Syntax_Syntax.lbpos = pos
        }
  
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2469 =
        let uu____2486 =
          let uu____2489 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2489  in
        let uu____2490 =
          let uu____2501 =
            let uu____2510 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2510)  in
          [uu____2501]  in
        (uu____2486, uu____2490)  in
      FStar_Syntax_Syntax.Tm_app uu____2469  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2559 =
        let uu____2576 =
          let uu____2579 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2579  in
        let uu____2580 =
          let uu____2591 =
            let uu____2600 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2600)  in
          [uu____2591]  in
        (uu____2576, uu____2580)  in
      FStar_Syntax_Syntax.Tm_app uu____2559  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____2663 =
            let uu____2680 =
              let uu____2683 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2683  in
            let uu____2684 =
              let uu____2695 =
                let uu____2704 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2704)  in
              let uu____2712 =
                let uu____2723 =
                  let uu____2732 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2732)  in
                [uu____2723]  in
              uu____2695 :: uu____2712  in
            (uu____2680, uu____2684)  in
          FStar_Syntax_Syntax.Tm_app uu____2663  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2792 =
        let uu____2807 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2826  ->
               match uu____2826 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2837;
                    FStar_Syntax_Syntax.index = uu____2838;
                    FStar_Syntax_Syntax.sort = t;_},uu____2840)
                   ->
                   let uu____2848 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2848) uu____2807
         in
      FStar_All.pipe_right bs uu____2792  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2864 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2882 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2910 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2931,uu____2932,bs,t,uu____2935,uu____2936)
                            ->
                            let uu____2945 = bs_univnames bs  in
                            let uu____2948 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2945 uu____2948
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2951,uu____2952,t,uu____2954,uu____2955,uu____2956)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2963 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2910 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___587_2972 = s  in
        let uu____2973 =
          let uu____2974 =
            let uu____2983 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____3001,bs,t,lids1,lids2) ->
                          let uu___598_3014 = se  in
                          let uu____3015 =
                            let uu____3016 =
                              let uu____3033 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3034 =
                                let uu____3035 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3035 t  in
                              (lid, uvs, uu____3033, uu____3034, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3016
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3015;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___598_3014.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___598_3014.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___598_3014.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___598_3014.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3049,t,tlid,n1,lids1) ->
                          let uu___608_3060 = se  in
                          let uu____3061 =
                            let uu____3062 =
                              let uu____3078 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3078, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3062  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3061;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___608_3060.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___608_3060.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___608_3060.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___608_3060.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____3082 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2983, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2974  in
        {
          FStar_Syntax_Syntax.sigel = uu____2973;
          FStar_Syntax_Syntax.sigrng =
            (uu___587_2972.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___587_2972.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___587_2972.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___587_2972.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3089,t) ->
        let uvs =
          let uu____3092 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3092 FStar_Util.set_elements  in
        let uu___617_3097 = s  in
        let uu____3098 =
          let uu____3099 =
            let uu____3106 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3106)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3099  in
        {
          FStar_Syntax_Syntax.sigel = uu____3098;
          FStar_Syntax_Syntax.sigrng =
            (uu___617_3097.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___617_3097.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___617_3097.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___617_3097.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3130 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3133 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3140) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3173,(FStar_Util.Inl t,uu____3175),uu____3176)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3223,(FStar_Util.Inr c,uu____3225),uu____3226)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3273 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3274,(FStar_Util.Inl t,uu____3276),uu____3277) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3324,(FStar_Util.Inr c,uu____3326),uu____3327) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3374 -> empty_set  in
          FStar_Util.set_union uu____3130 uu____3133  in
        let all_lb_univs =
          let uu____3378 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3394 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3394) empty_set)
             in
          FStar_All.pipe_right uu____3378 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___672_3404 = s  in
        let uu____3405 =
          let uu____3406 =
            let uu____3413 =
              let uu____3414 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___675_3426 = lb  in
                        let uu____3427 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3430 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___675_3426.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3427;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___675_3426.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3430;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___675_3426.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___675_3426.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3414)  in
            (uu____3413, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3406  in
        {
          FStar_Syntax_Syntax.sigel = uu____3405;
          FStar_Syntax_Syntax.sigrng =
            (uu___672_3404.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___672_3404.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___672_3404.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___672_3404.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3439,fml) ->
        let uvs =
          let uu____3442 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3442 FStar_Util.set_elements  in
        let uu___683_3447 = s  in
        let uu____3448 =
          let uu____3449 =
            let uu____3456 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3456)  in
          FStar_Syntax_Syntax.Sig_assume uu____3449  in
        {
          FStar_Syntax_Syntax.sigel = uu____3448;
          FStar_Syntax_Syntax.sigrng =
            (uu___683_3447.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___683_3447.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___683_3447.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___683_3447.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3458,bs,c,flags) ->
        let uvs =
          let uu____3467 =
            let uu____3470 = bs_univnames bs  in
            let uu____3473 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3470 uu____3473  in
          FStar_All.pipe_right uu____3467 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___694_3481 = s  in
        let uu____3482 =
          let uu____3483 =
            let uu____3496 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3497 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3496, uu____3497, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3483  in
        {
          FStar_Syntax_Syntax.sigel = uu____3482;
          FStar_Syntax_Syntax.sigrng =
            (uu___694_3481.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___694_3481.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___694_3481.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___694_3481.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3500 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3508  ->
    match uu___4_3508 with
    | "lift1" -> true
    | "lift2" -> true
    | "pure" -> true
    | "app" -> true
    | "push" -> true
    | "wp_if_then_else" -> true
    | "wp_assert" -> true
    | "wp_assume" -> true
    | "wp_close" -> true
    | "stronger" -> true
    | "ite_wp" -> true
    | "null_wp" -> true
    | "wp_trivial" -> true
    | "ctx" -> true
    | "gctx" -> true
    | "lift_from_pure" -> true
    | "return_wp" -> true
    | "return_elab" -> true
    | "bind_wp" -> true
    | "bind_elab" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3559 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3580 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3580)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3606 =
      let uu____3607 = unparen t  in uu____3607.FStar_Parser_AST.tm  in
    match uu____3606 with
    | FStar_Parser_AST.Wild  ->
        let uu____3613 =
          let uu____3614 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3614  in
        FStar_Util.Inr uu____3613
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3627)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____3718 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3718
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3735 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3735
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3751 =
               let uu____3757 =
                 let uu____3759 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3759
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3757)
                in
             FStar_Errors.raise_error uu____3751 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3768 ->
        let rec aux t1 univargs =
          let uu____3805 =
            let uu____3806 = unparen t1  in uu____3806.FStar_Parser_AST.tm
             in
          match uu____3805 with
          | FStar_Parser_AST.App (t2,targ,uu____3814) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3841  ->
                     match uu___5_3841 with
                     | FStar_Util.Inr uu____3848 -> true
                     | uu____3851 -> false) univargs
              then
                let uu____3859 =
                  let uu____3860 =
                    FStar_List.map
                      (fun uu___6_3870  ->
                         match uu___6_3870 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3860  in
                FStar_Util.Inr uu____3859
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3896  ->
                        match uu___7_3896 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3906 -> failwith "impossible")
                     univargs
                    in
                 let uu____3910 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3910)
          | uu____3926 ->
              let uu____3927 =
                let uu____3933 =
                  let uu____3935 =
                    let uu____3937 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3937 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3935  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3933)  in
              FStar_Errors.raise_error uu____3927 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3952 ->
        let uu____3953 =
          let uu____3959 =
            let uu____3961 =
              let uu____3963 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3963 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3961  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3959)  in
        FStar_Errors.raise_error uu____3953 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,{
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
              (e,{
                   FStar_Syntax_Syntax.qkind =
                     FStar_Syntax_Syntax.Quote_dynamic ;
                   FStar_Syntax_Syntax.antiquotes = uu____4004;_});
            FStar_Syntax_Syntax.pos = uu____4005;
            FStar_Syntax_Syntax.vars = uu____4006;_})::uu____4007
        ->
        let uu____4038 =
          let uu____4044 =
            let uu____4046 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4046
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4044)  in
        FStar_Errors.raise_error uu____4038 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4052 ->
        let uu____4071 =
          let uu____4077 =
            let uu____4079 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4079
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4077)  in
        FStar_Errors.raise_error uu____4071 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4092 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4092) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4120 = FStar_List.hd fields  in
        match uu____4120 with
        | (f,uu____4130) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4142 =
                match uu____4142 with
                | (f',uu____4148) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4150 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4150
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____4160 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4160);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env  ->
    fun p  ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____4523 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4530 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4531 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4533,pats1) ->
              let aux out uu____4574 =
                match uu____4574 with
                | (p2,uu____4587) ->
                    let intersection =
                      let uu____4597 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4597 out  in
                    let uu____4600 = FStar_Util.set_is_empty intersection  in
                    if uu____4600
                    then
                      let uu____4605 = pat_vars p2  in
                      FStar_Util.set_union out uu____4605
                    else
                      (let duplicate_bv =
                         let uu____4611 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4611  in
                       let uu____4614 =
                         let uu____4620 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4620)
                          in
                       FStar_Errors.raise_error uu____4614 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4644 = pat_vars p1  in
            FStar_All.pipe_right uu____4644 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4672 =
                let uu____4674 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4674  in
              if uu____4672
              then ()
              else
                (let nonlinear_vars =
                   let uu____4683 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4683  in
                 let first_nonlinear_var =
                   let uu____4687 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4687  in
                 let uu____4690 =
                   let uu____4696 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4696)  in
                 FStar_Errors.raise_error uu____4690 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4724 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4724 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4741 ->
            let uu____4744 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4744 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4895 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4919 =
              let uu____4920 =
                let uu____4921 =
                  let uu____4928 =
                    let uu____4929 =
                      let uu____4935 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4935, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4929  in
                  (uu____4928, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4921  in
              {
                FStar_Parser_AST.pat = uu____4920;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4919
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4955 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4958 = aux loc env1 p2  in
              match uu____4958 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___932_5047 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___934_5052 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___934_5052.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___934_5052.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___932_5047.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___938_5054 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___940_5059 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___940_5059.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___940_5059.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___938_5054.FStar_Syntax_Syntax.p)
                        }
                    | uu____5060 when top -> p4
                    | uu____5061 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5066 =
                    match binder with
                    | LetBinder uu____5087 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5112 = close_fun env1 t  in
                          desugar_term env1 uu____5112  in
                        let x1 =
                          let uu___951_5114 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___951_5114.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___951_5114.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5066 with
                   | (annots',binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots), imp))))
        | FStar_Parser_AST.PatWild aq ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5182 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5182, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5196 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5196, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5220 = resolvex loc env1 x  in
            (match uu____5220 with
             | (loc1,env2,xbv) ->
                 let uu____5249 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5249, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5272 = resolvex loc env1 x  in
            (match uu____5272 with
             | (loc1,env2,xbv) ->
                 let uu____5301 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5301, [], imp))
        | FStar_Parser_AST.PatName l ->
            let l1 =
              FStar_Syntax_DsEnv.fail_or env1
                (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
               in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5316 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5316, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5346;_},args)
            ->
            let uu____5352 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5413  ->
                     match uu____5413 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5494 = aux loc1 env2 arg  in
                         (match uu____5494 with
                          | (loc2,env3,uu____5541,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5352 with
             | (loc1,env2,annots,args1) ->
                 let l1 =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____5673 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5673, annots, false))
        | FStar_Parser_AST.PatApp uu____5691 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5722 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5773  ->
                     match uu____5773 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5834 = aux loc1 env2 pat  in
                         (match uu____5834 with
                          | (loc2,env3,uu____5876,pat1,ans,uu____5879) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5722 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5976 =
                     let uu____5979 =
                       let uu____5986 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5986  in
                     let uu____5987 =
                       let uu____5988 =
                         let uu____6002 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____6002, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5988  in
                     FStar_All.pipe_left uu____5979 uu____5987  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6036 =
                            let uu____6037 =
                              let uu____6051 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6051, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6037  in
                          FStar_All.pipe_left (pos_r r) uu____6036) pats1
                     uu____5976
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots, false))
        | FStar_Parser_AST.PatTuple (args,dep1) ->
            let uu____6109 =
              FStar_List.fold_left
                (fun uu____6169  ->
                   fun p2  ->
                     match uu____6169 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6251 = aux loc1 env2 p2  in
                         (match uu____6251 with
                          | (loc2,env3,uu____6298,pat,ans,uu____6301) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6109 with
             | (loc1,env2,annots,args1) ->
                 let args2 = FStar_List.rev args1  in
                 let l =
                   if dep1
                   then
                     FStar_Parser_Const.mk_dtuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                   else
                     FStar_Parser_Const.mk_tuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                    in
                 let constr =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                    in
                 let l1 =
                   match constr.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                   | uu____6467 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6470 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6470, annots, false))
        | FStar_Parser_AST.PatRecord [] ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatRecord fields ->
            let record = check_fields env1 fields p1.FStar_Parser_AST.prange
               in
            let fields1 =
              FStar_All.pipe_right fields
                (FStar_List.map
                   (fun uu____6551  ->
                      match uu____6551 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6581  ->
                      match uu____6581 with
                      | (f,uu____6587) ->
                          let uu____6588 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6614  ->
                                    match uu____6614 with
                                    | (g,uu____6621) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6588 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6627,p2) ->
                               p2)))
               in
            let app =
              let uu____6634 =
                let uu____6635 =
                  let uu____6642 =
                    let uu____6643 =
                      let uu____6644 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6644  in
                    FStar_Parser_AST.mk_pattern uu____6643
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6642, args)  in
                FStar_Parser_AST.PatApp uu____6635  in
              FStar_Parser_AST.mk_pattern uu____6634
                p1.FStar_Parser_AST.prange
               in
            let uu____6647 = aux loc env1 app  in
            (match uu____6647 with
             | (env2,e,b,p2,annots,uu____6693) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6733 =
                         let uu____6734 =
                           let uu____6748 =
                             let uu___1099_6749 = fv  in
                             let uu____6750 =
                               let uu____6753 =
                                 let uu____6754 =
                                   let uu____6761 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6761)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6754
                                  in
                               FStar_Pervasives_Native.Some uu____6753  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1099_6749.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1099_6749.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6750
                             }  in
                           (uu____6748, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6734  in
                       FStar_All.pipe_left pos uu____6733
                   | uu____6787 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6873 = aux' true loc env1 p2  in
            (match uu____6873 with
             | (loc1,env2,var,p3,ans,uu____6917) ->
                 let uu____6932 =
                   FStar_List.fold_left
                     (fun uu____6981  ->
                        fun p4  ->
                          match uu____6981 with
                          | (loc2,env3,ps1) ->
                              let uu____7046 = aux' true loc2 env3 p4  in
                              (match uu____7046 with
                               | (loc3,env4,uu____7087,p5,ans1,uu____7090) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6932 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7251 ->
            let uu____7252 = aux' true loc env1 p1  in
            (match uu____7252 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7349 = aux_maybe_or env p  in
      match uu____7349 with
      | (env1,b,pats) ->
          ((let uu____7404 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7404
              p.FStar_Parser_AST.prange);
           (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top  ->
    fun env  ->
      fun p  ->
        let mklet x ty tacopt =
          let uu____7477 =
            let uu____7478 =
              let uu____7489 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7489, (ty, tacopt))  in
            LetBinder uu____7478  in
          (env, uu____7477, [])  in
        let op_to_ident x =
          let uu____7506 =
            let uu____7512 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7512, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7506  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7534 = op_to_ident x  in
              mklet uu____7534 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7536) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7542;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7558 = op_to_ident x  in
              let uu____7559 = desugar_term env t  in
              mklet uu____7558 uu____7559 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7561);
                 FStar_Parser_AST.prange = uu____7562;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7582 = desugar_term env t  in
              mklet x uu____7582 tacopt1
          | uu____7583 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7596 = desugar_data_pat env p  in
           match uu____7596 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7625;
                      FStar_Syntax_Syntax.p = uu____7626;_},uu____7627)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7640;
                      FStar_Syntax_Syntax.p = uu____7641;_},uu____7642)::[]
                     -> []
                 | uu____7655 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7663  ->
    fun env  ->
      fun pat  ->
        let uu____7667 = desugar_data_pat env pat  in
        match uu____7667 with | (env1,uu____7683,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7705 = desugar_term_aq env e  in
      match uu____7705 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7724 = desugar_typ_aq env e  in
      match uu____7724 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7734  ->
        fun range  ->
          match uu____7734 with
          | (signedness,width) ->
              let tnm =
                Prims.op_Hat "FStar."
                  (Prims.op_Hat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.op_Hat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____7756 =
                  let uu____7758 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7758  in
                if uu____7756
                then
                  let uu____7761 =
                    let uu____7767 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7767)  in
                  FStar_Errors.log_issue range uu____7761
                else ());
               (let private_intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat ".__"
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat "."
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____7788 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7788 range  in
                let lid1 =
                  let uu____7792 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7792 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7802 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7802 range  in
                           let private_fv =
                             let uu____7804 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7804 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1269_7805 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1269_7805.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1269_7805.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7806 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7810 =
                        let uu____7816 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7816)
                         in
                      FStar_Errors.raise_error uu____7810 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7836 =
                  let uu____7843 =
                    let uu____7844 =
                      let uu____7861 =
                        let uu____7872 =
                          let uu____7881 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7881)  in
                        [uu____7872]  in
                      (lid1, uu____7861)  in
                    FStar_Syntax_Syntax.Tm_app uu____7844  in
                  FStar_Syntax_Syntax.mk uu____7843  in
                uu____7836 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7929 =
          let uu____7930 = unparen t  in uu____7930.FStar_Parser_AST.tm  in
        match uu____7929 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7931; FStar_Ident.ident = uu____7932;
              FStar_Ident.nsstr = uu____7933; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7938 ->
            let uu____7939 =
              let uu____7945 =
                let uu____7947 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7947  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7945)  in
            FStar_Errors.raise_error uu____7939 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___1296_8034 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1296_8034.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1296_8034.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8037 =
          let uu____8038 = unparen top  in uu____8038.FStar_Parser_AST.tm  in
        match uu____8037 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8043 ->
            let uu____8052 = desugar_formula env top  in (uu____8052, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8061 = desugar_formula env t  in (uu____8061, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8070 = desugar_formula env t  in (uu____8070, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8097 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8097, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8099 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8099, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8108 =
                let uu____8109 =
                  let uu____8116 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8116, args)  in
                FStar_Parser_AST.Op uu____8109  in
              FStar_Parser_AST.mk_term uu____8108 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8121 =
              let uu____8122 =
                let uu____8123 =
                  let uu____8130 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8130, [e])  in
                FStar_Parser_AST.Op uu____8123  in
              FStar_Parser_AST.mk_term uu____8122 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8121
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8142 = FStar_Ident.text_of_id op_star  in
             uu____8142 = "*") &&
              (let uu____8147 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8147 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8164;_},t1::t2::[])
                  when
                  let uu____8170 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8170 FStar_Option.isNone ->
                  let uu____8177 = flatten1 t1  in
                  FStar_List.append uu____8177 [t2]
              | uu____8180 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1344_8185 = top  in
              let uu____8186 =
                let uu____8187 =
                  let uu____8198 =
                    FStar_List.map (fun _8209  -> FStar_Util.Inr _8209) terms
                     in
                  (uu____8198, rhs)  in
                FStar_Parser_AST.Sum uu____8187  in
              {
                FStar_Parser_AST.tm = uu____8186;
                FStar_Parser_AST.range =
                  (uu___1344_8185.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1344_8185.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8217 =
              let uu____8218 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8218  in
            (uu____8217, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8224 =
              let uu____8230 =
                let uu____8232 =
                  let uu____8234 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8234 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8232  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8230)  in
            FStar_Errors.raise_error uu____8224 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8249 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8249 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8256 =
                   let uu____8262 =
                     let uu____8264 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8264
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8262)
                    in
                 FStar_Errors.raise_error uu____8256
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8279 =
                     let uu____8304 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8366 = desugar_term_aq env t  in
                               match uu____8366 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8304 FStar_List.unzip  in
                   (match uu____8279 with
                    | (args1,aqs) ->
                        let uu____8499 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8499, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8516)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8533 =
              let uu___1373_8534 = top  in
              let uu____8535 =
                let uu____8536 =
                  let uu____8543 =
                    let uu___1375_8544 = top  in
                    let uu____8545 =
                      let uu____8546 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8546  in
                    {
                      FStar_Parser_AST.tm = uu____8545;
                      FStar_Parser_AST.range =
                        (uu___1375_8544.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1375_8544.FStar_Parser_AST.level)
                    }  in
                  (uu____8543, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8536  in
              {
                FStar_Parser_AST.tm = uu____8535;
                FStar_Parser_AST.range =
                  (uu___1373_8534.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1373_8534.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8533
        | FStar_Parser_AST.Construct (n1,(a,uu____8554)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8574 =
                let uu___1385_8575 = top  in
                let uu____8576 =
                  let uu____8577 =
                    let uu____8584 =
                      let uu___1387_8585 = top  in
                      let uu____8586 =
                        let uu____8587 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8587  in
                      {
                        FStar_Parser_AST.tm = uu____8586;
                        FStar_Parser_AST.range =
                          (uu___1387_8585.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1387_8585.FStar_Parser_AST.level)
                      }  in
                    (uu____8584, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8577  in
                {
                  FStar_Parser_AST.tm = uu____8576;
                  FStar_Parser_AST.range =
                    (uu___1385_8575.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1385_8575.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8574))
        | FStar_Parser_AST.Construct (n1,(a,uu____8595)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8612 =
              let uu___1396_8613 = top  in
              let uu____8614 =
                let uu____8615 =
                  let uu____8622 =
                    let uu___1398_8623 = top  in
                    let uu____8624 =
                      let uu____8625 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8625  in
                    {
                      FStar_Parser_AST.tm = uu____8624;
                      FStar_Parser_AST.range =
                        (uu___1398_8623.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1398_8623.FStar_Parser_AST.level)
                    }  in
                  (uu____8622, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8615  in
              {
                FStar_Parser_AST.tm = uu____8614;
                FStar_Parser_AST.range =
                  (uu___1396_8613.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1396_8613.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8612
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8631; FStar_Ident.ident = uu____8632;
              FStar_Ident.nsstr = uu____8633; FStar_Ident.str = "Type0";_}
            ->
            let uu____8638 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8638, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8639; FStar_Ident.ident = uu____8640;
              FStar_Ident.nsstr = uu____8641; FStar_Ident.str = "Type";_}
            ->
            let uu____8646 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8646, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8647; FStar_Ident.ident = uu____8648;
               FStar_Ident.nsstr = uu____8649; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8669 =
              let uu____8670 =
                let uu____8671 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8671  in
              mk1 uu____8670  in
            (uu____8669, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8672; FStar_Ident.ident = uu____8673;
              FStar_Ident.nsstr = uu____8674; FStar_Ident.str = "Effect";_}
            ->
            let uu____8679 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8679, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8680; FStar_Ident.ident = uu____8681;
              FStar_Ident.nsstr = uu____8682; FStar_Ident.str = "True";_}
            ->
            let uu____8687 =
              let uu____8688 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8688
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8687, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8689; FStar_Ident.ident = uu____8690;
              FStar_Ident.nsstr = uu____8691; FStar_Ident.str = "False";_}
            ->
            let uu____8696 =
              let uu____8697 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8697
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8696, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8700;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8703 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8703 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8712 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8712, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8714 =
                    let uu____8716 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8716 txt
                     in
                  failwith uu____8714))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8725 = desugar_name mk1 setpos env true l  in
              (uu____8725, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8734 = desugar_name mk1 setpos env true l  in
              (uu____8734, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8752 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8752 with
                | FStar_Pervasives_Native.Some uu____8762 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8770 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8770 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8788 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8809 =
                    let uu____8810 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8810  in
                  (uu____8809, noaqs)
              | uu____8816 ->
                  let uu____8824 =
                    let uu____8830 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8830)  in
                  FStar_Errors.raise_error uu____8824
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8840 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8840 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8847 =
                    let uu____8853 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8853)
                     in
                  FStar_Errors.raise_error uu____8847
                    top.FStar_Parser_AST.range
              | uu____8861 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8865 = desugar_name mk1 setpos env true lid'  in
                  (uu____8865, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8887 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8887 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8906 ->
                       let uu____8913 =
                         FStar_Util.take
                           (fun uu____8937  ->
                              match uu____8937 with
                              | (uu____8943,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8913 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8988 =
                              let uu____9013 =
                                FStar_List.map
                                  (fun uu____9056  ->
                                     match uu____9056 with
                                     | (t,imp) ->
                                         let uu____9073 =
                                           desugar_term_aq env t  in
                                         (match uu____9073 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____9013
                                FStar_List.unzip
                               in
                            (match uu____8988 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9216 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9216, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9235 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9235 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9246 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9274  ->
                 match uu___8_9274 with
                 | FStar_Util.Inr uu____9280 -> true
                 | uu____9282 -> false) binders
            ->
            let terms =
              let uu____9291 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9308  ->
                        match uu___9_9308 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9314 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9291 [t]  in
            let uu____9316 =
              let uu____9341 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9398 = desugar_typ_aq env t1  in
                        match uu____9398 with
                        | (t',aq) ->
                            let uu____9409 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9409, aq)))
                 in
              FStar_All.pipe_right uu____9341 FStar_List.unzip  in
            (match uu____9316 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9519 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9519
                    in
                 let uu____9528 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9528, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9555 =
              let uu____9572 =
                let uu____9579 =
                  let uu____9586 =
                    FStar_All.pipe_left (fun _9595  -> FStar_Util.Inl _9595)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9586]  in
                FStar_List.append binders uu____9579  in
              FStar_List.fold_left
                (fun uu____9640  ->
                   fun b  ->
                     match uu____9640 with
                     | (env1,tparams,typs) ->
                         let uu____9701 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9716 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9716)
                            in
                         (match uu____9701 with
                          | (xopt,t1) ->
                              let uu____9741 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9750 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9750)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9741 with
                               | (env2,x) ->
                                   let uu____9770 =
                                     let uu____9773 =
                                       let uu____9776 =
                                         let uu____9777 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9777
                                          in
                                       [uu____9776]  in
                                     FStar_List.append typs uu____9773  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1557_9803 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1557_9803.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1557_9803.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9770)))) (env, [], []) uu____9572
               in
            (match uu____9555 with
             | (env1,uu____9831,targs) ->
                 let tup =
                   let uu____9854 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9854
                    in
                 let uu____9855 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9855, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9874 = uncurry binders t  in
            (match uu____9874 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9918 =
                   match uu___10_9918 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9935 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9935
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9959 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9959 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9992 = aux env [] bs  in (uu____9992, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____10001 = desugar_binder env b  in
            (match uu____10001 with
             | (FStar_Pervasives_Native.None ,uu____10012) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10027 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10027 with
                  | ((x,uu____10043),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10056 =
                        let uu____10057 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10057  in
                      (uu____10056, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10136 = FStar_Util.set_is_empty i  in
                    if uu____10136
                    then
                      let uu____10141 = FStar_Util.set_union acc set1  in
                      aux uu____10141 sets2
                    else
                      (let uu____10146 =
                         let uu____10147 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10147  in
                       FStar_Pervasives_Native.Some uu____10146)
                 in
              let uu____10150 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10150 sets  in
            ((let uu____10154 = check_disjoint bvss  in
              match uu____10154 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10158 =
                    let uu____10164 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10164)
                     in
                  let uu____10168 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10158 uu____10168);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10176 =
                FStar_List.fold_left
                  (fun uu____10196  ->
                     fun pat  ->
                       match uu____10196 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10222,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10232 =
                                  let uu____10235 = free_type_vars env1 t  in
                                  FStar_List.append uu____10235 ftvs  in
                                (env1, uu____10232)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10240,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10251 =
                                  let uu____10254 = free_type_vars env1 t  in
                                  let uu____10257 =
                                    let uu____10260 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10260 ftvs  in
                                  FStar_List.append uu____10254 uu____10257
                                   in
                                (env1, uu____10251)
                            | uu____10265 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10176 with
              | (uu____10274,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10286 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a  ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range))
                       in
                    FStar_List.append uu____10286 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_10343 =
                    match uu___11_10343 with
                    | [] ->
                        let uu____10370 = desugar_term_aq env1 body  in
                        (match uu____10370 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10407 =
                                       let uu____10408 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10408
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10407
                                       body1
                                      in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None  -> body1  in
                             let uu____10477 =
                               let uu____10480 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10480  in
                             (uu____10477, aq))
                    | p::rest ->
                        let uu____10495 = desugar_binding_pat env1 p  in
                        (match uu____10495 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10529)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10544 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10553 =
                               match b with
                               | LetBinder uu____10594 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10663) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10717 =
                                           let uu____10726 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10726, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10717
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10788,uu____10789) ->
                                              let tup2 =
                                                let uu____10791 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10791
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10796 =
                                                  let uu____10803 =
                                                    let uu____10804 =
                                                      let uu____10821 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10824 =
                                                        let uu____10835 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10844 =
                                                          let uu____10855 =
                                                            let uu____10864 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10864
                                                             in
                                                          [uu____10855]  in
                                                        uu____10835 ::
                                                          uu____10844
                                                         in
                                                      (uu____10821,
                                                        uu____10824)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10804
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10803
                                                   in
                                                uu____10796
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10912 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10912
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10963,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10965,pats)) ->
                                              let tupn =
                                                let uu____11010 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____11010
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11023 =
                                                  let uu____11024 =
                                                    let uu____11041 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11044 =
                                                      let uu____11055 =
                                                        let uu____11066 =
                                                          let uu____11075 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11075
                                                           in
                                                        [uu____11066]  in
                                                      FStar_List.append args
                                                        uu____11055
                                                       in
                                                    (uu____11041,
                                                      uu____11044)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11024
                                                   in
                                                mk1 uu____11023  in
                                              let p2 =
                                                let uu____11123 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11123
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11170 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10553 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11264,uu____11265,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11287 =
                let uu____11288 = unparen e  in
                uu____11288.FStar_Parser_AST.tm  in
              match uu____11287 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11298 ->
                  let uu____11299 = desugar_term_aq env e  in
                  (match uu____11299 with
                   | (head1,aq) ->
                       let uu____11312 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11312, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11319 ->
            let rec aux args aqs e =
              let uu____11396 =
                let uu____11397 = unparen e  in
                uu____11397.FStar_Parser_AST.tm  in
              match uu____11396 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11415 = desugar_term_aq env t  in
                  (match uu____11415 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11463 ->
                  let uu____11464 = desugar_term_aq env e  in
                  (match uu____11464 with
                   | (head1,aq) ->
                       let uu____11485 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11485, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
            let bind1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                x.FStar_Ident.idRange FStar_Parser_AST.Expr
               in
            let uu____11548 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11548
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____11600 = desugar_term_aq env t  in
            (match uu____11600 with
             | (tm,s) ->
                 let uu____11611 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11611, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11617 =
              let uu____11630 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11630 then desugar_typ_aq else desugar_term_aq  in
            uu____11617 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11689 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11832  ->
                        match uu____11832 with
                        | (attr_opt,(p,def)) ->
                            let uu____11890 = is_app_pattern p  in
                            if uu____11890
                            then
                              let uu____11923 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11923, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____12006 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____12006, def1)
                               | uu____12051 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12089);
                                           FStar_Parser_AST.prange =
                                             uu____12090;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12139 =
                                            let uu____12160 =
                                              let uu____12165 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12165  in
                                            (uu____12160, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12139, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12257) ->
                                        if top_level
                                        then
                                          let uu____12293 =
                                            let uu____12314 =
                                              let uu____12319 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12319  in
                                            (uu____12314, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12293, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12410 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12443 =
                FStar_List.fold_left
                  (fun uu____12516  ->
                     fun uu____12517  ->
                       match (uu____12516, uu____12517) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12625,uu____12626),uu____12627))
                           ->
                           let uu____12744 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12770 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12770 with
                                  | (env2,xx) ->
                                      let uu____12789 =
                                        let uu____12792 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12792 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12789))
                             | FStar_Util.Inr l ->
                                 let uu____12800 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12800, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12744 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12443 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12948 =
                    match uu____12948 with
                    | (attrs_opt,(uu____12984,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let pos = def.FStar_Parser_AST.range  in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some (t,tacopt) ->
                              let t1 =
                                let uu____13072 = is_comp_type env1 t  in
                                if uu____13072
                                then
                                  ((let uu____13076 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13086 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13086))
                                       in
                                    match uu____13076 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13093 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13096 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13096))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13093
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____13107 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body1 = desugar_term env1 def2  in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____13122 =
                                let uu____13123 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13123
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13122
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        let attrs =
                          match attrs_opt with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some l ->
                              FStar_List.map (desugar_term env1) l
                           in
                        mk_lb
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2,
                            pos)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let uu____13204 = desugar_term_aq env' body  in
                  (match uu____13204 with
                   | (body1,aq) ->
                       let uu____13217 =
                         let uu____13220 =
                           let uu____13221 =
                             let uu____13235 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13235)  in
                           FStar_Syntax_Syntax.Tm_let uu____13221  in
                         FStar_All.pipe_left mk1 uu____13220  in
                       (uu____13217, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13310 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13310 with
              | (env1,binder,pat1) ->
                  let uu____13332 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13358 = desugar_term_aq env1 t2  in
                        (match uu____13358 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13372 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13372
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13373 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13373, aq))
                    | LocalBinder (x,uu____13406) ->
                        let uu____13407 = desugar_term_aq env1 t2  in
                        (match uu____13407 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13421;
                                    FStar_Syntax_Syntax.p = uu____13422;_},uu____13423)::[]
                                   -> body1
                               | uu____13436 ->
                                   let uu____13439 =
                                     let uu____13446 =
                                       let uu____13447 =
                                         let uu____13470 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13473 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13470, uu____13473)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13447
                                        in
                                     FStar_Syntax_Syntax.mk uu____13446  in
                                   uu____13439 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13510 =
                               let uu____13513 =
                                 let uu____13514 =
                                   let uu____13528 =
                                     let uu____13531 =
                                       let uu____13532 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13532]  in
                                     FStar_Syntax_Subst.close uu____13531
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13528)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13514  in
                               FStar_All.pipe_left mk1 uu____13513  in
                             (uu____13510, aq))
                     in
                  (match uu____13332 with | (tm,aq) -> (tm, aq))
               in
            let uu____13594 = FStar_List.hd lbs  in
            (match uu____13594 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13638 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13638
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13654 =
                let uu____13655 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13655  in
              mk1 uu____13654  in
            let uu____13656 = desugar_term_aq env t1  in
            (match uu____13656 with
             | (t1',aq1) ->
                 let uu____13667 = desugar_term_aq env t2  in
                 (match uu____13667 with
                  | (t2',aq2) ->
                      let uu____13678 = desugar_term_aq env t3  in
                      (match uu____13678 with
                       | (t3',aq3) ->
                           let uu____13689 =
                             let uu____13690 =
                               let uu____13691 =
                                 let uu____13714 =
                                   let uu____13731 =
                                     let uu____13746 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13746,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13760 =
                                     let uu____13777 =
                                       let uu____13792 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13792,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13777]  in
                                   uu____13731 :: uu____13760  in
                                 (t1', uu____13714)  in
                               FStar_Syntax_Syntax.Tm_match uu____13691  in
                             mk1 uu____13690  in
                           (uu____13689, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____13988 =
              match uu____13988 with
              | (pat,wopt,b) ->
                  let uu____14010 = desugar_match_pat env pat  in
                  (match uu____14010 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14041 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14041
                          in
                       let uu____14046 = desugar_term_aq env1 b  in
                       (match uu____14046 with
                        | (b1,aq) ->
                            let uu____14059 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14059, aq)))
               in
            let uu____14064 = desugar_term_aq env e  in
            (match uu____14064 with
             | (e1,aq) ->
                 let uu____14075 =
                   let uu____14106 =
                     let uu____14139 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14139 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14106
                     (fun uu____14357  ->
                        match uu____14357 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14075 with
                  | (brs,aqs) ->
                      let uu____14576 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14576, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14610 =
              let uu____14631 = is_comp_type env t  in
              if uu____14631
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14686 = desugar_term_aq env t  in
                 match uu____14686 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14610 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14778 = desugar_term_aq env e  in
                 (match uu____14778 with
                  | (e1,aq) ->
                      let uu____14789 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14789, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14828,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14871 = FStar_List.hd fields  in
              match uu____14871 with | (f,uu____14883) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14929  ->
                        match uu____14929 with
                        | (g,uu____14936) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14943,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14957 =
                         let uu____14963 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14963)
                          in
                       FStar_Errors.raise_error uu____14957
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____14974 =
                    let uu____14985 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15016  ->
                              match uu____15016 with
                              | (f,uu____15026) ->
                                  let uu____15027 =
                                    let uu____15028 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15028
                                     in
                                  (uu____15027, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14985)  in
                  FStar_Parser_AST.Construct uu____14974
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15046 =
                      let uu____15047 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15047  in
                    FStar_Parser_AST.mk_term uu____15046
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15049 =
                      let uu____15062 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15092  ->
                                match uu____15092 with
                                | (f,uu____15102) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15062)  in
                    FStar_Parser_AST.Record uu____15049  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [(FStar_Pervasives_Native.None,
                         ((FStar_Parser_AST.mk_pattern
                             (FStar_Parser_AST.PatVar
                                (x, FStar_Pervasives_Native.None))
                             x.FStar_Ident.idRange), e))],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15162 = desugar_term_aq env recterm1  in
            (match uu____15162 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15178;
                         FStar_Syntax_Syntax.vars = uu____15179;_},args)
                      ->
                      let uu____15205 =
                        let uu____15206 =
                          let uu____15207 =
                            let uu____15224 =
                              let uu____15227 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15228 =
                                let uu____15231 =
                                  let uu____15232 =
                                    let uu____15239 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15239)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15232
                                   in
                                FStar_Pervasives_Native.Some uu____15231  in
                              FStar_Syntax_Syntax.fvar uu____15227
                                FStar_Syntax_Syntax.delta_constant
                                uu____15228
                               in
                            (uu____15224, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15207  in
                        FStar_All.pipe_left mk1 uu____15206  in
                      (uu____15205, s)
                  | uu____15268 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15272 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15272 with
              | (constrname,is_rec) ->
                  let uu____15291 = desugar_term_aq env e  in
                  (match uu____15291 with
                   | (e1,s) ->
                       let projname =
                         FStar_Syntax_Util.mk_field_projector_name_from_ident
                           constrname f.FStar_Ident.ident
                          in
                       let qual =
                         if is_rec
                         then
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.Record_projector
                                (constrname, (f.FStar_Ident.ident)))
                         else FStar_Pervasives_Native.None  in
                       let uu____15311 =
                         let uu____15312 =
                           let uu____15313 =
                             let uu____15330 =
                               let uu____15333 =
                                 let uu____15334 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15334
                                  in
                               FStar_Syntax_Syntax.fvar uu____15333
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15336 =
                               let uu____15347 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15347]  in
                             (uu____15330, uu____15336)  in
                           FStar_Syntax_Syntax.Tm_app uu____15313  in
                         FStar_All.pipe_left mk1 uu____15312  in
                       (uu____15311, s))))
        | FStar_Parser_AST.NamedTyp (uu____15384,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15394 =
              let uu____15395 = FStar_Syntax_Subst.compress tm  in
              uu____15395.FStar_Syntax_Syntax.n  in
            (match uu____15394 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15403 =
                   let uu___2091_15404 =
                     let uu____15405 =
                       let uu____15407 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15407  in
                     FStar_Syntax_Util.exp_string uu____15405  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2091_15404.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2091_15404.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15403, noaqs)
             | uu____15408 ->
                 let uu____15409 =
                   let uu____15415 =
                     let uu____15417 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15417
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15415)  in
                 FStar_Errors.raise_error uu____15409
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15426 = desugar_term_aq env e  in
            (match uu____15426 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15438 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15438, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15443 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15444 =
              let uu____15445 =
                let uu____15452 = desugar_term env e  in (bv, uu____15452)
                 in
              [uu____15445]  in
            (uu____15443, uu____15444)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15477 =
              let uu____15478 =
                let uu____15479 =
                  let uu____15486 = desugar_term env e  in (uu____15486, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15479  in
              FStar_All.pipe_left mk1 uu____15478  in
            (uu____15477, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range]
                 in
              let uu____15515 =
                let uu____15516 =
                  let uu____15523 =
                    let uu____15524 =
                      let uu____15525 =
                        let uu____15534 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15547 =
                          let uu____15548 =
                            let uu____15549 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15549  in
                          FStar_Parser_AST.mk_term uu____15548
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15534, uu____15547,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15525  in
                    FStar_Parser_AST.mk_term uu____15524
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15523)  in
                FStar_Parser_AST.Abs uu____15516  in
              FStar_Parser_AST.mk_term uu____15515
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____15564 = FStar_List.last steps  in
              match uu____15564 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15567,uu____15568,last_expr)) -> last_expr
              | uu____15570 -> failwith "impossible: no last_expr on calc"
               in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            let uu____15598 =
              FStar_List.fold_left
                (fun uu____15615  ->
                   fun uu____15616  ->
                     match (uu____15615, uu____15616) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15639 =
                             let uu____15646 =
                               let uu____15653 =
                                 let uu____15660 =
                                   let uu____15667 =
                                     let uu____15672 = eta_and_annot rel2  in
                                     (uu____15672, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15673 =
                                     let uu____15680 =
                                       let uu____15687 =
                                         let uu____15692 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15692,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15693 =
                                         let uu____15700 =
                                           let uu____15705 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15705,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15700]  in
                                       uu____15687 :: uu____15693  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15680
                                      in
                                   uu____15667 :: uu____15673  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15660
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15653
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15646
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15639
                             just.FStar_Parser_AST.range
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15598 with
             | (e1,uu____15743) ->
                 let e2 =
                   let uu____15745 =
                     let uu____15752 =
                       let uu____15759 =
                         let uu____15766 =
                           let uu____15771 = FStar_Parser_AST.thunk e1  in
                           (uu____15771, FStar_Parser_AST.Nothing)  in
                         [uu____15766]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15759  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15752  in
                   FStar_Parser_AST.mkApp finish1 uu____15745
                     init_expr.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15788 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15789 = desugar_formula env top  in
            (uu____15789, noaqs)
        | uu____15790 ->
            let uu____15791 =
              let uu____15797 =
                let uu____15799 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15799  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15797)  in
            FStar_Errors.raise_error uu____15791 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15809 -> false
    | uu____15819 -> true

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____15857  ->
              match uu____15857 with
              | (a,imp) ->
                  let uu____15870 = desugar_term env a  in
                  arg_withimp_e imp uu____15870))

and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun allow_type_promotion  ->
      fun env  ->
        fun t  ->
          let fail1 err = FStar_Errors.raise_error err r  in
          let is_requires uu____15907 =
            match uu____15907 with
            | (t1,uu____15914) ->
                let uu____15915 =
                  let uu____15916 = unparen t1  in
                  uu____15916.FStar_Parser_AST.tm  in
                (match uu____15915 with
                 | FStar_Parser_AST.Requires uu____15918 -> true
                 | uu____15927 -> false)
             in
          let is_ensures uu____15939 =
            match uu____15939 with
            | (t1,uu____15946) ->
                let uu____15947 =
                  let uu____15948 = unparen t1  in
                  uu____15948.FStar_Parser_AST.tm  in
                (match uu____15947 with
                 | FStar_Parser_AST.Ensures uu____15950 -> true
                 | uu____15959 -> false)
             in
          let is_app head1 uu____15977 =
            match uu____15977 with
            | (t1,uu____15985) ->
                let uu____15986 =
                  let uu____15987 = unparen t1  in
                  uu____15987.FStar_Parser_AST.tm  in
                (match uu____15986 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15990;
                        FStar_Parser_AST.level = uu____15991;_},uu____15992,uu____15993)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15995 -> false)
             in
          let is_smt_pat uu____16007 =
            match uu____16007 with
            | (t1,uu____16014) ->
                let uu____16015 =
                  let uu____16016 = unparen t1  in
                  uu____16016.FStar_Parser_AST.tm  in
                (match uu____16015 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16020);
                               FStar_Parser_AST.range = uu____16021;
                               FStar_Parser_AST.level = uu____16022;_},uu____16023)::uu____16024::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                 smtpat;
                               FStar_Parser_AST.range = uu____16073;
                               FStar_Parser_AST.level = uu____16074;_},uu____16075)::uu____16076::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16109 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16144 = head_and_args t1  in
            match uu____16144 with
            | (head1,args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma"
                     ->
                     let unit_tm =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let nil_pat =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                           t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                         FStar_Parser_AST.Nothing)
                        in
                     let req_true =
                       let req =
                         FStar_Parser_AST.Requires
                           ((FStar_Parser_AST.mk_term
                               (FStar_Parser_AST.Name
                                  FStar_Parser_Const.true_lid)
                               t1.FStar_Parser_AST.range
                               FStar_Parser_AST.Formula),
                             FStar_Pervasives_Native.None)
                          in
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let thunk_ens uu____16237 =
                       match uu____16237 with
                       | (e,i) ->
                           let uu____16248 = FStar_Parser_AST.thunk e  in
                           (uu____16248, i)
                        in
                     let fail_lemma uu____16260 =
                       let expected_one_of =
                         ["Lemma post";
                         "Lemma (ensures post)";
                         "Lemma (requires pre) (ensures post)";
                         "Lemma post [SMTPat ...]";
                         "Lemma (ensures post) [SMTPat ...]";
                         "Lemma (ensures post) (decreases d)";
                         "Lemma (ensures post) (decreases d) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d)";
                         "Lemma (requires pre) (ensures post) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"]
                          in
                       let msg = FStar_String.concat "\n\t" expected_one_of
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_InvalidLemmaArgument,
                           (Prims.op_Hat
                              "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                              msg)) t1.FStar_Parser_AST.range
                        in
                     let args1 =
                       match args with
                       | [] -> fail_lemma ()
                       | req::[] when is_requires req -> fail_lemma ()
                       | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                       | dec::[] when is_decreases dec -> fail_lemma ()
                       | ens::[] ->
                           let uu____16366 =
                             let uu____16373 =
                               let uu____16380 = thunk_ens ens  in
                               [uu____16380; nil_pat]  in
                             req_true :: uu____16373  in
                           unit_tm :: uu____16366
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16427 =
                             let uu____16434 =
                               let uu____16441 = thunk_ens ens  in
                               [uu____16441; nil_pat]  in
                             req :: uu____16434  in
                           unit_tm :: uu____16427
                       | ens::smtpat::[] when
                           (((let uu____16490 = is_requires ens  in
                              Prims.op_Negation uu____16490) &&
                               (let uu____16493 = is_smt_pat ens  in
                                Prims.op_Negation uu____16493))
                              &&
                              (let uu____16496 = is_decreases ens  in
                               Prims.op_Negation uu____16496))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16498 =
                             let uu____16505 =
                               let uu____16512 = thunk_ens ens  in
                               [uu____16512; smtpat]  in
                             req_true :: uu____16505  in
                           unit_tm :: uu____16498
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16559 =
                             let uu____16566 =
                               let uu____16573 = thunk_ens ens  in
                               [uu____16573; nil_pat; dec]  in
                             req_true :: uu____16566  in
                           unit_tm :: uu____16559
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16633 =
                             let uu____16640 =
                               let uu____16647 = thunk_ens ens  in
                               [uu____16647; smtpat; dec]  in
                             req_true :: uu____16640  in
                           unit_tm :: uu____16633
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16707 =
                             let uu____16714 =
                               let uu____16721 = thunk_ens ens  in
                               [uu____16721; nil_pat; dec]  in
                             req :: uu____16714  in
                           unit_tm :: uu____16707
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16781 =
                             let uu____16788 =
                               let uu____16795 = thunk_ens ens  in
                               [uu____16795; smtpat]  in
                             req :: uu____16788  in
                           unit_tm :: uu____16781
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16860 =
                             let uu____16867 =
                               let uu____16874 = thunk_ens ens  in
                               [uu____16874; dec; smtpat]  in
                             req :: uu____16867  in
                           unit_tm :: uu____16860
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16936 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16936, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16964 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16964
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16967 =
                       let uu____16974 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16974, [])  in
                     (uu____16967, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16992 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16992
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16995 =
                       let uu____17002 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17002, [])  in
                     (uu____16995, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17024 =
                       let uu____17031 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17031, [])  in
                     (uu____17024, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17054 when allow_type_promotion ->
                     let default_effect =
                       let uu____17056 = FStar_Options.ml_ish ()  in
                       if uu____17056
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17062 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17062
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17069 =
                       let uu____17076 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17076, [])  in
                     (uu____17069, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17099 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17118 = pre_process_comp_typ t  in
          match uu____17118 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____17170 =
                    let uu____17176 =
                      let uu____17178 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17178
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17176)
                     in
                  fail1 uu____17170)
               else ();
               (let is_universe uu____17194 =
                  match uu____17194 with
                  | (uu____17200,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17202 = FStar_Util.take is_universe args  in
                match uu____17202 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17261  ->
                           match uu____17261 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17268 =
                      let uu____17283 = FStar_List.hd args1  in
                      let uu____17292 = FStar_List.tl args1  in
                      (uu____17283, uu____17292)  in
                    (match uu____17268 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17347 =
                           let is_decrease uu____17386 =
                             match uu____17386 with
                             | (t1,uu____17397) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17408;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17409;_},uu____17410::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17449 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17347 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17566  ->
                                        match uu____17566 with
                                        | (t1,uu____17576) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17585,(arg,uu____17587)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17626 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17647 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17659 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17659
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17666 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17666
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17676 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17676
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17683 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17683
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17690 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17690
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17697 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17697
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17718 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17718
                                      then
                                        match rest2 with
                                        | req::ens::(pat,aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv
                                                    FStar_Parser_Const.nil_lid
                                                  ->
                                                  let nil =
                                                    FStar_Syntax_Syntax.mk_Tm_uinst
                                                      pat
                                                      [FStar_Syntax_Syntax.U_zero]
                                                     in
                                                  let pattern =
                                                    let uu____17809 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17809
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    FStar_Pervasives_Native.None
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____17830 -> pat  in
                                            let uu____17831 =
                                              let uu____17842 =
                                                let uu____17853 =
                                                  let uu____17862 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17862, aq)  in
                                                [uu____17853]  in
                                              ens :: uu____17842  in
                                            req :: uu____17831
                                        | uu____17903 -> rest2
                                      else rest2  in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
                                        FStar_Syntax_Syntax.flags =
                                          (FStar_List.append flags1
                                             decreases_clause)
                                      }))))))

and (desugar_formula :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____17935 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2398_17957 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2398_17957.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2398_17957.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b attr pats body =
        let tk =
          desugar_binder env
            (let uu___2406_18020 = b  in
             {
               FStar_Parser_AST.b = (uu___2406_18020.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2406_18020.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2406_18020.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18049 body1 =
          match uu____18049 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18095::uu____18096) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18114 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2425_18141 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2425_18141.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2425_18141.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18204 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18204))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern
                             (attr, names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18237 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18237 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2438_18247 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2438_18247.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2438_18247.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18253 =
                     let uu____18256 =
                       let uu____18257 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18257]  in
                     no_annot_abs uu____18256 body2  in
                   FStar_All.pipe_left setpos uu____18253  in
                 let uu____18278 =
                   let uu____18279 =
                     let uu____18296 =
                       let uu____18299 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18299
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____18301 =
                       let uu____18312 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18312]  in
                     (uu____18296, uu____18301)  in
                   FStar_Syntax_Syntax.Tm_app uu____18279  in
                 FStar_All.pipe_left mk1 uu____18278)
        | uu____18351 -> failwith "impossible"  in
      let push_quant q binders attr pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18433 = q (rest, attr, pats, body)  in
              let uu____18438 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18433 uu____18438
                FStar_Parser_AST.Formula
               in
            let uu____18439 = q ([b], attr, ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____18439 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18452 -> failwith "impossible"  in
      let uu____18456 =
        let uu____18457 = unparen f  in uu____18457.FStar_Parser_AST.tm  in
      match uu____18456 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18470,uu____18471,uu____18472) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18500,uu____18501,uu____18502) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,attr,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18567 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders attr
              pats body
             in
          desugar_formula env uu____18567
      | FStar_Parser_AST.QExists (_1::_2::_3,attr,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18620 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders attr
              pats body
             in
          desugar_formula env uu____18620
      | FStar_Parser_AST.QForall (b::[],attr,pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b attr pats body
      | FStar_Parser_AST.QExists (b::[],attr,pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b attr pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18698 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18703 =
        FStar_List.fold_left
          (fun uu____18736  ->
             fun b  ->
               match uu____18736 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2524_18780 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2524_18780.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2524_18780.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2524_18780.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18795 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18795 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2534_18813 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2534_18813.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2534_18813.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18814 =
                               let uu____18821 =
                                 let uu____18826 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18826)  in
                               uu____18821 :: out  in
                             (env2, uu____18814))
                    | uu____18837 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18703 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____18910 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18910)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18915 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18915)
      | FStar_Parser_AST.TVariable x ->
          let uu____18919 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18919)
      | FStar_Parser_AST.NoName t ->
          let uu____18923 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18923)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env  ->
    fun imp  ->
      fun uu___12_18931  ->
        match uu___12_18931 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18953 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18953, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18970 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18970 with
             | (env1,a1) ->
                 let uu____18987 =
                   let uu____18994 = trans_aqual env1 imp  in
                   ((let uu___2568_19000 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2568_19000.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2568_19000.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18994)
                    in
                 (uu____18987, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_19008  ->
      match uu___13_19008 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19012 =
            let uu____19013 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19013  in
          FStar_Pervasives_Native.Some uu____19012
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19029) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19031) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19034 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19052 = binder_ident b  in
         FStar_Common.list_of_option uu____19052) bs
  
let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___14_19089  ->
                  match uu___14_19089 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19094 -> false))
           in
        let quals2 q =
          let uu____19108 =
            (let uu____19112 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19112) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19108
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19129 = FStar_Ident.range_of_lid disc_name  in
                let uu____19130 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19129;
                  FStar_Syntax_Syntax.sigquals = uu____19130;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
  
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____19170 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19208  ->
                        match uu____19208 with
                        | (x,uu____19219) ->
                            let uu____19224 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19224 with
                             | (field_name,uu____19232) ->
                                 let only_decl =
                                   ((let uu____19237 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19237)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19239 =
                                        let uu____19241 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19241.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19239)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19259 =
                                       FStar_List.filter
                                         (fun uu___15_19263  ->
                                            match uu___15_19263 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19266 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19259
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19281  ->
                                             match uu___16_19281 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19286 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19289 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19289;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19296 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19296
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____19307 =
                                        let uu____19312 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19312  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19307;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbattrs = [];
                                        FStar_Syntax_Syntax.lbpos =
                                          FStar_Range.dummyRange
                                      }  in
                                    let impl =
                                      let uu____19316 =
                                        let uu____19317 =
                                          let uu____19324 =
                                            let uu____19327 =
                                              let uu____19328 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19328
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19327]  in
                                          ((false, [lb]), uu____19324)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19317
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19316;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____19170 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____19377,t,uu____19379,n1,uu____19381) when
            let uu____19388 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19388 ->
            let uu____19390 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19390 with
             | (formals,uu____19408) ->
                 (match formals with
                  | [] -> []
                  | uu____19437 ->
                      let filter_records uu___17_19453 =
                        match uu___17_19453 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19456,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19468 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19470 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19470 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             iquals)
                            &&
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Private iquals))
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____19482 = FStar_Util.first_N n1 formals  in
                      (match uu____19482 with
                       | (uu____19511,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19545 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun kopt  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____19624 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19624
                    then
                      let uu____19630 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19630
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19634 =
                      let uu____19639 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19639  in
                    let uu____19640 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19646 =
                          let uu____19649 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19649  in
                        FStar_Syntax_Util.arrow typars uu____19646
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19654 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19634;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19640;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19654;
                      FStar_Syntax_Syntax.lbattrs = [];
                      FStar_Syntax_Syntax.lbpos = rng
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
                  }
  
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___18_19708 =
            match uu___18_19708 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19710,uu____19711) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19721,uu____19722,uu____19723) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19733,uu____19734,uu____19735) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19765,uu____19766,uu____19767) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19813) ->
                let uu____19814 =
                  let uu____19815 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19815  in
                FStar_Parser_AST.mk_term uu____19814 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19817 =
                  let uu____19818 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19818  in
                FStar_Parser_AST.mk_term uu____19817 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19820) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____19851 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19859 =
                     let uu____19860 =
                       let uu____19867 = binder_to_term b  in
                       (out, uu____19867, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19860  in
                   FStar_Parser_AST.mk_term uu____19859
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19879 =
            match uu___19_19879 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19936  ->
                       match uu____19936 with
                       | (x,t,uu____19947) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19953 =
                    let uu____19954 =
                      let uu____19955 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19955  in
                    FStar_Parser_AST.mk_term uu____19954
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19953 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19962 = binder_idents parms  in id1 ::
                    uu____19962
                   in
                (FStar_List.iter
                   (fun uu____19980  ->
                      match uu____19980 with
                      | (f,uu____19990,uu____19991) ->
                          let uu____19996 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19996
                          then
                            let uu____20001 =
                              let uu____20007 =
                                let uu____20009 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20009
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20007)
                               in
                            FStar_Errors.raise_error uu____20001
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20015 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____20042  ->
                            match uu____20042 with
                            | (x,uu____20052,uu____20053) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____20015)))
            | uu____20111 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20151 =
            match uu___20_20151 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20175 = typars_of_binders _env binders  in
                (match uu____20175 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20211 =
                         let uu____20212 =
                           let uu____20213 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20213  in
                         FStar_Parser_AST.mk_term uu____20212
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20211 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     let _env1 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____20224 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20267 =
              FStar_List.fold_left
                (fun uu____20301  ->
                   fun uu____20302  ->
                     match (uu____20301, uu____20302) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20371 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20371 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20267 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20462 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20462
                | uu____20463 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20471 = desugar_abstract_tc quals env [] tc  in
              (match uu____20471 with
               | (uu____20484,uu____20485,se,uu____20487) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20490,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20509 =
                                 let uu____20511 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20511  in
                               if uu____20509
                               then
                                 let uu____20514 =
                                   let uu____20520 =
                                     let uu____20522 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20522
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20520)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20514
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____20535 ->
                               let uu____20536 =
                                 let uu____20543 =
                                   let uu____20544 =
                                     let uu____20559 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20559)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20544
                                    in
                                 FStar_Syntax_Syntax.mk uu____20543  in
                               uu____20536 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2843_20572 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2843_20572.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2843_20572.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2843_20572.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20573 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20577 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20577
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20590 = typars_of_binders env binders  in
              (match uu____20590 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20624 =
                           FStar_Util.for_some
                             (fun uu___21_20627  ->
                                match uu___21_20627 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20630 -> false) quals
                            in
                         if uu____20624
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20638 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20638
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20643 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20649  ->
                               match uu___22_20649 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20652 -> false))
                        in
                     if uu____20643
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20666 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20666
                     then
                       let uu____20672 =
                         let uu____20679 =
                           let uu____20680 = unparen t  in
                           uu____20680.FStar_Parser_AST.tm  in
                         match uu____20679 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20701 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20731)::args_rev ->
                                   let uu____20743 =
                                     let uu____20744 = unparen last_arg  in
                                     uu____20744.FStar_Parser_AST.tm  in
                                   (match uu____20743 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20772 -> ([], args))
                               | uu____20781 -> ([], args)  in
                             (match uu____20701 with
                              | (cattributes,args1) ->
                                  let uu____20820 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20820))
                         | uu____20831 -> (t, [])  in
                       match uu____20672 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___23_20854  ->
                                     match uu___23_20854 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20857 -> true))
                              in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars kopt1 t1 [qlid] quals1
                          rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____20866)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20890 = tycon_record_as_variant trec  in
              (match uu____20890 with
               | (t,fs) ->
                   let uu____20907 =
                     let uu____20910 =
                       let uu____20911 =
                         let uu____20920 =
                           let uu____20923 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20923  in
                         (uu____20920, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20911  in
                     uu____20910 :: quals  in
                   desugar_tycon env d uu____20907 [t])
          | uu____20928::uu____20929 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21099 = et  in
                match uu____21099 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21329 ->
                         let trec = tc  in
                         let uu____21353 = tycon_record_as_variant trec  in
                         (match uu____21353 with
                          | (t,fs) ->
                              let uu____21413 =
                                let uu____21416 =
                                  let uu____21417 =
                                    let uu____21426 =
                                      let uu____21429 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21429  in
                                    (uu____21426, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21417
                                   in
                                uu____21416 :: quals1  in
                              collect_tcs uu____21413 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21519 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21519 with
                          | (env2,uu____21580,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21733 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21733 with
                          | (env2,uu____21794,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21922 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21972 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21972 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22487  ->
                             match uu___25_22487 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22553,uu____22554);
                                    FStar_Syntax_Syntax.sigrng = uu____22555;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22556;
                                    FStar_Syntax_Syntax.sigmeta = uu____22557;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22558;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22622 =
                                     typars_of_binders env1 binders  in
                                   match uu____22622 with
                                   | (env2,tpars1) ->
                                       let uu____22649 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22649 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____22678 =
                                   let uu____22697 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22697)
                                    in
                                 [uu____22678]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22757);
                                    FStar_Syntax_Syntax.sigrng = uu____22758;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22760;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22761;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____22862 = push_tparams env1 tpars
                                    in
                                 (match uu____22862 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22929  ->
                                             match uu____22929 with
                                             | (x,uu____22941) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22946 =
                                        let uu____22973 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23083  ->
                                                  match uu____23083 with
                                                  | (id1,topt,doc1,of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                               -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                                ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____23143 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23143
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___24_23154
                                                                 ->
                                                                match uu___24_23154
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23166
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23174 =
                                                        let uu____23193 =
                                                          let uu____23194 =
                                                            let uu____23195 =
                                                              let uu____23211
                                                                =
                                                                let uu____23212
                                                                  =
                                                                  let uu____23215
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23215
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23212
                                                                 in
                                                              (name, univs1,
                                                                uu____23211,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23195
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23194;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____23193)
                                                         in
                                                      (name, uu____23174)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22973
                                         in
                                      (match uu____22946 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs1, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 []
                                             })
                                           :: constrs1))
                             | uu____23427 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23555  ->
                             match uu____23555 with
                             | (name_doc,uu____23581,uu____23582) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23654  ->
                             match uu____23654 with
                             | (uu____23673,uu____23674,se) -> se))
                      in
                   let uu____23700 =
                     let uu____23707 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23707 rng
                      in
                   (match uu____23700 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____23769  ->
                                  match uu____23769 with
                                  | (uu____23790,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23838,tps,k,uu____23841,constrs)
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract
                                             quals1)
                                            &&
                                            (Prims.op_Negation
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Private
                                                  quals1))
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      let uu____23862 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23877 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23894,uu____23895,uu____23896,uu____23897,uu____23898)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23905
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23877
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23909 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23916  ->
                                                          match uu___26_23916
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23918 ->
                                                              true
                                                          | uu____23928 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23909))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23862
                                  | uu____23930 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23947  ->
                                 match uu____23947 with
                                 | (lid,doc1) ->
                                     FStar_Syntax_DsEnv.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env  ->
    fun binders  ->
      let uu____23992 =
        FStar_List.fold_left
          (fun uu____24027  ->
             fun b  ->
               match uu____24027 with
               | (env1,binders1) ->
                   let uu____24071 = desugar_binder env1 b  in
                   (match uu____24071 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24094 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24094 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24147 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23992 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____24251 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24258  ->
                    match uu___27_24258 with
                    | FStar_Syntax_Syntax.Reflectable uu____24260 -> true
                    | uu____24262 -> false))
             in
          if uu____24251
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24267 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24267
                (FStar_Syntax_DsEnv.qualify monad_env)
               in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name]  in
            let refl_decl =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_declare_typ
                     (reflect_lid, [], FStar_Syntax_Syntax.tun));
                FStar_Syntax_Syntax.sigrng = range;
                FStar_Syntax_Syntax.sigquals = quals1;
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let uu____24308 = FStar_Syntax_Util.head_and_args at1  in
      match uu____24308 with
      | (hd1,args) ->
          let uu____24361 =
            let uu____24376 =
              let uu____24377 = FStar_Syntax_Subst.compress hd1  in
              uu____24377.FStar_Syntax_Syntax.n  in
            (uu____24376, args)  in
          (match uu____24361 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24402)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24437 =
                 let uu____24442 =
                   let uu____24451 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24451 a1  in
                 uu____24442 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24437 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24477 =
                      let uu____24486 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24486, b)  in
                    FStar_Pervasives_Native.Some uu____24477
                | uu____24503 ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let b =
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.fail_lax_attr
                  in
               FStar_Pervasives_Native.Some ([], b)
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24557) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                else ();
                FStar_Pervasives_Native.None)
           | uu____24592 -> FStar_Pervasives_Native.None)
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.term Prims.list ->
                  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                    Prims.list))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                fun attrs  ->
                  let env0 = env  in
                  let monad_env =
                    FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                  let uu____24764 = desugar_binders monad_env eff_binders  in
                  match uu____24764 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24804 =
                          let uu____24806 =
                            let uu____24815 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24815  in
                          FStar_List.length uu____24806  in
                        uu____24804 = (Prims.parse_int "1")  in
                      let mandatory_members =
                        let rr_members = ["repr"; "return"; "bind"]  in
                        if for_free
                        then rr_members
                        else
                          FStar_List.append rr_members
                            ["return_wp";
                            "bind_wp";
                            "if_then_else";
                            "ite_wp";
                            "stronger";
                            "close_wp";
                            "assert_p";
                            "assume_p";
                            "null_wp";
                            "trivial"]
                         in
                      let name_of_eff_decl decl =
                        match decl.FStar_Parser_AST.d with
                        | FStar_Parser_AST.Tycon
                            (uu____24899,uu____24900,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24902,uu____24903,uu____24904),uu____24905)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24942 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24945 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24957 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24957 mandatory_members)
                          eff_decls
                         in
                      (match uu____24945 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24976 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____25005  ->
                                     fun decl  ->
                                       match uu____25005 with
                                       | (env2,out) ->
                                           let uu____25025 =
                                             desugar_decl env2 decl  in
                                           (match uu____25025 with
                                            | (env3,ses) ->
                                                let uu____25038 =
                                                  let uu____25041 =
                                                    FStar_List.hd ses  in
                                                  uu____25041 :: out  in
                                                (env3, uu____25038)))
                                  (env1, []))
                              in
                           (match uu____24976 with
                            | (env2,decls) ->
                                let binders1 =
                                  FStar_Syntax_Subst.close_binders binders
                                   in
                                let actions_docs =
                                  FStar_All.pipe_right actions
                                    (FStar_List.map
                                       (fun d1  ->
                                          match d1.FStar_Parser_AST.d with
                                          | FStar_Parser_AST.Tycon
                                              (uu____25110,uu____25111,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25114,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____25115,(def,uu____25117)::
                                                      (cps_type,uu____25119)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____25120;
                                                   FStar_Parser_AST.level =
                                                     uu____25121;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____25177 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25177 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25215 =
                                                     let uu____25216 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25217 =
                                                       let uu____25218 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25218
                                                        in
                                                     let uu____25225 =
                                                       let uu____25226 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25226
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25216;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25217;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____25225
                                                     }  in
                                                   (uu____25215, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____25235,uu____25236,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25239,defn),doc1)::[])
                                              when for_free ->
                                              let uu____25278 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25278 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25316 =
                                                     let uu____25317 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25318 =
                                                       let uu____25319 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25319
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25317;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25318;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____25316, doc1))
                                          | uu____25328 ->
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                  "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                d1.FStar_Parser_AST.drange))
                                   in
                                let actions1 =
                                  FStar_List.map FStar_Pervasives_Native.fst
                                    actions_docs
                                   in
                                let eff_t1 =
                                  FStar_Syntax_Subst.close binders1 eff_t  in
                                let lookup1 s =
                                  let l =
                                    let uu____25364 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25364
                                     in
                                  let uu____25366 =
                                    let uu____25367 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____25367
                                     in
                                  ([], uu____25366)  in
                                let mname =
                                  FStar_Syntax_DsEnv.qualify env0 eff_name
                                   in
                                let qualifiers =
                                  FStar_List.map
                                    (trans_qual d.FStar_Parser_AST.drange
                                       (FStar_Pervasives_Native.Some mname))
                                    quals
                                   in
                                let se =
                                  if for_free
                                  then
                                    let dummy_tscheme =
                                      let uu____25385 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____25385)  in
                                    let uu____25392 =
                                      let uu____25393 =
                                        let uu____25394 =
                                          let uu____25395 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25395
                                           in
                                        let uu____25405 = lookup1 "return"
                                           in
                                        let uu____25407 = lookup1 "bind"  in
                                        let uu____25409 =
                                          FStar_List.map (desugar_term env2)
                                            attrs
                                           in
                                        {
                                          FStar_Syntax_Syntax.cattributes =
                                            [];
                                          FStar_Syntax_Syntax.mname = mname;
                                          FStar_Syntax_Syntax.univs = [];
                                          FStar_Syntax_Syntax.binders =
                                            binders1;
                                          FStar_Syntax_Syntax.signature =
                                            eff_t1;
                                          FStar_Syntax_Syntax.ret_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.bind_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.if_then_else =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.ite_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.stronger =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.close_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.assert_p =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.assume_p =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.null_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.trivial =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.repr =
                                            uu____25394;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25405;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25407;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25409
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____25393
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____25392;
                                      FStar_Syntax_Syntax.sigrng =
                                        (d.FStar_Parser_AST.drange);
                                      FStar_Syntax_Syntax.sigquals =
                                        qualifiers;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = []
                                    }
                                  else
                                    (let rr =
                                       FStar_Util.for_some
                                         (fun uu___28_25417  ->
                                            match uu___28_25417 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25420 -> true
                                            | uu____25422 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25437 =
                                       let uu____25438 =
                                         let uu____25439 =
                                           lookup1 "return_wp"  in
                                         let uu____25441 = lookup1 "bind_wp"
                                            in
                                         let uu____25443 =
                                           lookup1 "if_then_else"  in
                                         let uu____25445 = lookup1 "ite_wp"
                                            in
                                         let uu____25447 = lookup1 "stronger"
                                            in
                                         let uu____25449 = lookup1 "close_wp"
                                            in
                                         let uu____25451 = lookup1 "assert_p"
                                            in
                                         let uu____25453 = lookup1 "assume_p"
                                            in
                                         let uu____25455 = lookup1 "null_wp"
                                            in
                                         let uu____25457 = lookup1 "trivial"
                                            in
                                         let uu____25459 =
                                           if rr
                                           then
                                             let uu____25461 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____25461
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____25479 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25484 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25489 =
                                           FStar_List.map (desugar_term env2)
                                             attrs
                                            in
                                         {
                                           FStar_Syntax_Syntax.cattributes =
                                             [];
                                           FStar_Syntax_Syntax.mname = mname;
                                           FStar_Syntax_Syntax.univs = [];
                                           FStar_Syntax_Syntax.binders =
                                             binders1;
                                           FStar_Syntax_Syntax.signature =
                                             eff_t1;
                                           FStar_Syntax_Syntax.ret_wp =
                                             uu____25439;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25441;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25443;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25445;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25447;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25449;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____25451;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____25453;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____25455;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25457;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25459;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25479;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25484;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25489
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25438
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25437;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     })
                                   in
                                let env3 =
                                  FStar_Syntax_DsEnv.push_sigelt env0 se  in
                                let env4 =
                                  FStar_Syntax_DsEnv.push_doc env3 mname
                                    d.FStar_Parser_AST.doc
                                   in
                                let env5 =
                                  FStar_All.pipe_right actions_docs
                                    (FStar_List.fold_left
                                       (fun env5  ->
                                          fun uu____25515  ->
                                            match uu____25515 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25529 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25529
                                                   in
                                                FStar_Syntax_DsEnv.push_doc
                                                  env6
                                                  a.FStar_Syntax_Syntax.action_name
                                                  doc1) env4)
                                   in
                                let env6 =
                                  push_reflect_effect env5 qualifiers mname
                                    d.FStar_Parser_AST.drange
                                   in
                                let env7 =
                                  FStar_Syntax_DsEnv.push_doc env6 mname
                                    d.FStar_Parser_AST.doc
                                   in
                                (env7, [se])))

and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name
                   in
                let uu____25553 = desugar_binders env1 eff_binders  in
                match uu____25553 with
                | (env2,binders) ->
                    let uu____25590 =
                      let uu____25601 = head_and_args defn  in
                      match uu____25601 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25638 ->
                                let uu____25639 =
                                  let uu____25645 =
                                    let uu____25647 =
                                      let uu____25649 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25649 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25647  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25645)
                                   in
                                FStar_Errors.raise_error uu____25639
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25655 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25685)::args_rev ->
                                let uu____25697 =
                                  let uu____25698 = unparen last_arg  in
                                  uu____25698.FStar_Parser_AST.tm  in
                                (match uu____25697 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25726 -> ([], args))
                            | uu____25735 -> ([], args)  in
                          (match uu____25655 with
                           | (cattributes,args1) ->
                               let uu____25778 = desugar_args env2 args1  in
                               let uu____25779 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25778, uu____25779))
                       in
                    (match uu____25590 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                "Unexpected number of arguments to effect constructor")
                              defn.FStar_Parser_AST.range
                          else ();
                          (let uu____25819 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25819 with
                           | (ed_binders,uu____25833,ed_binders_opening) ->
                               let sub' shift_n uu____25852 =
                                 match uu____25852 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25867 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25867 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25871 =
                                       let uu____25872 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25872)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25871
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25893 =
                                   let uu____25894 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25894
                                    in
                                 let uu____25909 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25910 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25911 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25912 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25913 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25914 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25915 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25916 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25917 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25918 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25919 =
                                   let uu____25920 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25920
                                    in
                                 let uu____25935 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25936 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25937 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25953 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25954 =
                                          let uu____25955 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25955
                                           in
                                        let uu____25970 =
                                          let uu____25971 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25971
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25953;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25954;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25970
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____25893;
                                   FStar_Syntax_Syntax.ret_wp = uu____25909;
                                   FStar_Syntax_Syntax.bind_wp = uu____25910;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25911;
                                   FStar_Syntax_Syntax.ite_wp = uu____25912;
                                   FStar_Syntax_Syntax.stronger = uu____25913;
                                   FStar_Syntax_Syntax.close_wp = uu____25914;
                                   FStar_Syntax_Syntax.assert_p = uu____25915;
                                   FStar_Syntax_Syntax.assume_p = uu____25916;
                                   FStar_Syntax_Syntax.null_wp = uu____25917;
                                   FStar_Syntax_Syntax.trivial = uu____25918;
                                   FStar_Syntax_Syntax.repr = uu____25919;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25935;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25936;
                                   FStar_Syntax_Syntax.actions = uu____25937;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25989 =
                                     let uu____25991 =
                                       let uu____26000 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____26000
                                        in
                                     FStar_List.length uu____25991  in
                                   uu____25989 = (Prims.parse_int "1")  in
                                 let uu____26033 =
                                   let uu____26036 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26036 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (if for_free
                                      then
                                        FStar_Syntax_Syntax.Sig_new_effect_for_free
                                          ed1
                                      else
                                        FStar_Syntax_Syntax.Sig_new_effect
                                          ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26033;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_Syntax_DsEnv.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_Syntax_DsEnv.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____26060 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____26060
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____26062 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26062
                                 then
                                   let reflect_lid =
                                     let uu____26069 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26069
                                       (FStar_Syntax_DsEnv.qualify monad_env)
                                      in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname]
                                      in
                                   let refl_decl =
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_declare_typ
                                            (reflect_lid, [],
                                              FStar_Syntax_Syntax.tun));
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_Syntax_DsEnv.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____26081 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____26081 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____26166 ->
              let uu____26169 =
                let uu____26171 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____26171
                 in
              Prims.op_Hat "\n  " uu____26169
          | uu____26174 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____26193  ->
               match uu____26193 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.op_Hat k (Prims.op_Hat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.op_Hat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.op_Hat summary (Prims.op_Hat pp (Prims.op_Hat other1 text))
           in
        let fv =
          let uu____26238 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____26238
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____26241 =
          let uu____26252 = FStar_Syntax_Syntax.as_arg arg  in [uu____26252]
           in
        FStar_Syntax_Util.mk_app fv uu____26241

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26283 = desugar_decl_noattrs env d  in
      match uu____26283 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____26301 = mk_comment_attr d  in uu____26301 :: attrs1  in
          let uu____26302 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3400_26312 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3400_26312.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3400_26312.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3400_26312.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3400_26312.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3402_26315 = sigelt  in
                      let uu____26316 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26322 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26322) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3402_26315.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3402_26315.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3402_26315.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3402_26315.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26316
                      })) sigelts
             in
          (env1, uu____26302)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26348 = desugar_decl_aux env d  in
      match uu____26348 with
      | (env1,ses) ->
          let uu____26359 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26359)

and (desugar_decl_noattrs :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let p1 = trans_pragma p  in
          (FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange;
           (let se =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_pragma p1);
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            (env, [se])))
      | FStar_Parser_AST.Fsdoc uu____26387 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26392 = FStar_Syntax_DsEnv.iface env  in
          if uu____26392
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26407 =
               let uu____26409 =
                 let uu____26411 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26412 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26411
                   uu____26412
                  in
               Prims.op_Negation uu____26409  in
             if uu____26407
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26426 =
                  let uu____26428 =
                    let uu____26430 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26430 lid  in
                  Prims.op_Negation uu____26428  in
                if uu____26426
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26444 =
                     let uu____26446 =
                       let uu____26448 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26448
                         lid
                        in
                     Prims.op_Negation uu____26446  in
                   if uu____26444
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26466 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26466, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____26507,uu____26508)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26547 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26574  ->
                 match uu____26574 with | (x,uu____26582) -> x) tcs
             in
          let uu____26587 =
            let uu____26592 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26592 tcs1  in
          (match uu____26587 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26609 =
                   let uu____26610 =
                     let uu____26617 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26617  in
                   [uu____26610]  in
                 let uu____26630 =
                   let uu____26633 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26636 =
                     let uu____26647 =
                       let uu____26656 =
                         let uu____26657 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26657  in
                       FStar_Syntax_Syntax.as_arg uu____26656  in
                     [uu____26647]  in
                   FStar_Syntax_Util.mk_app uu____26633 uu____26636  in
                 FStar_Syntax_Util.abs uu____26609 uu____26630
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26697,id1))::uu____26699 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26702::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26706 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26706 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26712 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26712]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26733) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26743,uu____26744,uu____26745,uu____26746,uu____26747)
                     ->
                     let uu____26756 =
                       let uu____26757 =
                         let uu____26758 =
                           let uu____26765 = mkclass lid  in
                           (meths, uu____26765)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26758  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26757;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26756]
                 | uu____26768 -> []  in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses  in
                   FStar_List.concatMap (splice_decl meths) ses
                 else []  in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra
                  in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26802;
                    FStar_Parser_AST.prange = uu____26803;_},uu____26804)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26814;
                    FStar_Parser_AST.prange = uu____26815;_},uu____26816)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26832;
                         FStar_Parser_AST.prange = uu____26833;_},uu____26834);
                    FStar_Parser_AST.prange = uu____26835;_},uu____26836)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26858;
                         FStar_Parser_AST.prange = uu____26859;_},uu____26860);
                    FStar_Parser_AST.prange = uu____26861;_},uu____26862)::[]
                   -> false
               | (p,uu____26891)::[] ->
                   let uu____26900 = is_app_pattern p  in
                   Prims.op_Negation uu____26900
               | uu____26902 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x  -> (FStar_Pervasives_Native.None, x))
                lets
               in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let uu____26977 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26977 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26990 =
                     let uu____26991 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26991.FStar_Syntax_Syntax.n  in
                   match uu____26990 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27001) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let quals1 =
                         match quals with
                         | uu____27037::uu____27038 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____27041 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___29_27057  ->
                                     match uu___29_27057 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____27060;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____27061;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____27062;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____27063;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____27064;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____27065;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____27066;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____27078;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____27079;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____27080;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____27081;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____27082;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____27083;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____27097 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____27130  ->
                                   match uu____27130 with
                                   | (uu____27144,(uu____27145,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____27097
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____27165 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____27165
                         then
                           let uu____27171 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3597_27186 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3599_27188 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3599_27188.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3599_27188.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3597_27186.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3597_27186.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3597_27186.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3597_27186.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3597_27186.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3597_27186.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____27171)
                         else lbs  in
                       let names1 =
                         FStar_All.pipe_right fvs
                           (FStar_List.map
                              (fun fv  ->
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let attrs =
                         FStar_List.map (desugar_term env)
                           d.FStar_Parser_AST.attrs
                          in
                       let s =
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                           FStar_Syntax_Syntax.sigrng =
                             (d.FStar_Parser_AST.drange);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = attrs
                         }  in
                       let env1 = FStar_Syntax_DsEnv.push_sigelt env s  in
                       let env2 =
                         FStar_List.fold_left
                           (fun env2  ->
                              fun id1  ->
                                FStar_Syntax_DsEnv.push_doc env2 id1
                                  d.FStar_Parser_AST.doc) env1 names1
                          in
                       (env2, [s])
                   | uu____27218 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27226 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27245 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27226 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___3625_27282 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3625_27282.FStar_Parser_AST.prange)
                       }
                   | uu____27289 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3629_27296 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3629_27296.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3629_27296.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3629_27296.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27332 id1 =
                   match uu____27332 with
                   | (env1,ses) ->
                       let main =
                         let uu____27353 =
                           let uu____27354 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27354  in
                         FStar_Parser_AST.mk_term uu____27353
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id1]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____27404 = desugar_decl env1 id_decl  in
                       (match uu____27404 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27422 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27422 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let env1 =
            FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc  in
          (env1,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____27446 = close_fun env t  in
            desugar_term env uu____27446  in
          let quals1 =
            let uu____27450 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27450
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27462 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27462;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____27476 =
                  let uu____27485 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27485]  in
                let uu____27504 =
                  let uu____27507 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27507
                   in
                FStar_Syntax_Util.arrow uu____27476 uu____27504
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
            attrs
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____27562 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27562 with
            | FStar_Pervasives_Native.None  ->
                let uu____27565 =
                  let uu____27571 =
                    let uu____27573 =
                      let uu____27575 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27575 " not found"  in
                    Prims.op_Hat "Effect name " uu____27573  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27571)  in
                FStar_Errors.raise_error uu____27565
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27583 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27601 =
                  let uu____27604 =
                    let uu____27605 = desugar_term env t  in
                    ([], uu____27605)  in
                  FStar_Pervasives_Native.Some uu____27604  in
                (uu____27601, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27618 =
                  let uu____27621 =
                    let uu____27622 = desugar_term env wp  in
                    ([], uu____27622)  in
                  FStar_Pervasives_Native.Some uu____27621  in
                let uu____27629 =
                  let uu____27632 =
                    let uu____27633 = desugar_term env t  in
                    ([], uu____27633)  in
                  FStar_Pervasives_Native.Some uu____27632  in
                (uu____27618, uu____27629)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27645 =
                  let uu____27648 =
                    let uu____27649 = desugar_term env t  in
                    ([], uu____27649)  in
                  FStar_Pervasives_Native.Some uu____27648  in
                (FStar_Pervasives_Native.None, uu____27645)
             in
          (match uu____27583 with
           | (lift_wp,lift) ->
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect
                        {
                          FStar_Syntax_Syntax.source = src;
                          FStar_Syntax_Syntax.target = dst;
                          FStar_Syntax_Syntax.lift_wp = lift_wp;
                          FStar_Syntax_Syntax.lift = lift
                        });
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               (env, [se]))
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27683 =
              let uu____27684 =
                let uu____27691 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27691, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27684  in
            {
              FStar_Syntax_Syntax.sigel = uu____27683;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____27718 =
        FStar_List.fold_left
          (fun uu____27738  ->
             fun d  ->
               match uu____27738 with
               | (env1,sigelts) ->
                   let uu____27758 = desugar_decl env1 d  in
                   (match uu____27758 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27718 with
      | (env1,sigelts) ->
          let rec forward acc uu___31_27803 =
            match uu___31_27803 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27817,FStar_Syntax_Syntax.Sig_let uu____27818) ->
                     let uu____27831 =
                       let uu____27834 =
                         let uu___3758_27835 = se2  in
                         let uu____27836 =
                           let uu____27839 =
                             FStar_List.filter
                               (fun uu___30_27853  ->
                                  match uu___30_27853 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27858;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27859;_},uu____27860);
                                      FStar_Syntax_Syntax.pos = uu____27861;
                                      FStar_Syntax_Syntax.vars = uu____27862;_}
                                      when
                                      let uu____27889 =
                                        let uu____27891 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27891
                                         in
                                      uu____27889 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27895 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27839
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___3758_27835.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3758_27835.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3758_27835.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3758_27835.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27836
                         }  in
                       uu____27834 :: se1 :: acc  in
                     forward uu____27831 sigelts1
                 | uu____27901 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27909 = forward [] sigelts  in (env1, uu____27909)
  
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let (desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____27974) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27978;
               FStar_Syntax_Syntax.exports = uu____27979;
               FStar_Syntax_Syntax.is_interface = uu____27980;_},FStar_Parser_AST.Module
             (current_lid,uu____27982)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27991) ->
              let uu____27994 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27994
           in
        let uu____27999 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28041 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28041, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28063 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28063, mname, decls, false)
           in
        match uu____27999 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28105 = desugar_decls env2 decls  in
            (match uu____28105 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____28173 =
            (FStar_Options.interactive ()) &&
              (let uu____28176 =
                 let uu____28178 =
                   let uu____28180 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28180  in
                 FStar_Util.get_file_extension uu____28178  in
               FStar_List.mem uu____28176 ["fsti"; "fsi"])
             in
          if uu____28173 then as_interface m else m  in
        let uu____28194 = desugar_modul_common curmod env m1  in
        match uu____28194 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28216 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28216, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28238 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28238 with
      | (env1,modul,pop_when_done) ->
          let uu____28255 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28255 with
           | (env2,modul1) ->
               ((let uu____28267 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28267
                 then
                   let uu____28270 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28270
                 else ());
                (let uu____28275 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28275, modul1))))
  
let with_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    FStar_Options.push ();
    (let res = f ()  in
     let light = FStar_Options.ml_ish ()  in
     FStar_Options.pop ();
     if light then FStar_Options.set_ml_ish () else ();
     res)
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      with_options
        (fun uu____28325  ->
           let uu____28326 = desugar_modul env modul  in
           match uu____28326 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28364  ->
           let uu____28365 = desugar_decls env decls  in
           match uu____28365 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28416  ->
             let uu____28417 = desugar_partial_modul modul env a_modul  in
             match uu____28417 with | (env1,modul1) -> (modul1, env1))
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____28512 ->
                  let t =
                    let uu____28522 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28522  in
                  let uu____28535 =
                    let uu____28536 = FStar_Syntax_Subst.compress t  in
                    uu____28536.FStar_Syntax_Syntax.n  in
                  (match uu____28535 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28548,uu____28549)
                       -> bs1
                   | uu____28574 -> failwith "Impossible")
               in
            let uu____28584 =
              let uu____28591 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28591
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28584 with
            | (binders,uu____28593,binders_opening) ->
                let erase_term t =
                  let uu____28601 =
                    let uu____28602 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28602  in
                  FStar_Syntax_Subst.close binders uu____28601  in
                let erase_tscheme uu____28620 =
                  match uu____28620 with
                  | (us,t) ->
                      let t1 =
                        let uu____28640 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28640 t  in
                      let uu____28643 =
                        let uu____28644 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28644  in
                      ([], uu____28643)
                   in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening
                     in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____28667 ->
                        let bs =
                          let uu____28677 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28677  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28717 =
                          let uu____28718 =
                            let uu____28721 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28721  in
                          uu____28718.FStar_Syntax_Syntax.n  in
                        (match uu____28717 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28723,uu____28724) -> bs1
                         | uu____28749 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28757 =
                      let uu____28758 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28758  in
                    FStar_Syntax_Subst.close binders uu____28757  in
                  let uu___3917_28759 = action  in
                  let uu____28760 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28761 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3917_28759.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3917_28759.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28760;
                    FStar_Syntax_Syntax.action_typ = uu____28761
                  }  in
                let uu___3919_28762 = ed  in
                let uu____28763 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28764 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28765 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28766 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28767 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28768 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28769 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28770 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28771 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28772 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28773 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28774 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28775 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28776 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28777 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28778 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3919_28762.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3919_28762.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28763;
                  FStar_Syntax_Syntax.signature = uu____28764;
                  FStar_Syntax_Syntax.ret_wp = uu____28765;
                  FStar_Syntax_Syntax.bind_wp = uu____28766;
                  FStar_Syntax_Syntax.if_then_else = uu____28767;
                  FStar_Syntax_Syntax.ite_wp = uu____28768;
                  FStar_Syntax_Syntax.stronger = uu____28769;
                  FStar_Syntax_Syntax.close_wp = uu____28770;
                  FStar_Syntax_Syntax.assert_p = uu____28771;
                  FStar_Syntax_Syntax.assume_p = uu____28772;
                  FStar_Syntax_Syntax.null_wp = uu____28773;
                  FStar_Syntax_Syntax.trivial = uu____28774;
                  FStar_Syntax_Syntax.repr = uu____28775;
                  FStar_Syntax_Syntax.return_repr = uu____28776;
                  FStar_Syntax_Syntax.bind_repr = uu____28777;
                  FStar_Syntax_Syntax.actions = uu____28778;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3919_28762.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3926_28794 = se  in
                  let uu____28795 =
                    let uu____28796 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28796  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28795;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3926_28794.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3926_28794.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3926_28794.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3926_28794.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___3932_28800 = se  in
                  let uu____28801 =
                    let uu____28802 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28802
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28801;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3932_28800.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3932_28800.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3932_28800.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3932_28800.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28804 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28805 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28805 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28822 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28822
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28824 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28824)
  