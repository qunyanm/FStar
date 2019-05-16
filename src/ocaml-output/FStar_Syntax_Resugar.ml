open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____15 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____15
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____23 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____23
  
let map_opt :
  'Auu____33 'Auu____34 .
    unit ->
      ('Auu____33 -> 'Auu____34 FStar_Pervasives_Native.option) ->
        'Auu____33 Prims.list -> 'Auu____34 Prims.list
  = fun uu____50  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____59 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____59
      then
        let uu____63 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____63
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____73 .
    ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_128  ->
            match uu___0_128 with
            | (uu____136,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____143,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____144)) -> false
            | (uu____149,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____150)) -> false
            | uu____156 -> true))
  
let filter_pattern_imp :
  'Auu____169 .
    ('Auu____169 * Prims.bool) Prims.list ->
      ('Auu____169 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____204  ->
         match uu____204 with
         | (uu____211,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe))
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____261 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____274 = FStar_Options.print_universes ()  in
    if uu____274
    then
      let uu____278 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____278 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r

and (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____342 ->
          let uu____343 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____343 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____354 =
                      let uu____355 =
                        let uu____356 =
                          let uu____368 = FStar_Util.string_of_int n1  in
                          (uu____368, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____356  in
                      FStar_Parser_AST.Const uu____355  in
                    mk1 uu____354 r
                | uu____381 ->
                    let e1 =
                      let uu____383 =
                        let uu____384 =
                          let uu____385 =
                            let uu____397 = FStar_Util.string_of_int n1  in
                            (uu____397, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____385  in
                        FStar_Parser_AST.Const uu____384  in
                      mk1 uu____383 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____411 =
                      let uu____412 =
                        let uu____419 = FStar_Ident.id_of_text "+"  in
                        (uu____419, [e1; e2])  in
                      FStar_Parser_AST.Op uu____412  in
                    mk1 uu____411 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____427 ->
               let t =
                 let uu____431 =
                   let uu____432 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____432  in
                 mk1 uu____431 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____441 =
                        let uu____442 =
                          let uu____449 = resugar_universe x r  in
                          (acc, uu____449, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____442  in
                      mk1 uu____441 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____451 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____463 =
              let uu____469 =
                let uu____471 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____471  in
              (uu____469, r)  in
            FStar_Ident.mk_ident uu____463  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___1_509 =
      match uu___1_509 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some ("+", FStar_Pervasives_Native.None)
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.parse_int "2")))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some ("/", FStar_Pervasives_Native.None)
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some ("<", FStar_Pervasives_Native.None)
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", FStar_Pervasives_Native.None)
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | uu____837 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".[||]<-", FStar_Pervasives_Native.None)
    | "op_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".(||)<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Access" ->
        FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
    | "op_Lens_Access" ->
        FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
    | uu____977 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____995 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____995 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1013 ->
               let op =
                 let uu____1019 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1073) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____1019
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string * expected_arity) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____1400 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1400 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1470 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          if FStar_Util.starts_with str "dtuple"
          then
            FStar_Pervasives_Native.Some
              ("dtuple", FStar_Pervasives_Native.None)
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some
                ("tuple", FStar_Pervasives_Native.None)
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", FStar_Pervasives_Native.None)
              else
                (let uu____1572 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1572
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1608 =
      let uu____1609 = FStar_Syntax_Subst.compress t  in
      uu____1609.FStar_Syntax_Syntax.n  in
    match uu____1608 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____1630 = string_to_op s  in
        (match uu____1630 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1670 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1687 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1704 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1715 -> true
    | uu____1717 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1738 ->
        let uu____1740 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1740
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1754 = may_shorten lid  in
      if uu____1754 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____1899 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1899  in
      let uu____1902 =
        let uu____1903 = FStar_Syntax_Subst.compress t  in
        uu____1903.FStar_Syntax_Syntax.n  in
      match uu____1902 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1906 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1931 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1931
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1934 =
              let uu____1937 = bv_as_unique_ident x  in [uu____1937]  in
            FStar_Ident.lid_of_ids uu____1934  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1940 =
              let uu____1943 = bv_as_unique_ident x  in [uu____1943]  in
            FStar_Ident.lid_of_ids uu____1940  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = (Prims.parse_int "0")
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____1962 =
              let uu____1963 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1963  in
            mk1 uu____1962
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix)
                  in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                  in
               match r with
               | fst1::snd1::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk1 (FStar_Parser_AST.Projector (l, r1))
               | uu____1987 -> failwith "wrong projector format")
            else
              (let uu____1994 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1998 =
                      let uu____2000 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____2000  in
                    let uu____2003 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1998 <> uu____2003)
                  in
               if uu____1994
               then
                 let uu____2008 =
                   let uu____2009 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2009  in
                 mk1 uu____2008
               else
                 (let uu____2012 =
                    let uu____2013 =
                      let uu____2024 = maybe_shorten_fv env fv  in
                      (uu____2024, [])  in
                    FStar_Parser_AST.Construct uu____2013  in
                  mk1 uu____2012))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2042 = FStar_Options.print_universes ()  in
          if uu____2042
          then
            let univs1 =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____2073 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2073  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2096 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____2104 = FStar_Syntax_Syntax.is_teff t  in
          if uu____2104
          then
            let uu____2107 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____2107
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____2112 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____2133 -> ("Type", true)  in
          (match uu____2112 with
           | (nm,needs_app) ->
               let typ =
                 let uu____2145 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____2145  in
               let uu____2146 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____2146
               then
                 let uu____2149 =
                   let uu____2150 =
                     let uu____2157 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____2157, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____2150  in
                 mk1 uu____2149
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____2162) ->
          let uu____2187 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____2187 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2203 = FStar_Options.print_implicits ()  in
                 if uu____2203 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____2241  ->
                         match uu____2241 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____2281 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____2281 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____2291 = FStar_Options.print_implicits ()  in
                 if uu____2291 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____2302 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____2302 FStar_List.rev  in
               let rec aux body3 uu___2_2327 =
                 match uu___2_2327 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____2343 =
            let uu____2348 =
              let uu____2349 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____2349]  in
            FStar_Syntax_Subst.open_term uu____2348 phi  in
          (match uu____2343 with
           | (x1,phi1) ->
               let b =
                 let uu____2371 =
                   let uu____2374 = FStar_List.hd x1  in
                   resugar_binder' env uu____2374 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____2371  in
               let uu____2381 =
                 let uu____2382 =
                   let uu____2387 = resugar_term' env phi1  in
                   (b, uu____2387)  in
                 FStar_Parser_AST.Refine uu____2382  in
               mk1 uu____2381)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2389;
             FStar_Syntax_Syntax.vars = uu____2390;_},(e,uu____2392)::[])
          when
          (let uu____2433 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____2433) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_2482 =
            match uu___3_2482 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____2552 -> failwith "last of an empty list"  in
          let rec last_two uu___4_2591 =
            match uu___4_2591 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____2623::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____2701::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2772  ->
                   match uu____2772 with
                   | (e2,qual) ->
                       let uu____2789 = resugar_term' env e2  in
                       let uu____2790 = resugar_imp env qual  in
                       (uu____2789, uu____2790)) args1
               in
            let uu____2791 = resugar_term' env e1  in
            match uu____2791 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____2828  ->
                       match uu____2828 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____2844 = FStar_Options.print_implicits ()  in
            if uu____2844 then args else filter_imp args  in
          let uu____2859 = resugar_term_as_op e  in
          (match uu____2859 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2872) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____2897  ->
                        match uu____2897 with
                        | (x,uu____2909) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____2918 =
                                   let uu____2919 =
                                     let uu____2920 =
                                       let uu____2927 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____2927, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____2920  in
                                   mk1 uu____2919  in
                                 FStar_Pervasives_Native.Some uu____2918))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____2931) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2957)::[] -> b
                 | uu____2974 -> failwith "wrong arguments to dtuple"  in
               let uu____2984 =
                 let uu____2985 = FStar_Syntax_Subst.compress body  in
                 uu____2985.FStar_Syntax_Syntax.n  in
               (match uu____2984 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2990) ->
                    let uu____3015 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____3015 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____3025 = FStar_Options.print_implicits ()
                              in
                           if uu____3025 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____3042 =
                           let uu____3043 =
                             let uu____3054 =
                               FStar_List.map
                                 (fun _3065  -> FStar_Util.Inl _3065) xs3
                                in
                             (uu____3054, body3)  in
                           FStar_Parser_AST.Sum uu____3043  in
                         mk1 uu____3042)
                | uu____3072 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____3095  ->
                              match uu____3095 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____3113) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____3122) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____3131 = FStar_List.hd args1  in
               (match uu____3131 with
                | (t1,uu____3145) ->
                    let uu____3150 =
                      let uu____3151 = FStar_Syntax_Subst.compress t1  in
                      uu____3151.FStar_Syntax_Syntax.n  in
                    (match uu____3150 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____3158 =
                           let uu____3159 =
                             let uu____3164 = resugar_term' env t1  in
                             (uu____3164, f)  in
                           FStar_Parser_AST.Project uu____3159  in
                         mk1 uu____3158
                     | uu____3165 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____3166) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____3190 =
                 match new_args with
                 | (a1,uu____3200)::(a2,uu____3202)::[] -> (a1, a2)
                 | uu____3229 -> failwith "wrong arguments to try_with"  in
               (match uu____3190 with
                | (body,handler) ->
                    let decomp term =
                      let uu____3251 =
                        let uu____3252 = FStar_Syntax_Subst.compress term  in
                        uu____3252.FStar_Syntax_Syntax.n  in
                      match uu____3251 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____3257) ->
                          let uu____3282 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____3282 with | (x1,e2) -> e2)
                      | uu____3289 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____3292 = decomp body  in
                      resugar_term' env uu____3292  in
                    let handler1 =
                      let uu____3294 = decomp handler  in
                      resugar_term' env uu____3294  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____3302,uu____3303,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____3335,uu____3336,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____3373 =
                            let uu____3374 =
                              let uu____3383 = resugar_body t11  in
                              (uu____3383, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____3374  in
                          mk1 uu____3373
                      | uu____3386 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____3444 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____3474) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3483) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____3504) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists
                     (x,uu____3569,(uu____3570,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall
                     (x,uu____3606,(uu____3607,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____3642 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____3655 =
                   let uu____3656 = FStar_Syntax_Subst.compress body  in
                   uu____3656.FStar_Syntax_Syntax.n  in
                 match uu____3655 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____3661) ->
                     let uu____3686 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____3686 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____3696 = FStar_Options.print_implicits ()
                               in
                            if uu____3696 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____3712 =
                            let uu____3725 =
                              let uu____3726 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____3726.FStar_Syntax_Syntax.n  in
                            match uu____3725 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____3748 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (attr,uu____3774,pats) ->
                                      let uu____3812 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3856  ->
                                                     match uu____3856 with
                                                     | (e2,uu____3864) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (attr, uu____3812, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____3882 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      (FStar_Pervasives_Native.None, [],
                                        uu____3882)
                                  | uu____3893 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____3748 with
                                 | (attr,pats,body4) -> (attr, pats, body4))
                            | uu____3940 ->
                                let uu____3941 = resugar_term' env body2  in
                                (FStar_Pervasives_Native.None, [],
                                  uu____3941)
                             in
                          (match uu____3712 with
                           | (attr,pats,body3) ->
                               let uu____3965 = uncurry xs3 pats body3  in
                               (match uu____3965 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____4003 =
                                        let uu____4004 =
                                          let uu____4027 =
                                            let uu____4038 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____4038, pats1)  in
                                          (xs5, attr, uu____4027, body4)  in
                                        FStar_Parser_AST.QForall uu____4004
                                         in
                                      mk1 uu____4003
                                    else
                                      (let uu____4063 =
                                         let uu____4064 =
                                           let uu____4087 =
                                             let uu____4098 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____4098, pats1)  in
                                           (xs5, attr, uu____4087, body4)  in
                                         FStar_Parser_AST.QExists uu____4064
                                          in
                                       mk1 uu____4063))))
                 | uu____4121 ->
                     if op = "forall"
                     then
                       let uu____4125 =
                         let uu____4126 =
                           let uu____4149 = resugar_term' env body  in
                           ([], FStar_Pervasives_Native.None, ([], []),
                             uu____4149)
                            in
                         FStar_Parser_AST.QForall uu____4126  in
                       mk1 uu____4125
                     else
                       (let uu____4174 =
                          let uu____4175 =
                            let uu____4198 = resugar_term' env body  in
                            ([], FStar_Pervasives_Native.None, ([], []),
                              uu____4198)
                             in
                          FStar_Parser_AST.QExists uu____4175  in
                        mk1 uu____4174)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____4239)::[] -> resugar b
                  | uu____4256 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____4268) ->
               let uu____4276 = FStar_List.hd args1  in
               (match uu____4276 with
                | (e1,uu____4290) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____4362  ->
                         match uu____4362 with
                         | (e1,qual) ->
                             let uu____4379 = resugar_term' env e1  in
                             let uu____4380 = resugar_imp env qual  in
                             (uu____4379, uu____4380)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____4396 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____4396 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____4444 =
                               let uu____4445 =
                                 let uu____4452 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____4452)  in
                               FStar_Parser_AST.Op uu____4445  in
                             mk1 uu____4444  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____4470  ->
                                  match uu____4470 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____4489 =
                      let uu____4490 =
                        let uu____4497 =
                          let uu____4500 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____4500
                           in
                        (op1, uu____4497)  in
                      FStar_Parser_AST.Op uu____4490  in
                    mk1 uu____4489
                | uu____4513 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____4582 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____4582 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____4628 =
                   let uu____4641 =
                     let uu____4646 = resugar_pat' env pat1 branch_bv  in
                     let uu____4647 = resugar_term' env e  in
                     (uu____4646, uu____4647)  in
                   (FStar_Pervasives_Native.None, uu____4641)  in
                 [uu____4628]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____4699,t1)::(pat2,uu____4702,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4798 =
            let uu____4799 =
              let uu____4806 = resugar_term' env e  in
              let uu____4807 = resugar_term' env t1  in
              let uu____4808 = resugar_term' env t2  in
              (uu____4806, uu____4807, uu____4808)  in
            FStar_Parser_AST.If uu____4799  in
          mk1 uu____4798
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____4874 =
            match uu____4874 with
            | (pat,wopt,b) ->
                let uu____4916 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____4916 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4968 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____4968
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____4972 =
            let uu____4973 =
              let uu____4988 = resugar_term' env e  in
              let uu____4989 = FStar_List.map resugar_branch branches  in
              (uu____4988, uu____4989)  in
            FStar_Parser_AST.Match uu____4973  in
          mk1 uu____4972
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____5035) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____5104 =
            let uu____5105 =
              let uu____5114 = resugar_term' env e  in
              (uu____5114, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____5105  in
          mk1 uu____5104
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____5143 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____5143 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____5197 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____5197
                    in
                 let uu____5204 =
                   let uu____5209 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____5209
                    in
                 match uu____5204 with
                 | (univs1,td) ->
                     let uu____5229 =
                       let uu____5236 =
                         let uu____5237 = FStar_Syntax_Subst.compress td  in
                         uu____5237.FStar_Syntax_Syntax.n  in
                       match uu____5236 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____5246,(t1,uu____5248)::(d,uu____5250)::[])
                           -> (t1, d)
                       | uu____5307 -> failwith "wrong let binding format"
                        in
                     (match uu____5229 with
                      | (typ,def) ->
                          let uu____5338 =
                            let uu____5354 =
                              let uu____5355 =
                                FStar_Syntax_Subst.compress def  in
                              uu____5355.FStar_Syntax_Syntax.n  in
                            match uu____5354 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____5375) ->
                                let uu____5400 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____5400 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____5431 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____5431
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____5454 -> ([], def, false)  in
                          (match uu____5338 with
                           | (binders,term,is_pat_app) ->
                               let uu____5509 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____5520 =
                                       let uu____5521 =
                                         let uu____5522 =
                                           let uu____5529 =
                                             bv_as_unique_ident bv  in
                                           (uu____5529,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____5522
                                          in
                                       mk_pat uu____5521  in
                                     (uu____5520, term)
                                  in
                               (match uu____5509 with
                                | (pat,term1) ->
                                    let uu____5551 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____5594  ->
                                                  match uu____5594 with
                                                  | (bv,q) ->
                                                      let uu____5609 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____5609
                                                        (fun q1  ->
                                                           let uu____5621 =
                                                             let uu____5622 =
                                                               let uu____5629
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____5629,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____5622
                                                              in
                                                           mk_pat uu____5621)))
                                           in
                                        let uu____5632 =
                                          let uu____5637 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5637)
                                           in
                                        let uu____5640 =
                                          universe_to_string univs1  in
                                        (uu____5632, uu____5640)
                                      else
                                        (let uu____5649 =
                                           let uu____5654 =
                                             resugar_term' env term1  in
                                           (pat, uu____5654)  in
                                         let uu____5655 =
                                           universe_to_string univs1  in
                                         (uu____5649, uu____5655))
                                       in
                                    (attrs_opt, uu____5551))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____5761 =
                   match uu____5761 with
                   | (attrs,(pb,univs1)) ->
                       let uu____5821 =
                         let uu____5823 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____5823  in
                       if uu____5821
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____5904) ->
          let s =
            let uu____5923 =
              let uu____5925 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____5925 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____5923  in
          let uu____5930 = mk1 FStar_Parser_AST.Wild  in label s uu____5930
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____5938 =
            let uu____5939 =
              let uu____5944 = resugar_term' env tm  in (uu____5944, qi1)  in
            FStar_Parser_AST.Quote uu____5939  in
          mk1 uu____5938
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___5_5956 =
            match uu___5_5956 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5964,(uu____5965,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____6026 =
                        let uu____6027 =
                          let uu____6036 = resugar_seq t11  in
                          (uu____6036, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____6027  in
                      mk1 uu____6026
                  | uu____6039 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____6040,uu____6041,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____6109  ->
                         match uu____6109 with
                         | (x,uu____6117) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____6122 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____6140,t1) ->
               resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6180 = FStar_Options.print_universes ()  in
               if uu____6180
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6244 = FStar_Options.print_universes ()  in
               if uu____6244
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____6288 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____6288, FStar_Parser_AST.Nothing)  in
          let uu____6289 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____6289
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____6312 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____6312
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____6397 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____6397, (FStar_Pervasives_Native.snd post))  in
                    let uu____6408 =
                      let uu____6417 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____6417 then [] else [pre]  in
                    let uu____6452 =
                      let uu____6461 =
                        let uu____6470 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____6470 then [] else [pats]  in
                      FStar_List.append [post1] uu____6461  in
                    FStar_List.append uu____6408 uu____6452
                | uu____6529 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____6563  ->
                   match uu____6563 with
                   | (e,uu____6575) ->
                       let uu____6580 = resugar_term' env e  in
                       (uu____6580, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___6_6605 =
              match uu___6_6605 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____6638 = resugar_term' env e  in
                         (uu____6638, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____6643 -> aux l tl1)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))

and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____6690 = b  in
        match uu____6690 with
        | (x,aq) ->
            let uu____6699 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____6699
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____6713 =
                       let uu____6714 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____6714  in
                     FStar_Parser_AST.mk_binder uu____6713 r
                       FStar_Parser_AST.Type_level imp
                 | uu____6715 ->
                     let uu____6716 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____6716
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____6721 =
                          let uu____6722 =
                            let uu____6727 = bv_as_unique_ident x  in
                            (uu____6727, e)  in
                          FStar_Parser_AST.Annotated uu____6722  in
                        FStar_Parser_AST.mk_binder uu____6721 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun v1  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk1 a =
              let uu____6747 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____6747  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____6751 =
                if used
                then
                  let uu____6753 =
                    let uu____6760 = bv_as_unique_ident v1  in
                    (uu____6760, aqual)  in
                  FStar_Parser_AST.PatVar uu____6753
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____6751  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____6767;
                  FStar_Syntax_Syntax.vars = uu____6768;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____6778 = FStar_Options.print_bound_var_types ()  in
                if uu____6778
                then
                  let uu____6781 =
                    let uu____6782 =
                      let uu____6793 =
                        let uu____6800 = resugar_term' env typ  in
                        (uu____6800, FStar_Pervasives_Native.None)  in
                      (pat, uu____6793)  in
                    FStar_Parser_AST.PatAscribed uu____6782  in
                  mk1 uu____6781
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____6821 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____6821
            (fun aqual  ->
               let uu____6833 =
                 let uu____6838 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _6849  -> FStar_Pervasives_Native.Some _6849)
                   uu____6838
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____6833)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____6911 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____6911) &&
            (let uu____6914 =
               FStar_List.existsML
                 (fun uu____6927  ->
                    match uu____6927 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____6949)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____6954 -> false
                          | uu____6956 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____6914)
           in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____7024 = may_drop_implicits args  in
            if uu____7024 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____7049  ->
                 match uu____7049 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____7104 =
                  let uu____7106 =
                    let uu____7108 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____7108  in
                  Prims.op_Negation uu____7106  in
                if uu____7104
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____7152 = filter_pattern_imp args  in
              (match uu____7152 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____7202 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____7202 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7221 =
                       let uu____7227 =
                         let uu____7229 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7229
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7227)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7221);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7282  ->
                        match uu____7282 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7299 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____7299)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7307;
                 FStar_Syntax_Syntax.fv_delta = uu____7308;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____7337 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____7337 FStar_List.rev  in
              let args1 =
                let uu____7353 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7373  ->
                          match uu____7373 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____7353 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____7451 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____7451
                | (hd1::tl1,hd2::tl2) ->
                    let uu____7474 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____7474
                 in
              let args2 =
                let uu____7492 = map21 fields1 args1  in
                FStar_All.pipe_right uu____7492 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____7536 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____7536 with
               | FStar_Pervasives_Native.Some (op,uu____7548) ->
                   let uu____7565 =
                     let uu____7566 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____7566  in
                   mk1 uu____7565
               | FStar_Pervasives_Native.None  ->
                   let uu____7576 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____7576 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____7581 ->
              let uu____7582 =
                let uu____7583 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____7583  in
              mk1 uu____7582
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

and (resugar_arg_qual :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
          if b
          then FStar_Pervasives_Native.None
          else
            FStar_Pervasives_Native.Some
              (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7623 =
            let uu____7626 =
              let uu____7627 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____7627  in
            FStar_Pervasives_Native.Some uu____7626  in
          FStar_Pervasives_Native.Some uu____7623

and (resugar_imp :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.imp)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> FStar_Parser_AST.Hash
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____7639 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____7639

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___7_7647  ->
    match uu___7_7647 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____7654 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____7655 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____7656 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____7661 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____7670 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____7679 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___8_7685  ->
    match uu___8_7685 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon))
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____7728,datacons) ->
            let uu____7738 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____7766,uu____7767,uu____7768,inductive_lid,uu____7770,uu____7771)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____7778 -> failwith "unexpected"))
               in
            (match uu____7738 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____7799 = FStar_Options.print_implicits ()  in
                   if uu____7799 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____7816 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___9_7823  ->
                             match uu___9_7823 with
                             | FStar_Syntax_Syntax.RecordType uu____7825 ->
                                 true
                             | uu____7835 -> false))
                      in
                   if uu____7816
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____7889,univs1,term,uu____7892,num,uu____7894)
                           ->
                           let uu____7901 =
                             let uu____7902 =
                               FStar_Syntax_Subst.compress term  in
                             uu____7902.FStar_Syntax_Syntax.n  in
                           (match uu____7901 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____7916)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____7985  ->
                                          match uu____7985 with
                                          | (b,qual) ->
                                              let uu____8006 =
                                                bv_as_unique_ident b  in
                                              let uu____8007 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____8006, uu____8007,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____8018 -> failwith "unexpected")
                       | uu____8030 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     FStar_Parser_AST.TyconRecord
                       ((tylid.FStar_Ident.ident), bs2,
                         FStar_Pervasives_Native.None, fields)
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs1,term,uu____8161,num,uu____8163) ->
                            let c =
                              let uu____8184 =
                                let uu____8187 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____8187  in
                              ((l.FStar_Ident.ident), uu____8184,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____8207 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____8287 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
  
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____8313 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____8313;
          FStar_Parser_AST.attrs = []
        }
  
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____8343 = ts  in
        match uu____8343 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____8356 =
              let uu____8357 =
                let uu____8374 =
                  let uu____8383 =
                    let uu____8390 =
                      let uu____8391 =
                        let uu____8404 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____8404)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____8391  in
                    (uu____8390, FStar_Pervasives_Native.None)  in
                  [uu____8383]  in
                (false, false, uu____8374)  in
              FStar_Parser_AST.Tycon uu____8357  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8356
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tscheme" ts 
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun for_free  ->
      fun r  ->
        fun q  ->
          fun ed  ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params
                 in
              let uu____8493 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____8493 with
              | (bs,action_defn) ->
                  let uu____8500 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____8500 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____8510 = FStar_Options.print_implicits ()
                            in
                         if uu____8510
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____8520 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____8520 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____8537 =
                             let uu____8548 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____8548,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____8537  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None, t)),
                                   FStar_Pervasives_Native.None)]))
                       else
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None,
                                       action_defn1)),
                                   FStar_Pervasives_Native.None)])))
               in
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____8632 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____8632 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____8642 = FStar_Options.print_implicits ()  in
                  if uu____8642 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____8652 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____8652 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.bind_wp
                   in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else
                   in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp
                   in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger
                   in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp
                   in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p
                   in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p
                   in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr))
                   in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr
                   in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr
                   in
                let mandatory_members_decls =
                  if for_free
                  then [repr; return_repr; bind_repr]
                  else
                    [repr;
                    return_repr;
                    bind_repr;
                    ret_wp;
                    bind_wp;
                    if_then_else1;
                    ite_wp;
                    stronger;
                    close_wp;
                    assert_p;
                    assume_p;
                    null_wp;
                    trivial]
                   in
                let actions =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                    (FStar_List.map (fun a  -> resugar_action a false))
                   in
                let decls = FStar_List.append mandatory_members_decls actions
                   in
                mk_decl r q
                  (FStar_Parser_AST.NewEffect
                     (FStar_Parser_AST.DefineEffect
                        (eff_name, eff_binders2, eff_typ1, decls)))
  
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8737) ->
          let uu____8746 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____8769 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____8787 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____8795 -> false
                    | uu____8812 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____8746 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____8850 se1 =
                 match uu____8850 with
                 | (datacon_ses1,tycons) ->
                     let uu____8876 = resugar_typ env datacon_ses1 se1  in
                     (match uu____8876 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____8891 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____8891 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____8926 =
                           let uu____8927 =
                             let uu____8928 =
                               let uu____8945 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____8945)  in
                             FStar_Parser_AST.Tycon uu____8928  in
                           decl'_to_decl se uu____8927  in
                         FStar_Pervasives_Native.Some uu____8926
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____8980,uu____8981,uu____8982,uu____8983,uu____8984)
                              ->
                              let uu____8991 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____8991
                          | uu____8994 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____8998 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9005) ->
          let uu____9010 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9018  ->
                    match uu___10_9018 with
                    | FStar_Syntax_Syntax.Projector (uu____9020,uu____9021)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9023 -> true
                    | uu____9025 -> false))
             in
          if uu____9010
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))  in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____9060) ->
                 let uu____9089 =
                   let uu____9090 =
                     let uu____9091 =
                       let uu____9102 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____9102)  in
                     FStar_Parser_AST.TopLevelLet uu____9091  in
                   decl'_to_decl se uu____9090  in
                 FStar_Pervasives_Native.Some uu____9089
             | uu____9139 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____9144,fml) ->
          let uu____9146 =
            let uu____9147 =
              let uu____9148 =
                let uu____9153 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____9153)  in
              FStar_Parser_AST.Assume uu____9148  in
            decl'_to_decl se uu____9147  in
          FStar_Pervasives_Native.Some uu____9146
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9155 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9155
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____9158 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____9158
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9168,t) ->
                let uu____9178 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9178
            | uu____9179 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9187,t) ->
                let uu____9197 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____9197
            | uu____9198 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9222 -> failwith "Should not happen hopefully"  in
          let uu____9232 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____9232
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____9242 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____9242 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____9254 = FStar_Options.print_implicits ()  in
                 if uu____9254 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____9270 =
                 let uu____9271 =
                   let uu____9272 =
                     let uu____9289 =
                       let uu____9298 =
                         let uu____9305 =
                           let uu____9306 =
                             let uu____9319 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____9319)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____9306  in
                         (uu____9305, FStar_Pervasives_Native.None)  in
                       [uu____9298]  in
                     (false, false, uu____9289)  in
                   FStar_Parser_AST.Tycon uu____9272  in
                 decl'_to_decl se uu____9271  in
               FStar_Pervasives_Native.Some uu____9270)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9351 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____9351
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____9355 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___11_9363  ->
                    match uu___11_9363 with
                    | FStar_Syntax_Syntax.Projector (uu____9365,uu____9366)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9368 -> true
                    | uu____9370 -> false))
             in
          if uu____9355
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9378 =
                 (let uu____9382 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____9382) || (FStar_List.isEmpty uvs)
                  in
               if uu____9378
               then resugar_term' env t
               else
                 (let uu____9387 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____9387 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____9396 = resugar_term' env t1  in
                      label universes uu____9396)
                in
             let uu____9397 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____9397)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____9404 =
            let uu____9405 =
              let uu____9406 =
                let uu____9413 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____9418 = resugar_term' env t  in
                (uu____9413, uu____9418)  in
              FStar_Parser_AST.Splice uu____9406  in
            decl'_to_decl se uu____9405  in
          FStar_Pervasives_Native.Some uu____9404
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9421 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9438 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____9454 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____9478 = noenv resugar_term'  in uu____9478 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____9496 = noenv resugar_sigelt'  in uu____9496 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____9514 = noenv resugar_comp'  in uu____9514 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____9537 = noenv resugar_pat'  in uu____9537 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____9571 = noenv resugar_binder'  in uu____9571 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____9596 = noenv resugar_tscheme'  in uu____9596 ts 
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____9631 = noenv resugar_eff_decl'  in
          uu____9631 for_free r q ed
  