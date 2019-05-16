open Prims
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then y else x 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then x else y 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____103 = let uu____106 = f x  in uu____106 :: acc  in
            aux xs uu____103
         in
      aux l []
  
let rec map_if_all :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____173 = f x  in
            (match uu____173 with
             | FStar_Pervasives_Native.Some r -> aux xs (r :: acc)
             | FStar_Pervasives_Native.None  -> [])
         in
      let r = aux l []  in
      if (FStar_List.length l) = (FStar_List.length r)
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
  
let rec all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f  ->
    fun l  ->
      match l with
      | [] -> true
      | x::xs ->
          let uu____229 = f x  in if uu____229 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___0_262  ->
         match uu___0_262 with
         | (uu____268,FStar_Parser_AST.Nothing ) -> true
         | uu____270 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____299 'Auu____300 .
    Prims.bool -> ('Auu____299 -> 'Auu____300) -> 'Auu____299 -> 'Auu____300
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app  in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
  
let (str : Prims.string -> FStar_Pprint.document) =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____410 'Auu____411 .
    'Auu____410 ->
      ('Auu____411 -> 'Auu____410) ->
        'Auu____411 FStar_Pervasives_Native.option -> 'Auu____410
  =
  fun n1  ->
    fun f  ->
      fun x  ->
        match x with
        | FStar_Pervasives_Native.None  -> n1
        | FStar_Pervasives_Native.Some x' -> f x'
  
let (prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
  
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
  
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
  
let (infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1") 
let (infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1") 
let (break1 : FStar_Pprint.document) =
  FStar_Pprint.break_ (Prims.parse_int "1") 
let separate_break_map :
  'Auu____524 .
    FStar_Pprint.document ->
      ('Auu____524 -> FStar_Pprint.document) ->
        'Auu____524 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____549 =
          let uu____550 =
            let uu____551 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____551  in
          FStar_Pprint.separate_map uu____550 f l  in
        FStar_Pprint.group uu____549
  
let precede_break_separate_map :
  'Auu____563 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____563 -> FStar_Pprint.document) ->
          'Auu____563 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____593 =
            let uu____594 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____595 =
              let uu____596 = FStar_List.hd l  in
              FStar_All.pipe_right uu____596 f  in
            FStar_Pprint.precede uu____594 uu____595  in
          let uu____597 =
            let uu____598 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____604 =
                   let uu____605 =
                     let uu____606 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____606  in
                   FStar_Pprint.op_Hat_Hat sep uu____605  in
                 FStar_Pprint.op_Hat_Hat break1 uu____604) uu____598
             in
          FStar_Pprint.op_Hat_Hat uu____593 uu____597
  
let concat_break_map :
  'Auu____614 .
    ('Auu____614 -> FStar_Pprint.document) ->
      'Auu____614 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____634 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____638 = f x  in FStar_Pprint.op_Hat_Hat uu____638 break1)
          l
         in
      FStar_Pprint.group uu____634
  
let (parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    let uu____701 = str "begin"  in
    let uu____703 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____701 contents uu____703
  
let separate_map_last :
  'Auu____716 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____716 -> FStar_Pprint.document) ->
        'Auu____716 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.separate sep es1
  
let separate_break_map_last :
  'Auu____768 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____768 -> FStar_Pprint.document) ->
        'Auu____768 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____800 =
          let uu____801 =
            let uu____802 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____802  in
          separate_map_last uu____801 f l  in
        FStar_Pprint.group uu____800
  
let separate_map_or_flow :
  'Auu____812 .
    FStar_Pprint.document ->
      ('Auu____812 -> FStar_Pprint.document) ->
        'Auu____812 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____850 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____850 -> FStar_Pprint.document) ->
        'Auu____850 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.flow sep es1
  
let separate_map_or_flow_last :
  'Auu____902 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____902 -> FStar_Pprint.document) ->
        'Auu____902 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let (separate_or_flow :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun sep  -> fun l  -> separate_map_or_flow sep FStar_Pervasives.id l 
let (surround_maybe_empty :
  Prims.int ->
    Prims.int ->
      FStar_Pprint.document ->
        FStar_Pprint.document ->
          FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun n1  ->
    fun b  ->
      fun doc1  ->
        fun doc2  ->
          fun doc3  ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____984 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____984
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1006 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1006 -> FStar_Pprint.document) ->
                  'Auu____1006 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____1065 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1065
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1085 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1085 -> FStar_Pprint.document) ->
                  'Auu____1085 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____1144 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1144
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____1163  ->
    match uu____1163 with
    | (comment,keywords) ->
        let uu____1197 =
          let uu____1198 =
            let uu____1201 = str comment  in
            let uu____1202 =
              let uu____1205 =
                let uu____1208 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1219  ->
                       match uu____1219 with
                       | (k,v1) ->
                           let uu____1232 =
                             let uu____1235 = str k  in
                             let uu____1236 =
                               let uu____1239 =
                                 let uu____1242 = str v1  in [uu____1242]  in
                               FStar_Pprint.rarrow :: uu____1239  in
                             uu____1235 :: uu____1236  in
                           FStar_Pprint.concat uu____1232) keywords
                   in
                [uu____1208]  in
              FStar_Pprint.space :: uu____1205  in
            uu____1201 :: uu____1202  in
          FStar_Pprint.concat uu____1198  in
        FStar_Pprint.group uu____1197
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1252 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1268 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1268
      | uu____1271 -> false
  
let (is_tuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_tuple_data_lid' 
let (is_dtuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_dtuple_data_lid' 
let (is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool)
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____1322::(e2,uu____1324)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1347 -> false  in
      aux
  
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let (is_lex_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (uu____1371,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1382,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1403 = extract_from_list e2  in e1 :: uu____1403
    | uu____1406 ->
        let uu____1407 =
          let uu____1409 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1409  in
        failwith uu____1407
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1423;
           FStar_Parser_AST.level = uu____1424;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1426 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1438;
           FStar_Parser_AST.level = uu____1439;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1441;
                                                         FStar_Parser_AST.level
                                                           = uu____1442;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1444;
                                                    FStar_Parser_AST.level =
                                                      uu____1445;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.set_singleton)
          &&
          (FStar_Ident.lid_equals maybe_addr_of_lid
             FStar_Parser_Const.heap_addr_of_lid)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____1447;
                FStar_Parser_AST.level = uu____1448;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1450;
           FStar_Parser_AST.level = uu____1451;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1453 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1465 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1466;
           FStar_Parser_AST.range = uu____1467;
           FStar_Parser_AST.level = uu____1468;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1469;
                                                         FStar_Parser_AST.range
                                                           = uu____1470;
                                                         FStar_Parser_AST.level
                                                           = uu____1471;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1473;
                                                    FStar_Parser_AST.level =
                                                      uu____1474;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1475;
                FStar_Parser_AST.range = uu____1476;
                FStar_Parser_AST.level = uu____1477;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1479;
           FStar_Parser_AST.level = uu____1480;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1482 = extract_from_ref_set e1  in
        let uu____1485 = extract_from_ref_set e2  in
        FStar_List.append uu____1482 uu____1485
    | uu____1488 ->
        let uu____1489 =
          let uu____1491 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1491  in
        failwith uu____1489
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1503 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1503
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1512 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1512
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1523 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1523 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1533 = FStar_Ident.text_of_id op  in uu____1533 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1603 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1623 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1634 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1645 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1671  ->
    match uu___1_1671 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_1706  ->
      match uu___2_1706 with
      | FStar_Util.Inl c ->
          let uu____1719 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1719 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1735 .
    Prims.string ->
      ('Auu____1735 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1759  ->
      match uu____1759 with
      | (assoc_levels,tokens) ->
          let uu____1791 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1791 <> FStar_Pervasives_Native.None
  
let (opinfix4 : associativity_level) = (Right, [FStar_Util.Inr "**"]) 
let (opinfix3 : associativity_level) =
  (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37]) 
let (opinfix2 : associativity_level) =
  (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let (minus_lvl : associativity_level) = (Left, [FStar_Util.Inr "-"]) 
let (opinfix1 : associativity_level) =
  (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let (pipe_right : associativity_level) = (Left, [FStar_Util.Inr "|>"]) 
let (opinfix0d : associativity_level) = (Left, [FStar_Util.Inl 36]) 
let (opinfix0c : associativity_level) =
  (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62]) 
let (equal : associativity_level) = (Left, [FStar_Util.Inr "="]) 
let (opinfix0b : associativity_level) = (Left, [FStar_Util.Inl 38]) 
let (opinfix0a : associativity_level) = (Left, [FStar_Util.Inl 124]) 
let (colon_equals : associativity_level) = (NonAssoc, [FStar_Util.Inr ":="]) 
let (amp : associativity_level) = (Right, [FStar_Util.Inr "&"]) 
let (colon_colon : associativity_level) = (Right, [FStar_Util.Inr "::"]) 
let (level_associativity_spec : associativity_level Prims.list) =
  [opinfix4;
  opinfix3;
  opinfix2;
  opinfix1;
  pipe_right;
  opinfix0d;
  opinfix0c;
  opinfix0b;
  opinfix0a;
  colon_equals;
  amp;
  colon_colon] 
let (level_table :
  ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list) =
  let levels_from_associativity l uu___3_1963 =
    match uu___3_1963 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2013  ->
         match uu____2013 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2088 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2088 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2140) ->
          assoc_levels
      | uu____2178 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2211 . ('Auu____2211 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2260 =
        FStar_List.tryFind
          (fun uu____2296  ->
             match uu____2296 with
             | (uu____2313,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2260 with
      | FStar_Pervasives_Native.Some ((uu____2342,l1,uu____2344),uu____2345)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2395 =
            let uu____2397 =
              let uu____2399 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2399  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2397
             in
          failwith uu____2395
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2434 = assign_levels level_associativity_spec op  in
    match uu____2434 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2493 =
      let uu____2496 =
        let uu____2502 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2502  in
      FStar_List.tryFind uu____2496 operatorInfix0ad12  in
    uu____2493 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2569 =
      let uu____2584 =
        let uu____2602 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2602  in
      FStar_List.tryFind uu____2584 opinfix34  in
    uu____2569 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2668 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2668
    then (Prims.parse_int "1")
    else
      (let uu____2681 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2681
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2727 . FStar_Ident.ident -> 'Auu____2727 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _2743 when _2743 = (Prims.parse_int "0") -> true
      | _2745 when _2745 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2747 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2747 ["-"; "~"])
      | _2755 when _2755 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2757 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2757
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _2779 when _2779 = (Prims.parse_int "3") ->
          let uu____2780 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2780 [".()<-"; ".[]<-"]
      | uu____2788 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2834 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2886 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2928 -> true
      | uu____2934 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2967 = FStar_List.for_all is_binder_annot bs  in
          if uu____2967
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____2982 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____2987 = all_binders e (Prims.parse_int "0")  in
    match uu____2987 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3026 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3026
  
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool ;
  has_fsdoc: Prims.bool ;
  is_fsdoc: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> r
  
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_attrs
  
let (__proj__Mkdecl_meta__item__has_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_fsdoc
  
let (__proj__Mkdecl_meta__item__is_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> is_fsdoc
  
let (dummy_meta : decl_meta) =
  {
    r = FStar_Range.dummyRange;
    has_qs = false;
    has_attrs = false;
    has_fsdoc = false;
    is_fsdoc = false
  } 
let with_comment :
  'Auu____3175 .
    ('Auu____3175 -> FStar_Pprint.document) ->
      'Auu____3175 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3217 = FStar_ST.op_Bang comment_stack  in
          match uu____3217 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3288 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3288 FStar_Pprint.hardline  in
              let uu____3289 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3289
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3331 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3331 print_pos lookahead_pos))
              else
                (let uu____3334 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3334))
           in
        let uu____3337 =
          let uu____3343 =
            let uu____3344 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3344  in
          let uu____3345 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3343 uu____3345  in
        match uu____3337 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3354 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3354
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3366 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3366)
  
let with_comment_sep :
  'Auu____3378 'Auu____3379 .
    ('Auu____3378 -> 'Auu____3379) ->
      'Auu____3378 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3379)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3425 = FStar_ST.op_Bang comment_stack  in
          match uu____3425 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3496 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3496
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3538 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3542 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3542)
                     in
                  comments_before_pos uu____3538 print_pos lookahead_pos))
              else
                (let uu____3545 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3545))
           in
        let uu____3548 =
          let uu____3554 =
            let uu____3555 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3555  in
          let uu____3556 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3554 uu____3556  in
        match uu____3548 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3569 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3569
              else comments  in
            (comments1, printed_e)
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta ->
          FStar_Pprint.document ->
            Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos  ->
        fun meta_decl  ->
          fun doc1  ->
            fun r  ->
              fun init1  ->
                let uu____3622 = FStar_ST.op_Bang comment_stack  in
                match uu____3622 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3716 =
                          let uu____3718 =
                            let uu____3720 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3720  in
                          uu____3718 - lbegin  in
                        max k uu____3716  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3725 =
                          let uu____3726 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3727 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3726 uu____3727  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3725  in
                      let uu____3728 =
                        let uu____3730 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3730  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3728 pos meta_decl doc2 true init1))
                | uu____3733 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3746 = FStar_Range.line_of_pos pos  in
                         uu____3746 - lbegin  in
                       let lnum1 = min (Prims.parse_int "3") lnum  in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - (Prims.parse_int "1")
                         else lnum1  in
                       let lnum3 = max k lnum2  in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.parse_int "2")
                         else lnum3  in
                       let lnum5 =
                         if (Prims.op_Negation r) && meta_decl.has_fsdoc
                         then min (Prims.parse_int "2") lnum4
                         else lnum4  in
                       let lnum6 =
                         if r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc)
                         then (Prims.parse_int "1")
                         else lnum5  in
                       let lnum7 =
                         if init1 then (Prims.parse_int "2") else lnum6  in
                       let uu____3788 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3788)
  
let separate_map_with_comments :
  'Auu____3802 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3802 -> FStar_Pprint.document) ->
          'Auu____3802 Prims.list ->
            ('Auu____3802 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3861 x =
              match uu____3861 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3880 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3880 meta_decl doc1 false false
                     in
                  let uu____3884 =
                    let uu____3886 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3886  in
                  let uu____3887 =
                    let uu____3888 =
                      let uu____3889 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3889  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3888  in
                  (uu____3884, uu____3887)
               in
            let uu____3891 =
              let uu____3898 = FStar_List.hd xs  in
              let uu____3899 = FStar_List.tl xs  in (uu____3898, uu____3899)
               in
            match uu____3891 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3917 =
                    let uu____3919 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3919  in
                  let uu____3920 =
                    let uu____3921 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3921  in
                  (uu____3917, uu____3920)  in
                let uu____3923 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3923
  
let separate_map_with_comments_kw :
  'Auu____3950 'Auu____3951 .
    'Auu____3950 ->
      'Auu____3950 ->
        ('Auu____3950 -> 'Auu____3951 -> FStar_Pprint.document) ->
          'Auu____3951 Prims.list ->
            ('Auu____3951 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4015 x =
              match uu____4015 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4034 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4034 meta_decl doc1 false false
                     in
                  let uu____4038 =
                    let uu____4040 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4040  in
                  let uu____4041 =
                    let uu____4042 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4042  in
                  (uu____4038, uu____4041)
               in
            let uu____4044 =
              let uu____4051 = FStar_List.hd xs  in
              let uu____4052 = FStar_List.tl xs  in (uu____4051, uu____4052)
               in
            match uu____4044 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4070 =
                    let uu____4072 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4072  in
                  let uu____4073 = f prefix1 x  in (uu____4070, uu____4073)
                   in
                let uu____4075 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4075
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5067)) ->
          let uu____5070 =
            let uu____5072 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5072 FStar_Util.is_upper  in
          if uu____5070
          then
            let uu____5078 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5078 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5081 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5088 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5091 =
      let uu____5092 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5093 =
        let uu____5094 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5094  in
      FStar_Pprint.op_Hat_Hat uu____5092 uu____5093  in
    FStar_Pprint.op_Hat_Hat uu____5088 uu____5091

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5096 ->
        let uu____5097 =
          let uu____5098 = str "@ "  in
          let uu____5100 =
            let uu____5101 =
              let uu____5102 =
                let uu____5103 =
                  let uu____5104 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5104  in
                FStar_Pprint.op_Hat_Hat uu____5103 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5102  in
            FStar_Pprint.op_Hat_Hat uu____5101 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5098 uu____5100  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5097

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5107  ->
    match uu____5107 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5155 =
                match uu____5155 with
                | (kwd,arg) ->
                    let uu____5168 = str "@"  in
                    let uu____5170 =
                      let uu____5171 = str kwd  in
                      let uu____5172 =
                        let uu____5173 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5173
                         in
                      FStar_Pprint.op_Hat_Hat uu____5171 uu____5172  in
                    FStar_Pprint.op_Hat_Hat uu____5168 uu____5170
                 in
              let uu____5174 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5174 FStar_Pprint.hardline
           in
        let uu____5181 =
          let uu____5182 =
            let uu____5183 =
              let uu____5184 = str doc1  in
              let uu____5185 =
                let uu____5186 =
                  let uu____5187 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5187  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5186  in
              FStar_Pprint.op_Hat_Hat uu____5184 uu____5185  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5183  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5182  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5181

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5191 =
          let uu____5192 = str "val"  in
          let uu____5194 =
            let uu____5195 =
              let uu____5196 = p_lident lid  in
              let uu____5197 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5196 uu____5197  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5195  in
          FStar_Pprint.op_Hat_Hat uu____5192 uu____5194  in
        let uu____5198 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5191 uu____5198
    | FStar_Parser_AST.TopLevelLet (uu____5201,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5226 =
               let uu____5227 = str "let"  in p_letlhs uu____5227 lb false
                in
             FStar_Pprint.group uu____5226) lbs
    | uu____5230 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_5245 =
          match uu___4_5245 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5253 = f x  in
              let uu____5254 =
                let uu____5255 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5255  in
              FStar_Pprint.op_Hat_Hat uu____5253 uu____5254
           in
        let uu____5256 = str "["  in
        let uu____5258 =
          let uu____5259 = p_list' l  in
          let uu____5260 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5259 uu____5260  in
        FStar_Pprint.op_Hat_Hat uu____5256 uu____5258

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5264 =
          let uu____5265 = str "open"  in
          let uu____5267 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5265 uu____5267  in
        FStar_Pprint.group uu____5264
    | FStar_Parser_AST.Include uid ->
        let uu____5269 =
          let uu____5270 = str "include"  in
          let uu____5272 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5270 uu____5272  in
        FStar_Pprint.group uu____5269
    | FStar_Parser_AST.Friend uid ->
        let uu____5274 =
          let uu____5275 = str "friend"  in
          let uu____5277 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5275 uu____5277  in
        FStar_Pprint.group uu____5274
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5280 =
          let uu____5281 = str "module"  in
          let uu____5283 =
            let uu____5284 =
              let uu____5285 = p_uident uid1  in
              let uu____5286 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5285 uu____5286  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5284  in
          FStar_Pprint.op_Hat_Hat uu____5281 uu____5283  in
        let uu____5287 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5280 uu____5287
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5289 =
          let uu____5290 = str "module"  in
          let uu____5292 =
            let uu____5293 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5293  in
          FStar_Pprint.op_Hat_Hat uu____5290 uu____5292  in
        FStar_Pprint.group uu____5289
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5294,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5331 = str "effect"  in
          let uu____5333 =
            let uu____5334 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5334  in
          FStar_Pprint.op_Hat_Hat uu____5331 uu____5333  in
        let uu____5335 =
          let uu____5336 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5336 FStar_Pprint.equals
           in
        let uu____5339 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5335 uu____5339
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5370 =
          let uu____5371 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5371  in
        let uu____5384 =
          let uu____5385 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5423 =
                    let uu____5424 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5424 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5423)) uu____5385
           in
        FStar_Pprint.op_Hat_Hat uu____5370 uu____5384
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5441 = str "let"  in
          let uu____5443 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5441 uu____5443  in
        let uu____5444 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5444 p_letbinding lbs
          (fun uu____5454  ->
             match uu____5454 with
             | (p,t) ->
                 let uu____5461 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5461;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5467 =
          let uu____5468 = str "val"  in
          let uu____5470 =
            let uu____5471 =
              let uu____5472 = p_lident lid  in
              let uu____5473 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5472 uu____5473  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5471  in
          FStar_Pprint.op_Hat_Hat uu____5468 uu____5470  in
        FStar_All.pipe_left FStar_Pprint.group uu____5467
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5478 =
            let uu____5480 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5480 FStar_Util.is_upper  in
          if uu____5478
          then FStar_Pprint.empty
          else
            (let uu____5488 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5488 FStar_Pprint.space)
           in
        let uu____5490 =
          let uu____5491 = p_ident id1  in
          let uu____5492 =
            let uu____5493 =
              let uu____5494 =
                let uu____5495 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5495  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5494  in
            FStar_Pprint.group uu____5493  in
          FStar_Pprint.op_Hat_Hat uu____5491 uu____5492  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5490
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5504 = str "exception"  in
        let uu____5506 =
          let uu____5507 =
            let uu____5508 = p_uident uid  in
            let uu____5509 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5513 =
                     let uu____5514 = str "of"  in
                     let uu____5516 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5514 uu____5516  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5513) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5508 uu____5509  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5507  in
        FStar_Pprint.op_Hat_Hat uu____5504 uu____5506
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5520 = str "new_effect"  in
        let uu____5522 =
          let uu____5523 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5523  in
        FStar_Pprint.op_Hat_Hat uu____5520 uu____5522
    | FStar_Parser_AST.SubEffect se ->
        let uu____5525 = str "sub_effect"  in
        let uu____5527 =
          let uu____5528 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5528  in
        FStar_Pprint.op_Hat_Hat uu____5525 uu____5527
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5531 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5533,uu____5534) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5562 = str "%splice"  in
        let uu____5564 =
          let uu____5565 =
            let uu____5566 = str ";"  in p_list p_uident uu____5566 ids  in
          let uu____5568 =
            let uu____5569 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5569  in
          FStar_Pprint.op_Hat_Hat uu____5565 uu____5568  in
        FStar_Pprint.op_Hat_Hat uu____5562 uu____5564

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5572  ->
    match uu___5_5572 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5575 = str "#set-options"  in
        let uu____5577 =
          let uu____5578 =
            let uu____5579 = str s  in FStar_Pprint.dquotes uu____5579  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5578  in
        FStar_Pprint.op_Hat_Hat uu____5575 uu____5577
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5584 = str "#reset-options"  in
        let uu____5586 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5592 =
                 let uu____5593 = str s  in FStar_Pprint.dquotes uu____5593
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5592) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5584 uu____5586
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5598 = str "#push-options"  in
        let uu____5600 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5606 =
                 let uu____5607 = str s  in FStar_Pprint.dquotes uu____5607
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5606) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5598 uu____5600
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5638  ->
      match uu____5638 with
      | (typedecl,fsdoc_opt) ->
          let uu____5651 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5651 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5676 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5676
               else
                 (let uu____5679 =
                    let uu____5680 =
                      let uu____5681 =
                        let uu____5682 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5682 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5681  in
                    let uu____5683 =
                      let uu____5684 =
                        let uu____5685 =
                          let uu____5686 =
                            let uu____5687 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5687  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5686
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5685
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5684  in
                    FStar_Pprint.ifflat uu____5680 uu____5683  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5679))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5690  ->
      match uu___6_5690 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5719 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5719, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5736 = p_typ_sep false false t  in
          (match uu____5736 with
           | (comm,doc1) ->
               let uu____5756 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5756, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5812 =
            match uu____5812 with
            | (lid1,t,doc_opt) ->
                let uu____5829 =
                  let uu____5834 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5834
                   in
                (match uu____5829 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5852 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5852  in
          let uu____5861 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5861, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5928 =
            match uu____5928 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5957 =
                    let uu____5958 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5958  in
                  FStar_Range.extend_to_end_of_line uu____5957  in
                let uu____5963 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5963 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6002 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6002, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6007  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6007 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6042 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6042  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6044 =
                        let uu____6047 =
                          let uu____6050 = p_fsdoc fsdoc  in
                          let uu____6051 =
                            let uu____6054 = cont lid_doc  in [uu____6054]
                             in
                          uu____6050 :: uu____6051  in
                        kw :: uu____6047  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6044
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6061 =
                        let uu____6062 =
                          let uu____6063 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6063 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6062
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6061
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6083 =
                          let uu____6084 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6084  in
                        prefix2 uu____6083 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6086  ->
      match uu____6086 with
      | (lid,t,doc_opt) ->
          let uu____6103 =
            let uu____6104 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6105 =
              let uu____6106 = p_lident lid  in
              let uu____6107 =
                let uu____6108 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6108  in
              FStar_Pprint.op_Hat_Hat uu____6106 uu____6107  in
            FStar_Pprint.op_Hat_Hat uu____6104 uu____6105  in
          FStar_Pprint.group uu____6103

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6110  ->
    match uu____6110 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6144 =
            let uu____6145 =
              let uu____6146 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6146  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6145  in
          FStar_Pprint.group uu____6144  in
        let uu____6147 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6148 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6152 =
                 let uu____6153 =
                   let uu____6154 =
                     let uu____6155 =
                       let uu____6156 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6156
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6155  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6154  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6153  in
               FStar_Pprint.group uu____6152) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6147 uu____6148

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6160  ->
      fun inner_let  ->
        match uu____6160 with
        | (pat,uu____6168) ->
            let uu____6169 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6221 =
                    let uu____6228 =
                      let uu____6233 =
                        let uu____6234 =
                          let uu____6235 =
                            let uu____6236 = str "by"  in
                            let uu____6238 =
                              let uu____6239 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6239
                               in
                            FStar_Pprint.op_Hat_Hat uu____6236 uu____6238  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6235
                           in
                        FStar_Pprint.group uu____6234  in
                      (t, uu____6233)  in
                    FStar_Pervasives_Native.Some uu____6228  in
                  (pat1, uu____6221)
              | uu____6250 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6169 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6276);
                         FStar_Parser_AST.prange = uu____6277;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6294 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6294 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6300 =
                        if inner_let
                        then
                          let uu____6314 = pats_as_binders_if_possible pats
                             in
                          match uu____6314 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6337 = pats_as_binders_if_possible pats
                              in
                           match uu____6337 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6300 with
                       | (terms,style) ->
                           let uu____6364 =
                             let uu____6365 =
                               let uu____6366 =
                                 let uu____6367 = p_lident lid  in
                                 let uu____6368 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6367
                                   uu____6368
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6366
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6365  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6364)
                  | uu____6371 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6379 =
                              let uu____6380 =
                                let uu____6381 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6381
                                 in
                              FStar_Pprint.group uu____6380  in
                            FStar_Pprint.op_Hat_Hat uu____6379 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6392 =
                        let uu____6393 =
                          let uu____6394 =
                            let uu____6395 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6395  in
                          FStar_Pprint.group uu____6394  in
                        FStar_Pprint.op_Hat_Hat uu____6393 ascr_doc  in
                      FStar_Pprint.group uu____6392))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6397  ->
      match uu____6397 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6406 = p_term_sep false false e  in
          (match uu____6406 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6416 =
                 let uu____6417 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6417  in
               let uu____6418 =
                 let uu____6419 =
                   let uu____6420 =
                     let uu____6421 =
                       let uu____6422 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6422
                        in
                     FStar_Pprint.group uu____6421  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6420  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6419  in
               FStar_Pprint.ifflat uu____6416 uu____6418)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_6423  ->
    match uu___7_6423 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls

and (p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____6448 = p_uident uid  in
        let uu____6449 = p_binders true bs  in
        let uu____6451 =
          let uu____6452 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6452  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6448 uu____6449 uu____6451

and (p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let binders = p_binders true bs  in
          let uu____6467 =
            let uu____6468 =
              let uu____6469 =
                let uu____6470 = p_uident uid  in
                let uu____6471 = p_binders true bs  in
                let uu____6473 =
                  let uu____6474 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6474  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6470 uu____6471 uu____6473
                 in
              FStar_Pprint.group uu____6469  in
            let uu____6479 =
              let uu____6480 = str "with"  in
              let uu____6482 =
                let uu____6483 =
                  let uu____6484 =
                    let uu____6485 =
                      let uu____6486 =
                        let uu____6487 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6487
                         in
                      separate_map_last uu____6486 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6485  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6484  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6483  in
              FStar_Pprint.op_Hat_Hat uu____6480 uu____6482  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6468 uu____6479  in
          braces_with_nesting uu____6467

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6491,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6524 =
            let uu____6525 = p_lident lid  in
            let uu____6526 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6525 uu____6526  in
          let uu____6527 = p_simpleTerm ps false e  in
          prefix2 uu____6524 uu____6527
      | uu____6529 ->
          let uu____6530 =
            let uu____6532 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6532
             in
          failwith uu____6530

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6615 =
        match uu____6615 with
        | (kwd,t) ->
            let uu____6626 =
              let uu____6627 = str kwd  in
              let uu____6628 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6627 uu____6628  in
            let uu____6629 = p_simpleTerm ps false t  in
            prefix2 uu____6626 uu____6629
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6636 =
      let uu____6637 =
        let uu____6638 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6639 =
          let uu____6640 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6640  in
        FStar_Pprint.op_Hat_Hat uu____6638 uu____6639  in
      let uu____6642 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6637 uu____6642  in
    let uu____6643 =
      let uu____6644 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6644  in
    FStar_Pprint.op_Hat_Hat uu____6636 uu____6643

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6645  ->
    match uu___8_6645 with
    | FStar_Parser_AST.Private  -> str "private"
    | FStar_Parser_AST.Abstract  -> str "abstract"
    | FStar_Parser_AST.Noeq  -> str "noeq"
    | FStar_Parser_AST.Unopteq  -> str "unopteq"
    | FStar_Parser_AST.Assumption  -> str "assume"
    | FStar_Parser_AST.DefaultEffect  -> str "default"
    | FStar_Parser_AST.TotalEffect  -> str "total"
    | FStar_Parser_AST.Effect_qual  -> FStar_Pprint.empty
    | FStar_Parser_AST.New  -> str "new"
    | FStar_Parser_AST.Inline  -> str "inline"
    | FStar_Parser_AST.Visible  -> FStar_Pprint.empty
    | FStar_Parser_AST.Unfold_for_unification_and_vcgen  -> str "unfold"
    | FStar_Parser_AST.Inline_for_extraction  -> str "inline_for_extraction"
    | FStar_Parser_AST.Irreducible  -> str "irreducible"
    | FStar_Parser_AST.NoExtract  -> str "noextract"
    | FStar_Parser_AST.Reifiable  -> str "reifiable"
    | FStar_Parser_AST.Reflectable  -> str "reflectable"
    | FStar_Parser_AST.Opaque  -> str "opaque"
    | FStar_Parser_AST.Logic  -> str "logic"

and (p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document) =
  fun qs  ->
    match qs with
    | [] -> FStar_Pprint.empty
    | q::[] ->
        let uu____6665 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6665 FStar_Pprint.hardline
    | uu____6666 ->
        let uu____6667 =
          let uu____6668 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6668  in
        FStar_Pprint.op_Hat_Hat uu____6667 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6671  ->
    match uu___9_6671 with
    | FStar_Parser_AST.Rec  ->
        let uu____6672 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6672
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6674  ->
    match uu___10_6674 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6679,e) -> e
          | uu____6685 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6686 = str "#["  in
        let uu____6688 =
          let uu____6689 = p_term false false t1  in
          let uu____6692 =
            let uu____6693 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6693 break1  in
          FStar_Pprint.op_Hat_Hat uu____6689 uu____6692  in
        FStar_Pprint.op_Hat_Hat uu____6686 uu____6688

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6699 =
          let uu____6700 =
            let uu____6701 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6701  in
          FStar_Pprint.separate_map uu____6700 p_tuplePattern pats  in
        FStar_Pprint.group uu____6699
    | uu____6702 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6711 =
          let uu____6712 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6712 p_constructorPattern pats  in
        FStar_Pprint.group uu____6711
    | uu____6713 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6716;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6721 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6722 = p_constructorPattern hd1  in
        let uu____6723 = p_constructorPattern tl1  in
        infix0 uu____6721 uu____6722 uu____6723
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6725;_},pats)
        ->
        let uu____6731 = p_quident uid  in
        let uu____6732 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6731 uu____6732
    | uu____6733 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6749;
               FStar_Parser_AST.blevel = uu____6750;
               FStar_Parser_AST.aqual = uu____6751;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6760 =
               let uu____6761 = p_ident lid  in
               p_refinement aqual uu____6761 t1 phi  in
             soft_parens_with_nesting uu____6760
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6764;
               FStar_Parser_AST.blevel = uu____6765;
               FStar_Parser_AST.aqual = uu____6766;_},phi))
             ->
             let uu____6772 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6772
         | uu____6773 ->
             let uu____6778 =
               let uu____6779 = p_tuplePattern pat  in
               let uu____6780 =
                 let uu____6781 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6781
                  in
               FStar_Pprint.op_Hat_Hat uu____6779 uu____6780  in
             soft_parens_with_nesting uu____6778)
    | FStar_Parser_AST.PatList pats ->
        let uu____6785 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6785 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6804 =
          match uu____6804 with
          | (lid,pat) ->
              let uu____6811 = p_qlident lid  in
              let uu____6812 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6811 uu____6812
           in
        let uu____6813 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6813
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6825 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6826 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6827 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6825 uu____6826 uu____6827
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6838 =
          let uu____6839 =
            let uu____6840 =
              let uu____6841 = FStar_Ident.text_of_id op  in str uu____6841
               in
            let uu____6843 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6840 uu____6843  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6839  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6838
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6847 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6847 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6855 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6856 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6855 uu____6856
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6858 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6862;
           FStar_Parser_AST.prange = uu____6863;_},uu____6864)
        ->
        let uu____6869 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6869
    | FStar_Parser_AST.PatTuple (uu____6870,false ) ->
        let uu____6877 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6877
    | uu____6878 ->
        let uu____6879 =
          let uu____6881 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6881  in
        failwith uu____6879

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6886;_},uu____6887)
        -> true
    | uu____6894 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6900) -> true
    | uu____6902 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6909 = p_binder' is_atomic b  in
      match uu____6909 with
      | (b',t',catf) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf b' typ
           | FStar_Pervasives_Native.None  -> b')

and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document * FStar_Pprint.document
        FStar_Pervasives_Native.option * catf))
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____6946 =
            let uu____6947 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6948 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6947 uu____6948  in
          (uu____6946, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6954 = p_lident lid  in
          (uu____6954, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6961 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6972;
                   FStar_Parser_AST.blevel = uu____6973;
                   FStar_Parser_AST.aqual = uu____6974;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6979 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6979 t1 phi
            | uu____6980 ->
                let t' =
                  let uu____6982 = is_typ_tuple t  in
                  if uu____6982
                  then
                    let uu____6985 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6985
                  else p_tmFormula t  in
                let uu____6988 =
                  let uu____6989 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6990 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6989 uu____6990  in
                (uu____6988, t')
             in
          (match uu____6961 with
           | (b',t') ->
               let catf =
                 let uu____7008 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7008
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7015 =
                         let uu____7016 =
                           let uu____7017 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7017
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7016
                          in
                       FStar_Pprint.group uu____7015
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7022 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7022)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7027 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7055;
                  FStar_Parser_AST.blevel = uu____7056;
                  FStar_Parser_AST.aqual = uu____7057;_},phi)
               ->
               let uu____7061 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7061 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7082 ->
               if is_atomic
               then
                 let uu____7094 = p_atomicTerm t  in
                 (uu____7094, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7101 = p_appTerm t  in
                  (uu____7101, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7112 = p_refinement' aqual_opt binder t phi  in
          match uu____7112 with | (b,typ) -> cat_with_colon b typ

and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____7128 -> false
            | FStar_Parser_AST.App uu____7140 -> false
            | FStar_Parser_AST.Op uu____7148 -> false
            | uu____7156 -> true  in
          let uu____7158 = p_noSeqTerm false false phi  in
          match uu____7158 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7175 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7175)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7184 =
                let uu____7185 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7185 binder  in
              let uu____7186 =
                let uu____7187 = p_appTerm t  in
                let uu____7188 =
                  let uu____7189 =
                    let uu____7190 =
                      let uu____7191 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7192 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7191 uu____7192  in
                    FStar_Pprint.group uu____7190  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7189
                   in
                FStar_Pprint.op_Hat_Hat uu____7187 uu____7188  in
              (uu____7184, uu____7186)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7206 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7206

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7210 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7213 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7213)
       in
    if uu____7210
    then FStar_Pprint.underscore
    else (let uu____7218 = FStar_Ident.text_of_id lid  in str uu____7218)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7221 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7224 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7224)
       in
    if uu____7221
    then FStar_Pprint.underscore
    else (let uu____7229 = FStar_Ident.text_of_lid lid  in str uu____7229)

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  = fun b  -> if b then soft_parens_with_nesting else (fun x  -> x)

and (inline_comment_or_above :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun comm  ->
    fun doc1  ->
      fun sep  ->
        if comm = FStar_Pprint.empty
        then
          let uu____7250 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7250
        else
          (let uu____7253 =
             let uu____7254 =
               let uu____7255 =
                 let uu____7256 =
                   let uu____7257 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7257  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7256  in
               FStar_Pprint.group uu____7255  in
             let uu____7258 =
               let uu____7259 =
                 let uu____7260 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7260  in
               FStar_Pprint.op_Hat_Hat comm uu____7259  in
             FStar_Pprint.ifflat uu____7254 uu____7258  in
           FStar_All.pipe_left FStar_Pprint.group uu____7253)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7268 = p_noSeqTerm true false e1  in
            (match uu____7268 with
             | (comm,t1) ->
                 let uu____7277 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7278 =
                   let uu____7279 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7279
                    in
                 FStar_Pprint.op_Hat_Hat uu____7277 uu____7278)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7283 =
              let uu____7284 =
                let uu____7285 =
                  let uu____7286 = p_lident x  in
                  let uu____7287 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7286 uu____7287  in
                let uu____7288 =
                  let uu____7289 = p_noSeqTermAndComment true false e1  in
                  let uu____7292 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7289 uu____7292  in
                op_Hat_Slash_Plus_Hat uu____7285 uu____7288  in
              FStar_Pprint.group uu____7284  in
            let uu____7293 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7283 uu____7293
        | uu____7294 ->
            let uu____7295 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7295

and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7307 = p_noSeqTerm true false e1  in
            (match uu____7307 with
             | (comm,t1) ->
                 let uu____7320 =
                   let uu____7321 =
                     let uu____7322 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7322  in
                   let uu____7323 =
                     let uu____7324 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7324
                      in
                   FStar_Pprint.op_Hat_Hat uu____7321 uu____7323  in
                 (comm, uu____7320))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7328 =
              let uu____7329 =
                let uu____7330 =
                  let uu____7331 =
                    let uu____7332 = p_lident x  in
                    let uu____7333 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7332 uu____7333  in
                  let uu____7334 =
                    let uu____7335 = p_noSeqTermAndComment true false e1  in
                    let uu____7338 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7335 uu____7338  in
                  op_Hat_Slash_Plus_Hat uu____7331 uu____7334  in
                FStar_Pprint.group uu____7330  in
              let uu____7339 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7329 uu____7339  in
            (FStar_Pprint.empty, uu____7328)
        | uu____7340 -> p_noSeqTerm ps pb e

and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTermAndComment :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____7360 =
              let uu____7361 = p_tmIff e1  in
              let uu____7362 =
                let uu____7363 =
                  let uu____7364 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7364
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7363  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7361 uu____7362  in
            FStar_Pprint.group uu____7360
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7370 =
              let uu____7371 = p_tmIff e1  in
              let uu____7372 =
                let uu____7373 =
                  let uu____7374 =
                    let uu____7375 = p_typ false false t  in
                    let uu____7378 =
                      let uu____7379 = str "by"  in
                      let uu____7381 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7379 uu____7381  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7375 uu____7378  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7374
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7373  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7371 uu____7372  in
            FStar_Pprint.group uu____7370
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7382;_},e1::e2::e3::[])
            ->
            let uu____7389 =
              let uu____7390 =
                let uu____7391 =
                  let uu____7392 = p_atomicTermNotQUident e1  in
                  let uu____7393 =
                    let uu____7394 =
                      let uu____7395 =
                        let uu____7396 = p_term false false e2  in
                        soft_parens_with_nesting uu____7396  in
                      let uu____7399 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7395 uu____7399  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7394  in
                  FStar_Pprint.op_Hat_Hat uu____7392 uu____7393  in
                FStar_Pprint.group uu____7391  in
              let uu____7400 =
                let uu____7401 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7401  in
              FStar_Pprint.op_Hat_Hat uu____7390 uu____7400  in
            FStar_Pprint.group uu____7389
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7402;_},e1::e2::e3::[])
            ->
            let uu____7409 =
              let uu____7410 =
                let uu____7411 =
                  let uu____7412 = p_atomicTermNotQUident e1  in
                  let uu____7413 =
                    let uu____7414 =
                      let uu____7415 =
                        let uu____7416 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7416  in
                      let uu____7419 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7415 uu____7419  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7414  in
                  FStar_Pprint.op_Hat_Hat uu____7412 uu____7413  in
                FStar_Pprint.group uu____7411  in
              let uu____7420 =
                let uu____7421 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7421  in
              FStar_Pprint.op_Hat_Hat uu____7410 uu____7420  in
            FStar_Pprint.group uu____7409
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7431 =
              let uu____7432 = str "requires"  in
              let uu____7434 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7432 uu____7434  in
            FStar_Pprint.group uu____7431
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7444 =
              let uu____7445 = str "ensures"  in
              let uu____7447 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7445 uu____7447  in
            FStar_Pprint.group uu____7444
        | FStar_Parser_AST.Attributes es ->
            let uu____7451 =
              let uu____7452 = str "attributes"  in
              let uu____7454 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7452 uu____7454  in
            FStar_Pprint.group uu____7451
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7459 =
                let uu____7460 =
                  let uu____7461 = str "if"  in
                  let uu____7463 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7461 uu____7463  in
                let uu____7466 =
                  let uu____7467 = str "then"  in
                  let uu____7469 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7467 uu____7469  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7460 uu____7466  in
              FStar_Pprint.group uu____7459
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7473,uu____7474,e31) when
                     is_unit e31 ->
                     let uu____7476 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7476
                 | uu____7479 -> p_noSeqTermAndComment false false e2  in
               let uu____7482 =
                 let uu____7483 =
                   let uu____7484 = str "if"  in
                   let uu____7486 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7484 uu____7486  in
                 let uu____7489 =
                   let uu____7490 =
                     let uu____7491 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7491 e2_doc  in
                   let uu____7493 =
                     let uu____7494 = str "else"  in
                     let uu____7496 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7494 uu____7496  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7490 uu____7493  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7483 uu____7489  in
               FStar_Pprint.group uu____7482)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7519 =
              let uu____7520 =
                let uu____7521 =
                  let uu____7522 = str "try"  in
                  let uu____7524 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7522 uu____7524  in
                let uu____7527 =
                  let uu____7528 = str "with"  in
                  let uu____7530 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7528 uu____7530  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7521 uu____7527  in
              FStar_Pprint.group uu____7520  in
            let uu____7539 = paren_if (ps || pb)  in uu____7539 uu____7519
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7566 =
              let uu____7567 =
                let uu____7568 =
                  let uu____7569 = str "match"  in
                  let uu____7571 = p_noSeqTermAndComment false false e1  in
                  let uu____7574 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7569 uu____7571 uu____7574
                   in
                let uu____7578 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7568 uu____7578  in
              FStar_Pprint.group uu____7567  in
            let uu____7587 = paren_if (ps || pb)  in uu____7587 uu____7566
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7594 =
              let uu____7595 =
                let uu____7596 =
                  let uu____7597 = str "let open"  in
                  let uu____7599 = p_quident uid  in
                  let uu____7600 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7597 uu____7599 uu____7600
                   in
                let uu____7604 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7596 uu____7604  in
              FStar_Pprint.group uu____7595  in
            let uu____7606 = paren_if ps  in uu____7606 uu____7594
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7671 is_last =
              match uu____7671 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7705 =
                          let uu____7706 = str "let"  in
                          let uu____7708 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7706 uu____7708
                           in
                        FStar_Pprint.group uu____7705
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7711 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7717 = p_term_sep false false e2  in
                  (match uu____7717 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7727 =
                         if is_last
                         then
                           let uu____7729 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7730 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7729 doc_expr1
                             uu____7730
                         else
                           (let uu____7736 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7736)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7727)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7787 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7787
                     else
                       (let uu____7792 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7792)) lbs
               in
            let lbs_doc =
              let uu____7796 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7796  in
            let uu____7797 =
              let uu____7798 =
                let uu____7799 =
                  let uu____7800 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7800
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7799  in
              FStar_Pprint.group uu____7798  in
            let uu____7802 = paren_if ps  in uu____7802 uu____7797
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7809;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7812;
                                                             FStar_Parser_AST.level
                                                               = uu____7813;_})
            when matches_var maybe_x x ->
            let uu____7840 =
              let uu____7841 =
                let uu____7842 = str "function"  in
                let uu____7844 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7842 uu____7844  in
              FStar_Pprint.group uu____7841  in
            let uu____7853 = paren_if (ps || pb)  in uu____7853 uu____7840
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7859 =
              let uu____7860 = str "quote"  in
              let uu____7862 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7860 uu____7862  in
            FStar_Pprint.group uu____7859
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7864 =
              let uu____7865 = str "`"  in
              let uu____7867 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7865 uu____7867  in
            FStar_Pprint.group uu____7864
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7869 =
              let uu____7870 = str "`%"  in
              let uu____7872 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7870 uu____7872  in
            FStar_Pprint.group uu____7869
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7874;
              FStar_Parser_AST.level = uu____7875;_}
            ->
            let uu____7876 =
              let uu____7877 = str "`@"  in
              let uu____7879 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7877 uu____7879  in
            FStar_Pprint.group uu____7876
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7881 =
              let uu____7882 = str "`#"  in
              let uu____7884 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7882 uu____7884  in
            FStar_Pprint.group uu____7881
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7893 = str "calc"  in
              let uu____7895 =
                let uu____7896 =
                  let uu____7897 = p_noSeqTermAndComment false false rel  in
                  let uu____7900 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7897 uu____7900  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7896  in
              FStar_Pprint.op_Hat_Hat uu____7893 uu____7895  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7902 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7903 =
              let uu____7904 =
                let uu____7905 =
                  let uu____7906 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7909 =
                    let uu____7910 = str ";"  in
                    let uu____7912 =
                      let uu____7913 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7913
                       in
                    FStar_Pprint.op_Hat_Hat uu____7910 uu____7912  in
                  FStar_Pprint.op_Hat_Hat uu____7906 uu____7909  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7905  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____7904
               in
            FStar_Pprint.enclose head1 uu____7902 uu____7903
        | uu____7915 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7916  ->
    fun uu____7917  ->
      match uu____7917 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7922 =
            let uu____7923 = p_noSeqTermAndComment false false rel  in
            let uu____7926 =
              let uu____7927 =
                let uu____7928 =
                  let uu____7929 =
                    let uu____7930 = p_noSeqTermAndComment false false just
                       in
                    let uu____7933 =
                      let uu____7934 =
                        let uu____7935 =
                          let uu____7936 =
                            let uu____7937 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7940 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7937 uu____7940  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7936
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7935
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7934
                       in
                    FStar_Pprint.op_Hat_Hat uu____7930 uu____7933  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7929  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7928  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7927  in
            FStar_Pprint.op_Hat_Hat uu____7923 uu____7926  in
          FStar_Pprint.group uu____7922

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7942  ->
    match uu___11_7942 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7954 =
          let uu____7955 = str "[@"  in
          let uu____7957 =
            let uu____7958 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7959 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7958 uu____7959  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7955 uu____7957  in
        FStar_Pprint.group uu____7954

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,attr,(uu____7978,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8016 =
                   let uu____8017 =
                     let uu____8018 =
                       let uu____8019 =
                         let uu____8020 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8020
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8019 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8023 = p_quantifier_attr attr  in
                     prefix2 uu____8018 uu____8023  in
                   FStar_Pprint.group uu____8017  in
                 prefix2 uu____8016 term_doc
             | pats ->
                 let uu____8029 =
                   let uu____8030 =
                     let uu____8031 =
                       let uu____8032 =
                         let uu____8033 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8033
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8032 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8036 = p_trigger trigger  in
                     prefix2 uu____8031 uu____8036  in
                   FStar_Pprint.group uu____8030  in
                 prefix2 uu____8029 term_doc)
        | FStar_Parser_AST.QExists (bs,attr,(uu____8039,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8077 =
                   let uu____8078 =
                     let uu____8079 =
                       let uu____8080 =
                         let uu____8081 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8081
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8080 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8084 = p_quantifier_attr attr  in
                     prefix2 uu____8079 uu____8084  in
                   FStar_Pprint.group uu____8078  in
                 prefix2 uu____8077 term_doc
             | pats ->
                 let uu____8090 =
                   let uu____8091 =
                     let uu____8092 =
                       let uu____8093 =
                         let uu____8094 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8094
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8093 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8097 = p_trigger trigger  in
                     prefix2 uu____8092 uu____8097  in
                   FStar_Pprint.group uu____8091  in
                 prefix2 uu____8090 term_doc)
        | uu____8098 -> p_simpleTerm ps pb e

and (p_typ_top :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  ->
      fun pb  ->
        fun e  ->
          with_comment (p_typ_top' style ps pb) e e.FStar_Parser_AST.range

and (p_typ_top' :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  -> fun pb  -> fun e  -> p_tmArrow style true p_tmFormula e

and (sig_as_binders_if_possible :
  FStar_Parser_AST.term -> Prims.bool -> FStar_Pprint.document) =
  fun t  ->
    fun extra_space  ->
      let s = if extra_space then FStar_Pprint.space else FStar_Pprint.empty
         in
      let uu____8119 = all_binders_annot t  in
      if uu____8119
      then
        let uu____8122 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8122
      else
        (let uu____8133 =
           let uu____8134 =
             let uu____8135 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8135  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8134  in
         FStar_Pprint.group uu____8133)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8194 = x  in
      match uu____8194 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8259 = hd1  in
               (match uu____8259 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8331 = cb  in
      match uu____8331 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8350 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8356 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8356) hd1 tl1
                  in
               cat_with_colon uu____8350 typ)
       in
    let binders = FStar_List.fold_left fold_fun [] (FStar_List.rev pats)  in
    map_rev p_collapsed_binder binders

and (pats_as_binders_if_possible :
  FStar_Parser_AST.pattern Prims.list ->
    (FStar_Pprint.document Prims.list * annotation_style))
  =
  fun pats  ->
    let all_binders p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None ))
          ->
          (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
           | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
              ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                 FStar_Parser_AST.brange = uu____8435;
                 FStar_Parser_AST.blevel = uu____8436;
                 FStar_Parser_AST.aqual = uu____8437;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8446 =
                 let uu____8451 = p_ident lid  in
                 p_refinement' aqual uu____8451 t1 phi  in
               FStar_Pervasives_Native.Some uu____8446
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8458) ->
               let uu____8463 =
                 let uu____8468 =
                   let uu____8469 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8470 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8469 uu____8470  in
                 let uu____8471 = p_tmEqNoRefinement t  in
                 (uu____8468, uu____8471)  in
               FStar_Pervasives_Native.Some uu____8463
           | uu____8476 -> FStar_Pervasives_Native.None)
      | uu____8485 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8498 -> false
      | uu____8510 -> true  in
    let uu____8512 = map_if_all all_binders pats  in
    match uu____8512 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8544 = collapse_pats bs  in
        (uu____8544,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8561 = FStar_List.map p_atomicPattern pats  in
        (uu____8561,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8573 -> str "forall"
    | FStar_Parser_AST.QExists uu____8597 -> str "exists"
    | uu____8621 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8623  ->
    match uu___12_8623 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8635 =
          let uu____8636 =
            let uu____8637 =
              let uu____8638 = str "pattern"  in
              let uu____8640 =
                let uu____8641 =
                  let uu____8642 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8642
                   in
                FStar_Pprint.op_Hat_Hat uu____8641 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8638 uu____8640  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8637  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8636  in
        FStar_Pprint.group uu____8635

and (p_quantifier_attr :
  FStar_Ident.ident FStar_Pervasives_Native.option -> FStar_Pprint.document)
  =
  fun attr  ->
    match attr with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some attr1 ->
        let uu____8649 =
          let uu____8650 =
            let uu____8651 =
              let uu____8652 = p_uident attr1  in
              FStar_Pprint.op_Hat_Hat uu____8652 FStar_Pprint.rbrace  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8651  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8650  in
        FStar_Pprint.group uu____8649

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8658 = str "\\/"  in
    FStar_Pprint.separate_map uu____8658 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8665 =
      let uu____8666 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8666 p_appTerm pats  in
    FStar_Pprint.group uu____8665

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8678 = p_term_sep false pb e1  in
            (match uu____8678 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8687 = str "fun"  in
                   let uu____8689 =
                     let uu____8690 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8690
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8687 uu____8689  in
                 let uu____8691 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8693 =
                       let uu____8694 =
                         let uu____8695 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8695  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8694
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8693
                   else
                     (let uu____8698 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8698)
                    in
                 let uu____8699 = paren_if ps  in uu____8699 uu____8691)
        | uu____8704 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8712  ->
      match uu____8712 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8736 =
                    let uu____8737 =
                      let uu____8738 =
                        let uu____8739 = p_tuplePattern p  in
                        let uu____8740 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8739 uu____8740  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8738
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8737  in
                  FStar_Pprint.group uu____8736
              | FStar_Pervasives_Native.Some f ->
                  let uu____8742 =
                    let uu____8743 =
                      let uu____8744 =
                        let uu____8745 =
                          let uu____8746 =
                            let uu____8747 = p_tuplePattern p  in
                            let uu____8748 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8747
                              uu____8748
                             in
                          FStar_Pprint.group uu____8746  in
                        let uu____8750 =
                          let uu____8751 =
                            let uu____8754 = p_tmFormula f  in
                            [uu____8754; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8751  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8745 uu____8750
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8744
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8743  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8742
               in
            let uu____8756 = p_term_sep false pb e  in
            match uu____8756 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8766 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8766
                   else
                     (let uu____8769 =
                        let uu____8770 =
                          let uu____8771 =
                            let uu____8772 =
                              let uu____8773 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8773  in
                            op_Hat_Slash_Plus_Hat branch uu____8772  in
                          FStar_Pprint.group uu____8771  in
                        let uu____8774 =
                          let uu____8775 =
                            let uu____8776 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8776  in
                          FStar_Pprint.op_Hat_Hat branch uu____8775  in
                        FStar_Pprint.ifflat uu____8770 uu____8774  in
                      FStar_Pprint.group uu____8769))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8780 =
                       let uu____8781 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8781  in
                     op_Hat_Slash_Plus_Hat branch uu____8780)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8792 =
                      let uu____8793 =
                        let uu____8794 =
                          let uu____8795 =
                            let uu____8796 =
                              let uu____8797 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8797  in
                            FStar_Pprint.separate_map uu____8796
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8795
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8794
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8793  in
                    FStar_Pprint.group uu____8792
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8799 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8801;_},e1::e2::[])
        ->
        let uu____8807 = str "<==>"  in
        let uu____8809 = p_tmImplies e1  in
        let uu____8810 = p_tmIff e2  in
        infix0 uu____8807 uu____8809 uu____8810
    | uu____8811 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8813;_},e1::e2::[])
        ->
        let uu____8819 = str "==>"  in
        let uu____8821 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8827 = p_tmImplies e2  in
        infix0 uu____8819 uu____8821 uu____8827
    | uu____8828 ->
        p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
          false p_tmFormula e

and (format_sig :
  annotation_style ->
    FStar_Pprint.document Prims.list ->
      Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun style  ->
    fun terms  ->
      fun no_last_op  ->
        fun flat_space  ->
          let uu____8842 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8842 with
          | (terms',last1) ->
              let uu____8862 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8897 =
                      let uu____8898 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8898
                       in
                    let uu____8899 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8897, uu____8899)
                | Binders (n1,ln,parens1) ->
                    let uu____8913 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8921 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8913, break1, uu____8921)
                 in
              (match uu____8862 with
               | (n1,last_n,terms'1,sep,last_op) ->
                   let last2 = FStar_List.hd last1  in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > (Prims.parse_int "1")) &&
                         (Prims.op_Negation no_last_op)
                     then last_op
                     else FStar_Pprint.empty  in
                   let one_line_space =
                     if
                       (Prims.op_Negation (last2 = FStar_Pprint.empty)) ||
                         (Prims.op_Negation no_last_op)
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   let single_line_arg_indent =
                     FStar_Pprint.repeat n1 FStar_Pprint.space  in
                   let fs =
                     if flat_space
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   (match FStar_List.length terms with
                    | _8954 when _8954 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____8955 ->
                        let uu____8956 =
                          let uu____8957 =
                            let uu____8958 =
                              let uu____8959 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8960 =
                                let uu____8961 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8961
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8959 uu____8960
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8958  in
                          let uu____8962 =
                            let uu____8963 =
                              let uu____8964 =
                                let uu____8965 =
                                  let uu____8966 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8966  in
                                let uu____8967 =
                                  let uu____8968 =
                                    let uu____8969 =
                                      let uu____8970 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8971 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8977 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8977)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8970
                                        uu____8971
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8969
                                     in
                                  jump2 uu____8968  in
                                FStar_Pprint.ifflat uu____8965 uu____8967  in
                              FStar_Pprint.group uu____8964  in
                            let uu____8979 =
                              let uu____8980 =
                                let uu____8981 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8981  in
                              FStar_Pprint.align uu____8980  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8963 uu____8979
                             in
                          FStar_Pprint.ifflat uu____8957 uu____8962  in
                        FStar_Pprint.group uu____8956))

and (p_tmArrow :
  annotation_style ->
    Prims.bool ->
      (FStar_Parser_AST.term -> FStar_Pprint.document) ->
        FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun flat_space  ->
      fun p_Tm  ->
        fun e  ->
          let terms =
            match style with
            | Arrows uu____8995 -> p_tmArrow' p_Tm e
            | Binders uu____9002 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____9025 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____9031 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____9025 uu____9031
      | uu____9034 -> let uu____9035 = p_Tm e  in [uu____9035]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9088 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9114 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9088 uu____9114
        | uu____9137 ->
            let uu____9138 =
              let uu____9149 = p_Tm1 e1  in
              (uu____9149, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9138]
         in
      let fold_fun bs x =
        let uu____9247 = x  in
        match uu____9247 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9379 = hd1  in
                 (match uu____9379 with
                  | (b2s,t2,uu____9408) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9510 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9567 = cb  in
        match uu____9567 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9596 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9607 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9613 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9613) hd1 tl1
                         in
                      f uu____9607 typ))
         in
      let binders =
        let uu____9629 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9629  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9692 =
        let uu____9693 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9693 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9692  in
    let disj =
      let uu____9696 =
        let uu____9697 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9697 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9696  in
    let formula = p_tmDisjunction e  in
    FStar_Pprint.flow_map disj
      (fun d  ->
         FStar_Pprint.flow_map conj (fun x  -> FStar_Pprint.group x) d)
      formula

and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9717;_},e1::e2::[])
        ->
        let uu____9723 = p_tmDisjunction e1  in
        let uu____9728 = let uu____9733 = p_tmConjunction e2  in [uu____9733]
           in
        FStar_List.append uu____9723 uu____9728
    | uu____9742 -> let uu____9743 = p_tmConjunction e  in [uu____9743]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9753;_},e1::e2::[])
        ->
        let uu____9759 = p_tmConjunction e1  in
        let uu____9762 = let uu____9765 = p_tmTuple e2  in [uu____9765]  in
        FStar_List.append uu____9759 uu____9762
    | uu____9766 -> let uu____9767 = p_tmTuple e  in [uu____9767]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9784 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9784
          (fun uu____9792  ->
             match uu____9792 with | (e1,uu____9798) -> p_tmEq e1) args
    | uu____9799 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9808 =
             let uu____9809 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9809  in
           FStar_Pprint.group uu____9808)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12)
         in
      p_tmEqWith' p_X n1 e

and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op,e1::e2::[]) when
            ((is_operatorInfix0ad12 op) ||
               (let uu____9828 = FStar_Ident.text_of_id op  in
                uu____9828 = "="))
              ||
              (let uu____9833 = FStar_Ident.text_of_id op  in
               uu____9833 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9839 = levels op1  in
            (match uu____9839 with
             | (left1,mine,right1) ->
                 let uu____9858 =
                   let uu____9859 = FStar_All.pipe_left str op1  in
                   let uu____9861 = p_tmEqWith' p_X left1 e1  in
                   let uu____9862 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9859 uu____9861 uu____9862  in
                 paren_if_gt curr mine uu____9858)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9863;_},e1::e2::[])
            ->
            let uu____9869 =
              let uu____9870 = p_tmEqWith p_X e1  in
              let uu____9871 =
                let uu____9872 =
                  let uu____9873 =
                    let uu____9874 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9874  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9873  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9872  in
              FStar_Pprint.op_Hat_Hat uu____9870 uu____9871  in
            FStar_Pprint.group uu____9869
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9875;_},e1::[])
            ->
            let uu____9880 = levels "-"  in
            (match uu____9880 with
             | (left1,mine,right1) ->
                 let uu____9900 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9900)
        | uu____9901 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon; amp; opinfix3; opinfix4]  in
      p_tmNoEqWith' false p_X n1 e

and (p_tmNoEqWith' :
  Prims.bool ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun inside_tuple  ->
    fun p_X  ->
      fun curr  ->
        fun e  ->
          match e.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Construct
              (lid,(e1,uu____9949)::(e2,uu____9951)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9971 = is_list e  in Prims.op_Negation uu____9971)
              ->
              let op = "::"  in
              let uu____9976 = levels op  in
              (match uu____9976 with
               | (left1,mine,right1) ->
                   let uu____9995 =
                     let uu____9996 = str op  in
                     let uu____9997 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9999 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9996 uu____9997 uu____9999  in
                   paren_if_gt curr mine uu____9995)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____10018 = levels op  in
              (match uu____10018 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10052 = p_binder false b  in
                         let uu____10054 =
                           let uu____10055 =
                             let uu____10056 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10056 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10055
                            in
                         FStar_Pprint.op_Hat_Hat uu____10052 uu____10054
                     | FStar_Util.Inr t ->
                         let uu____10058 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10060 =
                           let uu____10061 =
                             let uu____10062 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10062 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10061
                            in
                         FStar_Pprint.op_Hat_Hat uu____10058 uu____10060
                      in
                   let uu____10063 =
                     let uu____10064 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10069 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10064 uu____10069  in
                   paren_if_gt curr mine uu____10063)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10071;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10101 = levels op  in
              (match uu____10101 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10121 = str op  in
                     let uu____10122 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10124 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10121 uu____10122 uu____10124
                   else
                     (let uu____10128 =
                        let uu____10129 = str op  in
                        let uu____10130 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10132 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10129 uu____10130 uu____10132  in
                      paren_if_gt curr mine uu____10128))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10141 = levels op1  in
              (match uu____10141 with
               | (left1,mine,right1) ->
                   let uu____10160 =
                     let uu____10161 = str op1  in
                     let uu____10162 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10164 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10161 uu____10162 uu____10164  in
                   paren_if_gt curr mine uu____10160)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10184 =
                let uu____10185 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10186 =
                  let uu____10187 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10187 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10185 uu____10186  in
              braces_with_nesting uu____10184
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10192;_},e1::[])
              ->
              let uu____10197 =
                let uu____10198 = str "~"  in
                let uu____10200 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10198 uu____10200  in
              FStar_Pprint.group uu____10197
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10202;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10211 = levels op  in
                   (match uu____10211 with
                    | (left1,mine,right1) ->
                        let uu____10230 =
                          let uu____10231 = str op  in
                          let uu____10232 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10234 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10231 uu____10232 uu____10234  in
                        paren_if_gt curr mine uu____10230)
               | uu____10236 -> p_X e)
          | uu____10237 -> p_X e

and (p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_appTerm e

and (p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_tmRefinement e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmNoEqWith p_tmRefinement e

and (p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.NamedTyp (lid,e1) ->
        let uu____10244 =
          let uu____10245 = p_lident lid  in
          let uu____10246 =
            let uu____10247 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10247  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10245 uu____10246  in
        FStar_Pprint.group uu____10244
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10250 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10252 = p_appTerm e  in
    let uu____10253 =
      let uu____10254 =
        let uu____10255 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10255 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10254  in
    FStar_Pprint.op_Hat_Hat uu____10252 uu____10253

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10261 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10261 t phi
      | FStar_Parser_AST.TAnnotated uu____10262 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10268 ->
          let uu____10269 =
            let uu____10271 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10271
             in
          failwith uu____10269
      | FStar_Parser_AST.TVariable uu____10274 ->
          let uu____10275 =
            let uu____10277 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10277
             in
          failwith uu____10275
      | FStar_Parser_AST.NoName uu____10280 ->
          let uu____10281 =
            let uu____10283 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10283
             in
          failwith uu____10281

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10287  ->
      match uu____10287 with
      | (lid,e) ->
          let uu____10295 =
            let uu____10296 = p_qlident lid  in
            let uu____10297 =
              let uu____10298 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10298
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10296 uu____10297  in
          FStar_Pprint.group uu____10295

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10301 when is_general_application e ->
        let uu____10308 = head_and_args e  in
        (match uu____10308 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10355 = p_argTerm e1  in
                  let uu____10356 =
                    let uu____10357 =
                      let uu____10358 =
                        let uu____10359 = str "`"  in
                        let uu____10361 =
                          let uu____10362 = p_indexingTerm head1  in
                          let uu____10363 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10362 uu____10363  in
                        FStar_Pprint.op_Hat_Hat uu____10359 uu____10361  in
                      FStar_Pprint.group uu____10358  in
                    let uu____10365 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10357 uu____10365  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10355 uu____10356
              | uu____10366 ->
                  let uu____10373 =
                    let uu____10384 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10384
                    then
                      let uu____10418 =
                        FStar_Util.take
                          (fun uu____10442  ->
                             match uu____10442 with
                             | (uu____10448,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10418 with
                      | (fs_typ_args,args1) ->
                          let uu____10486 =
                            let uu____10487 = p_indexingTerm head1  in
                            let uu____10488 =
                              let uu____10489 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10489
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10487 uu____10488
                             in
                          (uu____10486, args1)
                    else
                      (let uu____10504 = p_indexingTerm head1  in
                       (uu____10504, args))
                     in
                  (match uu____10373 with
                   | (head_doc,args1) ->
                       let uu____10525 =
                         let uu____10526 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10526 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10525)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10548 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10548)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10567 =
               let uu____10568 = p_quident lid  in
               let uu____10569 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10568 uu____10569  in
             FStar_Pprint.group uu____10567
         | hd1::tl1 ->
             let uu____10586 =
               let uu____10587 =
                 let uu____10588 =
                   let uu____10589 = p_quident lid  in
                   let uu____10590 = p_argTerm hd1  in
                   prefix2 uu____10589 uu____10590  in
                 FStar_Pprint.group uu____10588  in
               let uu____10591 =
                 let uu____10592 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10592  in
               FStar_Pprint.op_Hat_Hat uu____10587 uu____10591  in
             FStar_Pprint.group uu____10586)
    | uu____10597 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10608 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10608 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10612 = str "#"  in
        let uu____10614 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10612 uu____10614
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10617 = str "#["  in
        let uu____10619 =
          let uu____10620 = p_indexingTerm t  in
          let uu____10621 =
            let uu____10622 = str "]"  in
            let uu____10624 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10622 uu____10624  in
          FStar_Pprint.op_Hat_Hat uu____10620 uu____10621  in
        FStar_Pprint.op_Hat_Hat uu____10617 uu____10619
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10627  ->
    match uu____10627 with | (e,uu____10633) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10638;_},e1::e2::[])
          ->
          let uu____10644 =
            let uu____10645 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10646 =
              let uu____10647 =
                let uu____10648 = p_term false false e2  in
                soft_parens_with_nesting uu____10648  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10647  in
            FStar_Pprint.op_Hat_Hat uu____10645 uu____10646  in
          FStar_Pprint.group uu____10644
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10651;_},e1::e2::[])
          ->
          let uu____10657 =
            let uu____10658 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10659 =
              let uu____10660 =
                let uu____10661 = p_term false false e2  in
                soft_brackets_with_nesting uu____10661  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10660  in
            FStar_Pprint.op_Hat_Hat uu____10658 uu____10659  in
          FStar_Pprint.group uu____10657
      | uu____10664 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10669 = p_quident lid  in
        let uu____10670 =
          let uu____10671 =
            let uu____10672 = p_term false false e1  in
            soft_parens_with_nesting uu____10672  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10671  in
        FStar_Pprint.op_Hat_Hat uu____10669 uu____10670
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10680 =
          let uu____10681 = FStar_Ident.text_of_id op  in str uu____10681  in
        let uu____10683 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10680 uu____10683
    | uu____10684 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assume_lid ->
        str "assume"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____10697 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10706 =
          let uu____10707 = FStar_Ident.text_of_id op  in str uu____10707  in
        let uu____10709 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10706 uu____10709
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10713 =
          let uu____10714 =
            let uu____10715 =
              let uu____10716 = FStar_Ident.text_of_id op  in str uu____10716
               in
            let uu____10718 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10715 uu____10718  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10714  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10713
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10733 = all_explicit args  in
        if uu____10733
        then
          let uu____10736 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10737 =
            let uu____10738 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10739 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10738 p_tmEq uu____10739  in
          let uu____10746 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10736 uu____10737 uu____10746
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10768 =
                 let uu____10769 = p_quident lid  in
                 let uu____10770 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10769 uu____10770  in
               FStar_Pprint.group uu____10768
           | hd1::tl1 ->
               let uu____10787 =
                 let uu____10788 =
                   let uu____10789 =
                     let uu____10790 = p_quident lid  in
                     let uu____10791 = p_argTerm hd1  in
                     prefix2 uu____10790 uu____10791  in
                   FStar_Pprint.group uu____10789  in
                 let uu____10792 =
                   let uu____10793 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10793  in
                 FStar_Pprint.op_Hat_Hat uu____10788 uu____10792  in
               FStar_Pprint.group uu____10787)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10800 =
          let uu____10801 = p_atomicTermNotQUident e1  in
          let uu____10802 =
            let uu____10803 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10803  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10801 uu____10802
           in
        FStar_Pprint.group uu____10800
    | uu____10806 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10811 = p_quident constr_lid  in
        let uu____10812 =
          let uu____10813 =
            let uu____10814 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10814  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10813  in
        FStar_Pprint.op_Hat_Hat uu____10811 uu____10812
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10816 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10816 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10818 = p_term_sep false false e1  in
        (match uu____10818 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10831 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10831))
    | uu____10832 when is_array e ->
        let es = extract_from_list e  in
        let uu____10836 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10837 =
          let uu____10838 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10838
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10843 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10836 uu____10837 uu____10843
    | uu____10846 when is_list e ->
        let uu____10847 =
          let uu____10848 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10849 = extract_from_list e  in
          separate_map_or_flow_last uu____10848
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10849
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10847 FStar_Pprint.rbracket
    | uu____10858 when is_lex_list e ->
        let uu____10859 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10860 =
          let uu____10861 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10862 = extract_from_list e  in
          separate_map_or_flow_last uu____10861
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10862
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10859 uu____10860 FStar_Pprint.rbracket
    | uu____10871 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10875 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10876 =
          let uu____10877 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10877 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10875 uu____10876 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10887 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10890 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10887 uu____10890
    | FStar_Parser_AST.Op (op,args) when
        let uu____10899 = handleable_op op args  in
        Prims.op_Negation uu____10899 ->
        let uu____10901 =
          let uu____10903 =
            let uu____10905 = FStar_Ident.text_of_id op  in
            let uu____10907 =
              let uu____10909 =
                let uu____10911 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10911
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10909  in
            Prims.op_Hat uu____10905 uu____10907  in
          Prims.op_Hat "Operation " uu____10903  in
        failwith uu____10901
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10918 = p_term false false e  in
        soft_parens_with_nesting uu____10918
    | FStar_Parser_AST.Const uu____10921 ->
        let uu____10922 = p_term false false e  in
        soft_parens_with_nesting uu____10922
    | FStar_Parser_AST.Op uu____10925 ->
        let uu____10932 = p_term false false e  in
        soft_parens_with_nesting uu____10932
    | FStar_Parser_AST.Tvar uu____10935 ->
        let uu____10936 = p_term false false e  in
        soft_parens_with_nesting uu____10936
    | FStar_Parser_AST.Var uu____10939 ->
        let uu____10940 = p_term false false e  in
        soft_parens_with_nesting uu____10940
    | FStar_Parser_AST.Name uu____10943 ->
        let uu____10944 = p_term false false e  in
        soft_parens_with_nesting uu____10944
    | FStar_Parser_AST.Construct uu____10947 ->
        let uu____10958 = p_term false false e  in
        soft_parens_with_nesting uu____10958
    | FStar_Parser_AST.Abs uu____10961 ->
        let uu____10968 = p_term false false e  in
        soft_parens_with_nesting uu____10968
    | FStar_Parser_AST.App uu____10971 ->
        let uu____10978 = p_term false false e  in
        soft_parens_with_nesting uu____10978
    | FStar_Parser_AST.Let uu____10981 ->
        let uu____11002 = p_term false false e  in
        soft_parens_with_nesting uu____11002
    | FStar_Parser_AST.LetOpen uu____11005 ->
        let uu____11010 = p_term false false e  in
        soft_parens_with_nesting uu____11010
    | FStar_Parser_AST.Seq uu____11013 ->
        let uu____11018 = p_term false false e  in
        soft_parens_with_nesting uu____11018
    | FStar_Parser_AST.Bind uu____11021 ->
        let uu____11028 = p_term false false e  in
        soft_parens_with_nesting uu____11028
    | FStar_Parser_AST.If uu____11031 ->
        let uu____11038 = p_term false false e  in
        soft_parens_with_nesting uu____11038
    | FStar_Parser_AST.Match uu____11041 ->
        let uu____11056 = p_term false false e  in
        soft_parens_with_nesting uu____11056
    | FStar_Parser_AST.TryWith uu____11059 ->
        let uu____11074 = p_term false false e  in
        soft_parens_with_nesting uu____11074
    | FStar_Parser_AST.Ascribed uu____11077 ->
        let uu____11086 = p_term false false e  in
        soft_parens_with_nesting uu____11086
    | FStar_Parser_AST.Record uu____11089 ->
        let uu____11102 = p_term false false e  in
        soft_parens_with_nesting uu____11102
    | FStar_Parser_AST.Project uu____11105 ->
        let uu____11110 = p_term false false e  in
        soft_parens_with_nesting uu____11110
    | FStar_Parser_AST.Product uu____11113 ->
        let uu____11120 = p_term false false e  in
        soft_parens_with_nesting uu____11120
    | FStar_Parser_AST.Sum uu____11123 ->
        let uu____11134 = p_term false false e  in
        soft_parens_with_nesting uu____11134
    | FStar_Parser_AST.QForall uu____11137 ->
        let uu____11160 = p_term false false e  in
        soft_parens_with_nesting uu____11160
    | FStar_Parser_AST.QExists uu____11163 ->
        let uu____11186 = p_term false false e  in
        soft_parens_with_nesting uu____11186
    | FStar_Parser_AST.Refine uu____11189 ->
        let uu____11194 = p_term false false e  in
        soft_parens_with_nesting uu____11194
    | FStar_Parser_AST.NamedTyp uu____11197 ->
        let uu____11202 = p_term false false e  in
        soft_parens_with_nesting uu____11202
    | FStar_Parser_AST.Requires uu____11205 ->
        let uu____11213 = p_term false false e  in
        soft_parens_with_nesting uu____11213
    | FStar_Parser_AST.Ensures uu____11216 ->
        let uu____11224 = p_term false false e  in
        soft_parens_with_nesting uu____11224
    | FStar_Parser_AST.Attributes uu____11227 ->
        let uu____11230 = p_term false false e  in
        soft_parens_with_nesting uu____11230
    | FStar_Parser_AST.Quote uu____11233 ->
        let uu____11238 = p_term false false e  in
        soft_parens_with_nesting uu____11238
    | FStar_Parser_AST.VQuote uu____11241 ->
        let uu____11242 = p_term false false e  in
        soft_parens_with_nesting uu____11242
    | FStar_Parser_AST.Antiquote uu____11245 ->
        let uu____11246 = p_term false false e  in
        soft_parens_with_nesting uu____11246
    | FStar_Parser_AST.CalcProof uu____11249 ->
        let uu____11258 = p_term false false e  in
        soft_parens_with_nesting uu____11258

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_11261  ->
    match uu___15_11261 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11273) ->
        let uu____11276 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11276
    | FStar_Const.Const_bytearray (bytes,uu____11278) ->
        let uu____11283 =
          let uu____11284 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11284  in
        let uu____11285 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11283 uu____11285
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_11308 =
          match uu___13_11308 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_11315 =
          match uu___14_11315 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11330  ->
               match uu____11330 with
               | (s,w) ->
                   let uu____11337 = signedness s  in
                   let uu____11338 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11337 uu____11338)
            sign_width_opt
           in
        let uu____11339 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11339 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11343 = FStar_Range.string_of_range r  in str uu____11343
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11347 = p_quident lid  in
        let uu____11348 =
          let uu____11349 =
            let uu____11350 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11350  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11349  in
        FStar_Pprint.op_Hat_Hat uu____11347 uu____11348

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11353 = str "u#"  in
    let uu____11355 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11353 uu____11355

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11357;_},u1::u2::[])
        ->
        let uu____11363 =
          let uu____11364 = p_universeFrom u1  in
          let uu____11365 =
            let uu____11366 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11366  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11364 uu____11365  in
        FStar_Pprint.group uu____11363
    | FStar_Parser_AST.App uu____11367 ->
        let uu____11374 = head_and_args u  in
        (match uu____11374 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11400 =
                    let uu____11401 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11402 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11410  ->
                           match uu____11410 with
                           | (u1,uu____11416) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11401 uu____11402  in
                  FStar_Pprint.group uu____11400
              | uu____11417 ->
                  let uu____11418 =
                    let uu____11420 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11420
                     in
                  failwith uu____11418))
    | uu____11423 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11449 = FStar_Ident.text_of_id id1  in str uu____11449
    | FStar_Parser_AST.Paren u1 ->
        let uu____11452 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11452
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11453;_},uu____11454::uu____11455::[])
        ->
        let uu____11459 = p_universeFrom u  in
        soft_parens_with_nesting uu____11459
    | FStar_Parser_AST.App uu____11460 ->
        let uu____11467 = p_universeFrom u  in
        soft_parens_with_nesting uu____11467
    | uu____11468 ->
        let uu____11469 =
          let uu____11471 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11471
           in
        failwith uu____11469

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    FStar_ST.op_Colon_Equals unfold_tuples false; p_term false false e
  
let (signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document)
  = fun e  -> p_justSig e 
let (decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun e  -> p_decl e 
let (pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  -> p_disjunctivePattern p 
let (binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun b  -> p_binder true b 
let (modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document) =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____11560,decls) ->
           let uu____11566 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11566
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11575,decls,uu____11577) ->
           let uu____11584 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11584
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11644  ->
         match uu____11644 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11666)) -> false
      | ([],uu____11670) -> false
      | uu____11674 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11684 -> true
         | uu____11686 -> false)
    }
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____11729,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11735,decls,uu____11737) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11789 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11802;
                 FStar_Parser_AST.doc = uu____11803;
                 FStar_Parser_AST.quals = uu____11804;
                 FStar_Parser_AST.attrs = uu____11805;_}::uu____11806 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11812 =
                   let uu____11815 =
                     let uu____11818 = FStar_List.tl ds  in d :: uu____11818
                      in
                   d0 :: uu____11815  in
                 (uu____11812, (d0.FStar_Parser_AST.drange))
             | uu____11823 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11789 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11880 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11880 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11989 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11989, comments1))))))
  