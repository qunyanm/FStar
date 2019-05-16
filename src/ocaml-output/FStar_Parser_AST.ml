open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee  -> match projectee with | Un  -> true | uu____26 -> false 
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee  -> match projectee with | Expr  -> true | uu____37 -> false 
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____48 -> false
  
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee  -> match projectee with | Kind  -> true | uu____59 -> false 
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____70 -> false
  
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____81 -> false
  
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Rec  -> true | uu____92 -> false 
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Static  -> true | uu____103 -> false
  
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dynamic  -> true | uu____114 -> false
  
type term' =
  | Wild 
  | Const of FStar_Const.sconst 
  | Op of (FStar_Ident.ident * term Prims.list) 
  | Tvar of FStar_Ident.ident 
  | Uvar of FStar_Ident.ident 
  | Var of FStar_Ident.lid 
  | Name of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid * FStar_Ident.ident) 
  | Construct of (FStar_Ident.lid * (term * imp) Prims.list) 
  | Abs of (pattern Prims.list * term) 
  | App of (term * term * imp) 
  | Let of (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
  (pattern * term)) Prims.list * term) 
  | LetOpen of (FStar_Ident.lid * term) 
  | Seq of (term * term) 
  | Bind of (FStar_Ident.ident * term * term) 
  | If of (term * term * term) 
  | Match of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | TryWith of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | Ascribed of (term * term * term FStar_Pervasives_Native.option) 
  | Record of (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
  Prims.list) 
  | Project of (term * FStar_Ident.lid) 
  | Product of (binder Prims.list * term) 
  | Sum of ((binder,term) FStar_Util.either Prims.list * term) 
  | QForall of (binder Prims.list * FStar_Ident.ident
  FStar_Pervasives_Native.option * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | QExists of (binder Prims.list * FStar_Ident.ident
  FStar_Pervasives_Native.option * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | Refine of (binder * term) 
  | NamedTyp of (FStar_Ident.ident * term) 
  | Paren of term 
  | Requires of (term * Prims.string FStar_Pervasives_Native.option) 
  | Ensures of (term * Prims.string FStar_Pervasives_Native.option) 
  | Labeled of (term * Prims.string * Prims.bool) 
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
  | Antiquote of term 
  | Quote of (term * quote_kind) 
  | VQuote of term 
  | CalcProof of (term * term * calc_step Prims.list) 
and term = {
  tm: term' ;
  range: FStar_Range.range ;
  level: level }
and calc_step =
  | CalcStep of (term * term * term) 
and binder' =
  | Variable of FStar_Ident.ident 
  | TVariable of FStar_Ident.ident 
  | Annotated of (FStar_Ident.ident * term) 
  | TAnnotated of (FStar_Ident.ident * term) 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStar_Range.range ;
  blevel: level ;
  aqual: arg_qualifier FStar_Pervasives_Native.option }
and pattern' =
  | PatWild of arg_qualifier FStar_Pervasives_Native.option 
  | PatConst of FStar_Const.sconst 
  | PatApp of (pattern * pattern Prims.list) 
  | PatVar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option) 
  | PatName of FStar_Ident.lid 
  | PatTvar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option) 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list * Prims.bool) 
  | PatRecord of (FStar_Ident.lid * pattern) Prims.list 
  | PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option)) 
  | PatOr of pattern Prims.list 
  | PatOp of FStar_Ident.ident 
and pattern = {
  pat: pattern' ;
  prange: FStar_Range.range }
and arg_qualifier =
  | Implicit 
  | Equality 
  | Meta of term 
and imp =
  | FsTypApp 
  | Hash 
  | UnivApp 
  | HashBrace of term 
  | Infix 
  | Nothing 
let (uu___is_Wild : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Wild  -> true | uu____741 -> false 
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____753 -> false
  
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Op _0 -> true | uu____778 -> false 
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee  -> match projectee with | Op _0 -> _0 
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____815 -> false
  
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____834 -> false
  
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____853 -> false
  
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____872 -> false
  
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____895 -> false
  
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____936 -> false
  
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____991 -> false
  
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1034 -> false
  
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1091 -> false
  
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____1174 -> false
  
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____1209 -> false
  
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____1246 -> false
  
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let (uu___is_If : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | If _0 -> true | uu____1289 -> false
  
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee  -> match projectee with | If _0 -> _0 
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1340 -> false
  
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1415 -> false
  
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1484 -> false
  
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0 
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1539 -> false
  
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee  -> match projectee with | Record _0 -> _0 
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1598 -> false
  
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1635 -> false
  
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1682 -> false
  
let (__proj__Sum__item___0 :
  term' -> ((binder,term) FStar_Util.either Prims.list * term)) =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1753 -> false
  
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * FStar_Ident.ident FStar_Pervasives_Native.option *
      (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term))
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1860 -> false
  
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * FStar_Ident.ident FStar_Pervasives_Native.option *
      (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term))
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1949 -> false
  
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1984 -> false
  
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____2015 -> false
  
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____2041 -> false
  
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Requires _0 -> _0 
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____2088 -> false
  
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ensures _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____2136 -> false
  
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____2179 -> false
  
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____2200 -> false
  
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Antiquote _0 -> true | uu____2225 -> false
  
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Antiquote _0 -> _0 
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____2248 -> false
  
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VQuote _0 -> true | uu____2279 -> false
  
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | VQuote _0 -> _0 
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | CalcProof _0 -> true | uu____2306 -> false
  
let (__proj__CalcProof__item___0 :
  term' -> (term * term * calc_step Prims.list)) =
  fun projectee  -> match projectee with | CalcProof _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  -> match projectee with | { tm; range; level;_} -> tm 
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> range 
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> level 
let (uu___is_CalcStep : calc_step -> Prims.bool) = fun projectee  -> true 
let (__proj__CalcStep__item___0 : calc_step -> (term * term * term)) =
  fun projectee  -> match projectee with | CalcStep _0 -> _0 
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____2409 -> false
  
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____2428 -> false
  
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____2451 -> false
  
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____2486 -> false
  
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____2517 -> false
  
let (__proj__NoName__item___0 : binder' -> term) =
  fun projectee  -> match projectee with | NoName _0 -> _0 
let (__proj__Mkbinder__item__b : binder -> binder') =
  fun projectee  -> match projectee with | { b; brange; blevel; aqual;_} -> b 
let (__proj__Mkbinder__item__brange : binder -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> brange
  
let (__proj__Mkbinder__item__blevel : binder -> level) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> blevel
  
let (__proj__Mkbinder__item__aqual :
  binder -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> aqual
  
let (uu___is_PatWild : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatWild _0 -> true | uu____2590 -> false
  
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PatWild _0 -> _0 
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____2615 -> false
  
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____2640 -> false
  
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____2683 -> false
  
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____2720 -> false
  
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____2745 -> false
  
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____2784 -> false
  
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____2816 -> false
  
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | PatTuple _0 -> _0 
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____2862 -> false
  
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee  -> match projectee with | PatRecord _0 -> _0 
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2909 -> false
  
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2960 -> false
  
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2985 -> false
  
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee  -> match projectee with | { pat; prange;_} -> pat 
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee  -> match projectee with | { pat; prange;_} -> prange 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____3019 -> false
  
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____3030 -> false
  
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____3042 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____3060 -> false
  
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hash  -> true | uu____3071 -> false
  
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____3082 -> false
  
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | HashBrace _0 -> true | uu____3094 -> false
  
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee  -> match projectee with | HashBrace _0 -> _0 
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix  -> true | uu____3112 -> false
  
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____3123 -> false
  
type patterns = (FStar_Ident.ident Prims.list * term Prims.list Prims.list)
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type fsdoc = (Prims.string * (Prims.string * Prims.string) Prims.list)
type tycon =
  | TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option) 
  | TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * term) 
  | TyconRecord of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
  FStar_Pervasives_Native.option) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term
  FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option *
  Prims.bool) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____3271 -> false
  
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____3332 -> false
  
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____3409 -> false
  
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____3521 -> false
  
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term
      FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option *
      Prims.bool) Prims.list))
  = fun projectee  -> match projectee with | TyconVariant _0 -> _0 
type qualifier =
  | Private 
  | Abstract 
  | Noeq 
  | Unopteq 
  | Assumption 
  | DefaultEffect 
  | TotalEffect 
  | Effect_qual 
  | New 
  | Inline 
  | Visible 
  | Unfold_for_unification_and_vcgen 
  | Inline_for_extraction 
  | Irreducible 
  | NoExtract 
  | Reifiable 
  | Reflectable 
  | Opaque 
  | Logic 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____3620 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____3631 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____3642 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____3653 -> false
  
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____3664 -> false
  
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____3675 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____3686 -> false
  
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____3697 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____3708 -> false 
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____3719 -> false
  
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____3730 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____3741 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____3752 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____3763 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____3774 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____3785 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____3796 -> false
  
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____3807 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____3818 -> false
  
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____3849 -> false
  
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____3870 -> false
  
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let (uu___is_Doc : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____3895 -> false
  
let (__proj__Doc__item___0 : decoration -> fsdoc) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____3933 -> false
  
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____3956 -> false
  
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____3987 -> false
  
let (__proj__LiftForFree__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let (__proj__Mklift__item__msource : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> msource
  
let (__proj__Mklift__item__mdest : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> mdest
  
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> lift_op
  
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | LightOff 
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____4071 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____4096 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____4127 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____4154 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____4165 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Friend of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Main of term 
  | Tycon of (Prims.bool * Prims.bool * (tycon * fsdoc
  FStar_Pervasives_Native.option) Prims.list) 
  | Val of (FStar_Ident.ident * term) 
  | Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option) 
  | NewEffect of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident * term) 
  | Splice of (FStar_Ident.ident Prims.list * term) 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  doc: fsdoc FStar_Pervasives_Native.option ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term) 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____4364 -> false
  
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____4383 -> false
  
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Open _0 -> _0 
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Friend _0 -> true | uu____4402 -> false
  
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Friend _0 -> _0 
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____4421 -> false
  
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Include _0 -> _0 
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____4444 -> false
  
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____4485 -> false
  
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_Main : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____4534 -> false
  
let (__proj__Main__item___0 : decl' -> term) =
  fun projectee  -> match projectee with | Main _0 -> _0 
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____4569 -> false
  
let (__proj__Tycon__item___0 :
  decl' ->
    (Prims.bool * Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option)
      Prims.list))
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____4640 -> false
  
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____4677 -> false
  
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Exception _0 -> _0 
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____4714 -> false
  
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____4733 -> false
  
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____4752 -> false
  
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let (uu___is_Fsdoc : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____4771 -> false
  
let (__proj__Fsdoc__item___0 : decl' -> fsdoc) =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____4794 -> false
  
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Splice _0 -> true | uu____4831 -> false
  
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list * term)) =
  fun projectee  -> match projectee with | Splice _0 -> _0 
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> d
  
let (__proj__Mkdecl__item__drange : decl -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> drange
  
let (__proj__Mkdecl__item__doc :
  decl -> fsdoc FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> doc1
  
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> quals
  
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> attrs
  
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____4949 -> false
  
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____5012 -> false
  
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____5086 -> false
  
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____5132 -> false
  
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul
type inputFragment = (file,decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl  -> decl.drange 
let (check_id : FStar_Ident.ident -> unit) =
  fun id1  ->
    let first_char =
      FStar_String.substring id1.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1")
       in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____5194 =
         let uu____5200 =
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             id1.FStar_Ident.idText
            in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____5200)  in
       FStar_Errors.raise_error uu____5194 id1.FStar_Ident.idRange)
  
let at_most_one :
  'Auu____5213 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____5213 Prims.list ->
          'Auu____5213 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____5238 ->
            let uu____5241 =
              let uu____5247 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s
                 in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____5247)  in
            FStar_Errors.raise_error uu____5241 r
  
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____5276 =
            FStar_List.choose
              (fun uu___0_5281  ->
                 match uu___0_5281 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____5285 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____5276  in
        let attributes_ =
          let uu____5292 =
            FStar_List.choose
              (fun uu___1_5301  ->
                 match uu___1_5301 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____5311 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____5292  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___2_5327  ->
               match uu___2_5327 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____5331 -> FStar_Pervasives_Native.None) decorations
           in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
  
let (mk_binder :
  binder' ->
    FStar_Range.range ->
      level -> arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
  
let (mk_term : term' -> FStar_Range.range -> level -> term) =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l } 
let (mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term) =
  fun t  ->
    fun rminus  ->
      fun r  ->
        fun l  ->
          let t1 =
            match t.tm with
            | Const (FStar_Const.Const_int
                (s,FStar_Pervasives_Native.Some (FStar_Const.Signed ,width)))
                ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.op_Hat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____5421 ->
                let uu____5422 =
                  let uu____5429 = FStar_Ident.mk_ident ("-", rminus)  in
                  (uu____5429, [t])  in
                Op uu____5422
             in
          mk_term t1 r l
  
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p  -> fun r  -> { pat = p; prange = r } 
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____5468 -> Abs (ps, body)
  
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = FStar_Ident.gen r1  in
        let uu____5508 =
          let uu____5509 =
            let uu____5516 =
              let uu____5517 =
                let uu____5518 =
                  let uu____5533 =
                    let uu____5534 =
                      let uu____5535 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____5535  in
                    mk_term uu____5534 r1 Expr  in
                  (uu____5533, branches)  in
                Match uu____5518  in
              mk_term uu____5517 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____5516)
             in
          Abs uu____5509  in
        mk_term uu____5508 r2 Expr
  
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____5573,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____5592 -> FStar_Pervasives_Native.None
  
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid  ->
    fun r  ->
      let uu____5612 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____5612 r
  
let (consPat : FStar_Range.range -> pattern -> pattern -> pattern') =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd1; tl1])
  
let (consTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd1, Nothing); (tl1, Nothing)]))
          r Expr
  
let (lexConsTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid,
               [(hd1, Nothing); (tl1, Nothing)])) r Expr
  
let (mkConsList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl1  -> consTerm r e tl1) elts nil
  
let (mkLexList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl1  -> lexConsTerm r e tl1) elts
        nil
  
let (ml_comp : term -> term) =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr  in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let (tot_comp : term -> term) =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr
       in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let (mkApp : term -> (term * imp) Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____5807 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____5821 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____5831  ->
                        match uu____5831 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
  
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let uu____5853 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____5853 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            let uu____5867 =
              let uu____5868 = FStar_Ident.set_lid_range empty_lid r  in
              Var uu____5868  in
            mk_term uu____5867 r Expr  in
          let addr_of =
            let uu____5870 =
              let uu____5871 = FStar_Ident.set_lid_range addr_of_lid r  in
              Var uu____5871  in
            mk_term uu____5870 r Expr  in
          let singleton1 =
            let uu____5873 =
              let uu____5874 = FStar_Ident.set_lid_range singleton_lid r  in
              Var uu____5874  in
            mk_term uu____5873 r Expr  in
          let union1 =
            let uu____5876 =
              let uu____5877 = FStar_Ident.set_lid_range union_lid r  in
              Var uu____5877  in
            mk_term uu____5876 r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp addr_of [(e, Nothing)] r  in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r  in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
  
let (mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____5934 ->
            (match t.tm with
             | Name s ->
                 let uu____5938 =
                   let uu____5939 =
                     let uu____5950 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____5950)  in
                   Construct uu____5939  in
                 mk_term uu____5938 r Un
             | uu____5969 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let (unit_const : FStar_Range.range -> term) =
  fun r  -> mk_term (Const FStar_Const.Const_unit) r Expr 
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r  ->
    let admit1 =
      let admit_name =
        let uu____5988 =
          let uu____5989 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r  in
          Var uu____5989  in
        mk_term uu____5988 r Expr  in
      mkExplicitApp admit_name [unit_const r] r  in
    let magic1 =
      let magic_name =
        let uu____5992 =
          let uu____5993 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r  in
          Var uu____5993  in
        mk_term uu____5992 r Expr  in
      mkExplicitApp magic_name [unit_const r] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'Auu____6000 .
    FStar_Range.range ->
      (pattern * 'Auu____6000 FStar_Pervasives_Native.option * term)
  =
  fun r  ->
    let uu____6014 = mkAdmitMagic r  in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____6014)
  
let focusBranches :
  'Auu____6024 .
    (Prims.bool * (pattern * 'Auu____6024 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'Auu____6024 FStar_Pervasives_Native.option * term)
          Prims.list
  =
  fun branches  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches  in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered, "Focusing on only some cases");
         (let focussed =
            let uu____6124 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____6124
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____6217 =
            let uu____6228 = mkWildAdmitMagic r  in [uu____6228]  in
          FStar_List.append focussed uu____6217))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'Auu____6325 .
    (Prims.bool * ('Auu____6325 * term)) Prims.list ->
      FStar_Range.range -> ('Auu____6325 * term) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____6406  ->
              match uu____6406 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____6439 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____6439))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusAttrLetBindings :
  'Auu____6486 'Auu____6487 .
    ('Auu____6486 * (Prims.bool * ('Auu____6487 * term))) Prims.list ->
      FStar_Range.range -> ('Auu____6486 * ('Auu____6487 * term)) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____6557  ->
             match uu____6557 with | (attr,(focus,uu____6574)) -> focus) lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____6633  ->
              match uu____6633 with
              | (attr,(f,lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____6692 =
                       let uu____6697 = mkAdmitMagic r  in
                       ((FStar_Pervasives_Native.fst lb), uu____6697)  in
                     (attr, uu____6692))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____6754  ->
                match uu____6754 with | (attr,(uu____6777,lb)) -> (attr, lb)))
  
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____6822 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____6822 r
  
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____6851 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____6851 r
  
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____6880 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____6880 r
  
let (mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range ->
            arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun id1  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id1, t)) m Type_level implicit
                 in
              match refopt with
              | FStar_Pervasives_Native.None  -> b
              | FStar_Pervasives_Native.Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id1, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range  in
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit  in
                     mk_binder
                       (Annotated
                          (id1, (mk_term (Refine (b1, phi)) m Type_level))) m
                       Type_level implicit)
  
let (mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern)
  =
  fun pat  ->
    fun t  ->
      fun should_bind_pat  ->
        fun phi_opt  ->
          fun t_range  ->
            fun range  ->
              let t1 =
                match phi_opt with
                | FStar_Pervasives_Native.None  -> t
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x,uu____6982) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____6987 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____6991 =
                                 let uu____6992 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____6992  in
                               mk_term uu____6991 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____7013 =
                                 let uu____7014 =
                                   let uu____7015 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____7015  in
                                 mk_term uu____7014 phi.range Formula  in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____7013)
                                in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula
                              in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range  in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                FStar_Pervasives_Native.None), phi)) range
                         Type_level)
                 in
              mk_pattern
                (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
  
let rec (extract_named_refinement :
  term ->
    (FStar_Ident.ident * term * term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____7106; blevel = uu____7107;
           aqual = uu____7108;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____7123 -> FStar_Pervasives_Native.None
  
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur  ->
    fun ds  ->
      let uu____7167 = cur  in
      match uu____7167 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____7198 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
  
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____7227 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____7227 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____7265 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____7265 :: ds1
                   else ds1  in
                 let m1 = as_mlist ((m, d), []) ds2  in FStar_Util.Inl m1
             | uu____7277 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___3_7288  ->
                       match uu___3_7288 with
                       | { d = TopLevelModule uu____7289; drange = r;
                           doc = uu____7291; quals = uu____7292;
                           attrs = uu____7293;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____7298 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___4_7329 =
          match uu___4_7329 with
          | 38 -> "Amp"
          | 64 -> "At"
          | 43 -> "Plus"
          | 45 when arity = (Prims.parse_int "1") -> "Minus"
          | 45 -> "Subtraction"
          | 126 -> "Tilde"
          | 47 -> "Slash"
          | 92 -> "Backslash"
          | 60 -> "Less"
          | 61 -> "Equals"
          | 62 -> "Greater"
          | 95 -> "Underscore"
          | 124 -> "Bar"
          | 33 -> "Bang"
          | 94 -> "Hat"
          | 37 -> "Percent"
          | 42 -> "Star"
          | 63 -> "Question"
          | 58 -> "Colon"
          | 36 -> "Dollar"
          | 46 -> "Dot"
          | c ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedOperatorSymbol,
                  (Prims.op_Hat "Unexpected operator symbol: '"
                     (Prims.op_Hat (FStar_Util.string_of_char c) "'"))) r
           in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[||]<-" -> "op_Brack_Lens_Assignment"
        | ".(||)<-" -> "op_Lens_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
        | ".[||]" -> "op_Brack_Lens_Access"
        | ".(||)" -> "op_Lens_Access"
        | uu____7399 ->
            let uu____7401 =
              let uu____7403 =
                let uu____7407 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____7407  in
              FStar_String.concat "_" uu____7403  in
            Prims.op_Hat "op_" uu____7401
  
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s  -> fun r  -> compile_op (~- (Prims.parse_int "1")) s r 
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____7449  ->
    match uu____7449 with
    | (comment,keywords) ->
        let uu____7484 =
          let uu____7486 =
            FStar_List.map
              (fun uu____7500  ->
                 match uu____7500 with
                 | (k,v1) -> Prims.op_Hat k (Prims.op_Hat "->" v1)) keywords
             in
          FStar_String.concat "," uu____7486  in
        Prims.op_Hat comment uu____7484
  
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___5_7522  ->
    match uu___5_7522 with | NoLetQualifier  -> "" | Rec  -> "rec"
  
let to_string_l :
  'Auu____7535 .
    Prims.string ->
      ('Auu____7535 -> Prims.string) ->
        'Auu____7535 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____7565 = FStar_List.map f l  in
        FStar_String.concat sep uu____7565
  
let (imp_to_string : imp -> Prims.string) =
  fun uu___6_7576  ->
    match uu___6_7576 with | Hash  -> "#" | uu____7579 -> ""
  
let rec (term_to_string : term -> Prims.string) =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____7622) ->
        let uu____7629 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____7629
    | Ensures (t,uu____7633) ->
        let uu____7640 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____7640
    | Labeled (t,l,uu____7645) ->
        let uu____7650 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____7650
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____7660 = FStar_Ident.text_of_id s  in
        let uu____7662 =
          let uu____7664 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____7664  in
        FStar_Util.format2 "%s(%s)" uu____7660 uu____7662
    | Tvar id1 -> id1.FStar_Ident.idText
    | Uvar id1 -> id1.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Projector (rec_lid,field_id) ->
        let uu____7680 = FStar_Ident.string_of_lid rec_lid  in
        FStar_Util.format2 "%s?.%s" uu____7680 field_id.FStar_Ident.idText
    | Construct (l,args) ->
        let uu____7697 =
          to_string_l " "
            (fun uu____7708  ->
               match uu____7708 with
               | (a,imp) ->
                   let uu____7716 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____7716)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____7697
    | Abs (pats,t) ->
        let uu____7726 = to_string_l " " pat_to_string pats  in
        let uu____7729 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____7726 uu____7729
    | App (t1,t2,imp) ->
        let uu____7736 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7739 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____7736 (imp_to_string imp)
          uu____7739
    | Let (Rec ,(a,(p,b))::lbs,body) ->
        let uu____7800 = attrs_opt_to_string a  in
        let uu____7802 =
          let uu____7804 = FStar_All.pipe_right p pat_to_string  in
          let uu____7807 = FStar_All.pipe_right b term_to_string  in
          FStar_Util.format2 "%s=%s" uu____7804 uu____7807  in
        let uu____7811 =
          to_string_l " "
            (fun uu____7833  ->
               match uu____7833 with
               | (a1,(p1,b1)) ->
                   let uu____7862 = attrs_opt_to_string a1  in
                   let uu____7864 = FStar_All.pipe_right p1 pat_to_string  in
                   let uu____7867 = FStar_All.pipe_right b1 term_to_string
                      in
                   FStar_Util.format3 "%sand %s=%s" uu____7862 uu____7864
                     uu____7867) lbs
           in
        let uu____7871 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____7800 uu____7802
          uu____7811 uu____7871
    | Let (q,(attrs,(pat,tm))::[],body) ->
        let uu____7930 = attrs_opt_to_string attrs  in
        let uu____7932 = FStar_All.pipe_right pat pat_to_string  in
        let uu____7935 = FStar_All.pipe_right tm term_to_string  in
        let uu____7938 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____7930
          (string_of_let_qualifier q) uu____7932 uu____7935 uu____7938
    | Let (uu____7942,uu____7943,uu____7944) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid,t) ->
        let uu____7978 = FStar_Ident.string_of_lid lid  in
        let uu____7980 = term_to_string t  in
        FStar_Util.format2 "let open %s in %s" uu____7978 uu____7980
    | Seq (t1,t2) ->
        let uu____7985 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7988 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____7985 uu____7988
    | Bind (id1,t1,t2) ->
        let uu____7995 = term_to_string t1  in
        let uu____7997 = term_to_string t2  in
        FStar_Util.format3 "%s <- %s; %s" id1.FStar_Ident.idText uu____7995
          uu____7997
    | If (t1,t2,t3) ->
        let uu____8003 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8006 = FStar_All.pipe_right t2 term_to_string  in
        let uu____8009 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____8003 uu____8006
          uu____8009
    | Match (t,branches) ->
        let s =
          match x.tm with
          | Match uu____8038 -> "match"
          | TryWith uu____8054 -> "try"
          | uu____8070 -> failwith "impossible"  in
        let uu____8073 = FStar_All.pipe_right t term_to_string  in
        let uu____8076 =
          to_string_l " | "
            (fun uu____8094  ->
               match uu____8094 with
               | (p,w,e) ->
                   let uu____8111 = FStar_All.pipe_right p pat_to_string  in
                   let uu____8114 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8119 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____8119
                      in
                   let uu____8122 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____8111 uu____8114
                     uu____8122) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____8073 uu____8076
    | TryWith (t,branches) ->
        let s =
          match x.tm with
          | Match uu____8152 -> "match"
          | TryWith uu____8168 -> "try"
          | uu____8184 -> failwith "impossible"  in
        let uu____8187 = FStar_All.pipe_right t term_to_string  in
        let uu____8190 =
          to_string_l " | "
            (fun uu____8208  ->
               match uu____8208 with
               | (p,w,e) ->
                   let uu____8225 = FStar_All.pipe_right p pat_to_string  in
                   let uu____8228 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8233 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____8233
                      in
                   let uu____8236 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____8225 uu____8228
                     uu____8236) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____8187 uu____8190
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____8245 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8248 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____8245 uu____8248
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____8257 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8260 = FStar_All.pipe_right t2 term_to_string  in
        let uu____8263 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____8257 uu____8260 uu____8263
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____8283 = FStar_All.pipe_right e term_to_string  in
        let uu____8286 =
          to_string_l " "
            (fun uu____8297  ->
               match uu____8297 with
               | (l,e1) ->
                   let uu____8305 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____8305)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____8283 uu____8286
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____8325 =
          to_string_l " "
            (fun uu____8336  ->
               match uu____8336 with
               | (l,e) ->
                   let uu____8344 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____8344)
            fields
           in
        FStar_Util.format1 "{%s}" uu____8325
    | Project (e,l) ->
        let uu____8351 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____8351 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____8374 = FStar_All.pipe_right b binder_to_string  in
        let uu____8377 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____8374 uu____8377
    | Product (b::[],t) when x.level = Kind ->
        let uu____8385 = FStar_All.pipe_right b binder_to_string  in
        let uu____8388 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____8385 uu____8388
    | Sum (binders,t) ->
        let uu____8406 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___7_8438  ->
                  match uu___7_8438 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1))
           in
        FStar_All.pipe_right uu____8406 (FStar_String.concat " & ")
    | QForall (bs,attr,(uu____8453,pats),t) ->
        let uu____8486 = to_string_l " " binder_to_string bs  in
        let uu____8489 =
          match attr with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some attr1 ->
              FStar_Ident.string_of_ident attr1
           in
        let uu____8494 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____8500 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format4 "forall %s. %s {:pattern %s} %s" uu____8486
          uu____8489 uu____8494 uu____8500
    | QExists (bs,attrs,(uu____8506,pats),t) ->
        let uu____8539 = to_string_l " " binder_to_string bs  in
        let uu____8542 =
          match attrs with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some attr ->
              FStar_Ident.string_of_ident attr
           in
        let uu____8547 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____8553 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format4 "exists %s. %s {:pattern %s} %s" uu____8539
          uu____8542 uu____8547 uu____8553
    | Refine (b,t) ->
        let uu____8559 = FStar_All.pipe_right b binder_to_string  in
        let uu____8562 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____8559 uu____8562
    | NamedTyp (x1,t) ->
        let uu____8568 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____8568
    | Paren t ->
        let uu____8573 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____8573
    | Product (bs,t) ->
        let uu____8583 =
          let uu____8585 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____8585 (FStar_String.concat ",")  in
        let uu____8600 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____8583
          uu____8600
    | Discrim lid ->
        let uu____8605 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format1 "%s?" uu____8605
    | Attributes ts ->
        let uu____8611 =
          let uu____8613 = FStar_List.map term_to_string ts  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8613  in
        FStar_Util.format1 "(attributes %s)" uu____8611
    | Antiquote t ->
        let uu____8625 = term_to_string t  in
        FStar_Util.format1 "(`#%s)" uu____8625
    | Quote (t,Static ) ->
        let uu____8629 = term_to_string t  in
        FStar_Util.format1 "(`(%s))" uu____8629
    | Quote (t,Dynamic ) ->
        let uu____8633 = term_to_string t  in
        FStar_Util.format1 "quote (%s)" uu____8633
    | VQuote t ->
        let uu____8637 = term_to_string t  in
        FStar_Util.format1 "`%%%s" uu____8637
    | CalcProof (rel,init1,steps) ->
        let uu____8647 = term_to_string rel  in
        let uu____8649 = term_to_string init1  in
        let uu____8651 =
          let uu____8653 = FStar_List.map calc_step_to_string steps  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8653  in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____8647 uu____8649
          uu____8651

and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____8664  ->
    match uu____8664 with
    | CalcStep (rel,just,next) ->
        let uu____8669 = term_to_string rel  in
        let uu____8671 = term_to_string just  in
        let uu____8673 = term_to_string next  in
        FStar_Util.format3 "%s{ %s } %s" uu____8669 uu____8671 uu____8673

and (binder_to_string : binder -> Prims.string) =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____8685 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____8685
      | Annotated (i,t) ->
          let uu____8691 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____8691
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____8697 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____8697 s

and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_8700  ->
    match uu___8_8700 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____8706 -> ""

and (pat_to_string : pattern -> Prims.string) =
  fun x  ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None ) -> "_"
    | PatWild uu____8713 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____8724 = FStar_All.pipe_right p pat_to_string  in
        let uu____8727 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____8724 uu____8727
    | PatTvar (i,aq) ->
        let uu____8737 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____8737 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____8746 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____8746 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____8753 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____8753
    | PatTuple (l,false ) ->
        let uu____8764 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____8764
    | PatTuple (l,true ) ->
        let uu____8775 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____8775
    | PatRecord l ->
        let uu____8786 =
          to_string_l "; "
            (fun uu____8797  ->
               match uu____8797 with
               | (f,e) ->
                   let uu____8805 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____8805) l
           in
        FStar_Util.format1 "{%s}" uu____8786
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____8815 = FStar_Ident.text_of_id op  in
        FStar_Util.format1 "(%s)" uu____8815
    | PatAscribed (p,(t,FStar_Pervasives_Native.None )) ->
        let uu____8828 = FStar_All.pipe_right p pat_to_string  in
        let uu____8831 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____8828 uu____8831
    | PatAscribed (p,(t,FStar_Pervasives_Native.Some tac)) ->
        let uu____8846 = FStar_All.pipe_right p pat_to_string  in
        let uu____8849 = FStar_All.pipe_right t term_to_string  in
        let uu____8852 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s:%s by %s)" uu____8846 uu____8849 uu____8852

and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___9_8856  ->
    match uu___9_8856 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____8870 =
          let uu____8872 = FStar_List.map term_to_string attrs  in
          FStar_All.pipe_right uu____8872 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____8870

let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____8895) ->
        let uu____8900 = FStar_Ident.lid_of_ids [i]  in [uu____8900]
    | PatApp (p1,uu____8902) -> head_id_of_pat p1
    | PatAscribed (p1,uu____8908) -> head_id_of_pat p1
    | uu____8921 -> []
  
let lids_of_let :
  'Auu____8927 .
    (pattern * 'Auu____8927) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____8962  ->
            match uu____8962 with | (p,uu____8970) -> head_id_of_pat p))
  
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___10_8977  ->
    match uu___10_8977 with
    | TyconAbstract (i,uu____8980,uu____8981) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____8991,uu____8992,uu____8993) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____9003,uu____9004,uu____9005) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____9035,uu____9036,uu____9037) ->
        i.FStar_Ident.idText
  
let (decl_to_string : decl -> Prims.string) =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.op_Hat "module " l.FStar_Ident.str
    | Open l -> Prims.op_Hat "open " l.FStar_Ident.str
    | Friend l -> Prims.op_Hat "friend " l.FStar_Ident.str
    | Include l -> Prims.op_Hat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____9095,pats) ->
        let uu____9109 =
          let uu____9111 =
            let uu____9115 = lids_of_let pats  in
            FStar_All.pipe_right uu____9115
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____9111 (FStar_String.concat ", ")  in
        Prims.op_Hat "let " uu____9109
    | Main uu____9132 -> "main ..."
    | Assume (i,uu____9135) -> Prims.op_Hat "assume " i.FStar_Ident.idText
    | Tycon (uu____9137,uu____9138,tys) ->
        let uu____9160 =
          let uu____9162 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____9187  ->
                    match uu____9187 with | (x,uu____9196) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____9162 (FStar_String.concat ", ")  in
        Prims.op_Hat "type " uu____9160
    | Val (i,uu____9208) -> Prims.op_Hat "val " i.FStar_Ident.idText
    | Exception (i,uu____9211) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____9218,uu____9219,uu____9220)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____9231,uu____9232)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | Splice (ids,t) ->
        let uu____9244 =
          let uu____9246 =
            let uu____9248 =
              FStar_List.map (fun i  -> i.FStar_Ident.idText) ids  in
            FStar_All.pipe_left (FStar_String.concat ";") uu____9248  in
          let uu____9260 =
            let uu____9262 =
              let uu____9264 = term_to_string t  in
              Prims.op_Hat uu____9264 ")"  in
            Prims.op_Hat "] (" uu____9262  in
          Prims.op_Hat uu____9246 uu____9260  in
        Prims.op_Hat "splice[" uu____9244
    | SubEffect uu____9269 -> "sub_effect"
    | Pragma uu____9271 -> "pragma"
    | Fsdoc uu____9273 -> "fsdoc"
  
let (modul_to_string : modul -> Prims.string) =
  fun m  ->
    match m with
    | Module (uu____9283,decls) ->
        let uu____9289 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____9289 (FStar_String.concat "\n")
    | Interface (uu____9304,decls,uu____9306) ->
        let uu____9313 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____9313 (FStar_String.concat "\n")
  
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id1  ->
    fun decl  ->
      match decl.d with
      | Val (id',uu____9342) -> FStar_Ident.ident_equals id1 id'
      | uu____9343 -> false
  
let (thunk : term -> term) =
  fun ens  ->
    let wildpat = mk_pattern (PatWild FStar_Pervasives_Native.None) ens.range
       in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
  
let (idents_of_binders :
  binder Prims.list -> FStar_Range.range -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    fun r  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun b  ->
              match b.b with
              | Variable i -> i
              | TVariable i -> i
              | Annotated (i,uu____9381) -> i
              | TAnnotated (i,uu____9383) -> i
              | NoName uu____9384 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))
  