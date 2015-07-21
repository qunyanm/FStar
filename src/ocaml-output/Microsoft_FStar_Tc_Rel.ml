
let new_kvar = (fun ( r ) ( binders ) -> (let wf = (fun ( k ) ( _28_39 ) -> (match (_28_39) with
| () -> begin
true
end))
in (let u = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in ((Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (u, (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)) r), u))))

let new_tvar = (fun ( r ) ( binders ) ( k ) -> (let wf = (fun ( t ) ( tk ) -> true)
in (let binders = ((Support.List.filter (fun ( x ) -> (not ((Microsoft_FStar_Absyn_Syntax.is_null_binder x))))) binders)
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _ -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let k' = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in ((Microsoft_FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r), uv))))
end)))))

let new_evar = (fun ( r ) ( binders ) ( t ) -> (let wf = (fun ( e ) ( t ) -> true)
in (let binders = ((Support.List.filter (fun ( x ) -> (not ((Microsoft_FStar_Absyn_Syntax.is_null_binder x))))) binders)
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _ -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, (Microsoft_FStar_Absyn_Syntax.mk_Total t)) None r)
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _ -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r), uv)
end))))
end)))))

type rel =
| EQ
| SUB
| SUBINV

type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

type ('a, 'b) problem =
{lhs : 'a; relation : rel; rhs : 'a; element : 'b option; logical_guard : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); scope : Microsoft_FStar_Absyn_Syntax.binders; reason : string list; loc : Support.Microsoft.FStar.Range.range; rank : int option}

type ('a, 'b) problem_t =
('a, 'b) problem

type prob =
| KProb of (Microsoft_FStar_Absyn_Syntax.knd, unit) problem
| TProb of (Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) problem
| EProb of (Microsoft_FStar_Absyn_Syntax.exp, unit) problem
| CProb of (Microsoft_FStar_Absyn_Syntax.comp, unit) problem

type probs =
prob list

type uvi =
| UK of (Microsoft_FStar_Absyn_Syntax.uvar_k * Microsoft_FStar_Absyn_Syntax.knd)
| UT of ((Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd) * Microsoft_FStar_Absyn_Syntax.typ)
| UE of ((Microsoft_FStar_Absyn_Syntax.uvar_e * Microsoft_FStar_Absyn_Syntax.typ) * Microsoft_FStar_Absyn_Syntax.exp)

type worklist =
{attempting : probs; deferred : (int * string * prob) list; subst : uvi list; ctr : int; slack_vars : (bool * Microsoft_FStar_Absyn_Syntax.typ) list; defer_ok : bool; smt_ok : bool; tcenv : Microsoft_FStar_Tc_Env.env}

type deferred =
{carry : (string * prob) list; slack : (bool * Microsoft_FStar_Absyn_Syntax.typ) list}

let no_deferred = {carry = []; slack = []}

type solution =
| Success of (uvi list * deferred)
| Failed of (prob * string)

let rel_to_string = (fun ( _28_1 ) -> (match (_28_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

let prob_to_string = (fun ( env ) ( _28_2 ) -> (match (_28_2) with
| KProb (p) -> begin
(Support.Microsoft.FStar.Util.format3 "\t%s\n\t\t%s\n\t%s" (Microsoft_FStar_Absyn_Print.kind_to_string p.lhs) (rel_to_string p.relation) (Microsoft_FStar_Absyn_Print.kind_to_string p.rhs))
end
| TProb (p) -> begin
(Support.Microsoft.FStar.Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" (((Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.lhs))::((Microsoft_FStar_Absyn_Print.tag_of_typ p.lhs))::((rel_to_string p.relation))::(((Support.List.hd) p.reason))::((Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.rhs))::((Microsoft_FStar_Absyn_Print.tag_of_typ p.rhs))::((Microsoft_FStar_Tc_Normalize.formula_norm_to_string env (Support.Prims.fst p.logical_guard)))::[]))
end
| EProb (p) -> begin
(Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.lhs) (rel_to_string p.relation) (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.rhs))
end
| CProb (p) -> begin
(Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs) (rel_to_string p.relation) (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs))
end))

let uvi_to_string = (fun ( env ) ( uvi ) -> (let str = (fun ( u ) -> if (! (Microsoft_FStar_Options.hide_uvar_nums)) then begin
"?"
end else begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id u))
end)
in (match (uvi) with
| UK ((u, _)) -> begin
((Support.Microsoft.FStar.Util.format1 "UK %s") (str u))
end
| UT (((u, _), t)) -> begin
((fun ( x ) -> (Support.Microsoft.FStar.Util.format2 "UT %s %s" x (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t))) (str u))
end
| UE (((u, _), _)) -> begin
((Support.Microsoft.FStar.Util.format1 "UE %s") (str u))
end)))

let invert_rel = (fun ( _28_3 ) -> (match (_28_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

let invert = (fun ( p ) -> (let _28_165 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _28_165.element; logical_guard = _28_165.logical_guard; scope = _28_165.scope; reason = _28_165.reason; loc = _28_165.loc; rank = _28_165.rank}))

let maybe_invert = (fun ( p ) -> if (p.relation = SUBINV) then begin
(invert p)
end else begin
p
end)

let maybe_invert_p = (fun ( _28_4 ) -> (match (_28_4) with
| KProb (p) -> begin
KProb ((maybe_invert p))
end
| TProb (p) -> begin
TProb ((maybe_invert p))
end
| EProb (p) -> begin
EProb ((maybe_invert p))
end
| CProb (p) -> begin
CProb ((maybe_invert p))
end))

let vary_rel = (fun ( rel ) ( _28_5 ) -> (match (_28_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_rel = (fun ( _28_6 ) -> (match (_28_6) with
| KProb (p) -> begin
p.relation
end
| TProb (p) -> begin
p.relation
end
| EProb (p) -> begin
p.relation
end
| CProb (p) -> begin
p.relation
end))

let p_reason = (fun ( _28_7 ) -> (match (_28_7) with
| KProb (p) -> begin
p.reason
end
| TProb (p) -> begin
p.reason
end
| EProb (p) -> begin
p.reason
end
| CProb (p) -> begin
p.reason
end))

let p_loc = (fun ( _28_8 ) -> (match (_28_8) with
| KProb (p) -> begin
p.loc
end
| TProb (p) -> begin
p.loc
end
| EProb (p) -> begin
p.loc
end
| CProb (p) -> begin
p.loc
end))

let p_context = (fun ( _28_9 ) -> (match (_28_9) with
| KProb (p) -> begin
p.scope
end
| TProb (p) -> begin
p.scope
end
| EProb (p) -> begin
p.scope
end
| CProb (p) -> begin
p.scope
end))

let p_guard = (fun ( _28_10 ) -> (match (_28_10) with
| KProb (p) -> begin
p.logical_guard
end
| TProb (p) -> begin
p.logical_guard
end
| EProb (p) -> begin
p.logical_guard
end
| CProb (p) -> begin
p.logical_guard
end))

let p_scope = (fun ( _28_11 ) -> (match (_28_11) with
| KProb (p) -> begin
p.scope
end
| TProb (p) -> begin
p.scope
end
| EProb (p) -> begin
p.scope
end
| CProb (p) -> begin
p.scope
end))

let p_invert = (fun ( _28_12 ) -> (match (_28_12) with
| KProb (p) -> begin
KProb ((invert p))
end
| TProb (p) -> begin
TProb ((invert p))
end
| EProb (p) -> begin
EProb ((invert p))
end
| CProb (p) -> begin
CProb ((invert p))
end))

let is_top_level_prob = (fun ( p ) -> (((Support.List.length) (p_reason p)) = 1))

let mk_problem = (fun ( scope ) ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (new_tvar (p_loc orig) scope Microsoft_FStar_Absyn_Syntax.ktype); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let new_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (new_tvar (Microsoft_FStar_Tc_Env.get_range env) (Microsoft_FStar_Tc_Env.binders env) Microsoft_FStar_Absyn_Syntax.ktype); scope = []; reason = (reason)::[]; loc = loc; rank = None})

let problem_using_guard = (fun ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun ( problem ) ( x ) ( phi ) -> (match (problem.element) with
| None -> begin
(Microsoft_FStar_Absyn_Util.close_forall (((Microsoft_FStar_Absyn_Syntax.v_binder x))::[]) phi)
end
| Some (e) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ ((Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, e)))::[]) phi)
end))

let solve_prob' = (fun ( resolve_ok ) ( prob ) ( logical_guard ) ( uvis ) ( wl ) -> (let phi = (match (logical_guard) with
| None -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _28_284 = (p_guard prob)
in (match (_28_284) with
| (_, uv) -> begin
(let _28_292 = (match ((Microsoft_FStar_Absyn_Util.compress_typ uv).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uvar, k)) -> begin
(let phi = (Microsoft_FStar_Absyn_Util.close_for_kind phi k)
in (Microsoft_FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _ -> begin
if (not (resolve_ok)) then begin
(failwith "Impossible: this instance has already been assigned a solution")
end
end)
in (match (uvis) with
| [] -> begin
wl
end
| _ -> begin
(let _28_297 = if ((Microsoft_FStar_Tc_Env.debug wl.tcenv) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Extending solution: %s\n" ((Support.String.concat ", ") (Support.List.map (uvi_to_string wl.tcenv) uvis)))
end
in (let _28_299 = wl
in {attempting = _28_299.attempting; deferred = _28_299.deferred; subst = (Support.List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _28_299.slack_vars; defer_ok = _28_299.defer_ok; smt_ok = _28_299.smt_ok; tcenv = _28_299.tcenv}))
end))
end))))

let extend_solution = (fun ( sol ) ( wl ) -> (let _28_303 = wl
in {attempting = _28_303.attempting; deferred = _28_303.deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _28_303.slack_vars; defer_ok = _28_303.defer_ok; smt_ok = _28_303.smt_ok; tcenv = _28_303.tcenv}))

let solve_prob = (fun ( prob ) ( logical_guard ) ( uvis ) ( wl ) -> (solve_prob' false prob logical_guard uvis wl))

let explain = (fun ( env ) ( d ) ( s ) -> (Support.Microsoft.FStar.Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" (Support.Microsoft.FStar.Range.string_of_range (p_loc d)) (prob_to_string env d) ((Support.String.concat "\n\t>") (p_reason d)) s))

let empty_worklist = (fun ( env ) -> {attempting = []; deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun ( env ) ( prob ) -> (let _28_315 = (empty_worklist env)
in {attempting = (prob)::[]; deferred = _28_315.deferred; subst = _28_315.subst; ctr = _28_315.ctr; slack_vars = _28_315.slack_vars; defer_ok = _28_315.defer_ok; smt_ok = _28_315.smt_ok; tcenv = _28_315.tcenv}))

let wl_of_guard = (fun ( env ) ( g ) -> (let _28_319 = (empty_worklist env)
in {attempting = (Support.List.map (Support.Prims.snd) g.carry); deferred = _28_319.deferred; subst = _28_319.subst; ctr = _28_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _28_319.smt_ok; tcenv = _28_319.tcenv}))

let defer = (fun ( reason ) ( prob ) ( wl ) -> (let _28_324 = wl
in {attempting = _28_324.attempting; deferred = ((wl.ctr, reason, prob))::wl.deferred; subst = _28_324.subst; ctr = _28_324.ctr; slack_vars = _28_324.slack_vars; defer_ok = _28_324.defer_ok; smt_ok = _28_324.smt_ok; tcenv = _28_324.tcenv}))

let attempt = (fun ( probs ) ( wl ) -> (let _28_328 = wl
in {attempting = (Support.List.append probs wl.attempting); deferred = _28_328.deferred; subst = _28_328.subst; ctr = _28_328.ctr; slack_vars = _28_328.slack_vars; defer_ok = _28_328.defer_ok; smt_ok = _28_328.smt_ok; tcenv = _28_328.tcenv}))

let add_slack_mul = (fun ( slack ) ( wl ) -> (let _28_332 = wl
in {attempting = _28_332.attempting; deferred = _28_332.deferred; subst = _28_332.subst; ctr = _28_332.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _28_332.defer_ok; smt_ok = _28_332.smt_ok; tcenv = _28_332.tcenv}))

let add_slack_add = (fun ( slack ) ( wl ) -> (let _28_336 = wl
in {attempting = _28_336.attempting; deferred = _28_336.deferred; subst = _28_336.subst; ctr = _28_336.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _28_336.defer_ok; smt_ok = _28_336.smt_ok; tcenv = _28_336.tcenv}))

let giveup = (fun ( env ) ( reason ) ( prob ) -> (let _28_341 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Failed %s:\n%s\n" reason (prob_to_string env prob))
end
in Failed ((prob, reason))))

let commit = (fun ( env ) ( uvis ) -> ((Support.List.iter (fun ( _28_13 ) -> (match (_28_13) with
| UK ((u, k)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u k)
end
| UT (((u, k), t)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u t)
end
| UE (((u, _), e)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u e)
end))) uvis))

let find_uvar_k = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _28_14 ) -> (match (_28_14) with
| UK ((u, t)) -> begin
if (Support.Microsoft.FStar.Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _ -> begin
None
end))))

let find_uvar_t = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _28_15 ) -> (match (_28_15) with
| UT (((u, _), t)) -> begin
if (Support.Microsoft.FStar.Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _ -> begin
None
end))))

let find_uvar_e = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _28_16 ) -> (match (_28_16) with
| UE (((u, _), t)) -> begin
if (Support.Microsoft.FStar.Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _ -> begin
None
end))))

let simplify_formula = (fun ( env ) ( f ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ = (fun ( env ) ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
((Support.Microsoft.FStar.Util.Inl (norm_targ env t)), (Support.Prims.snd a))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
((Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env v)), (Support.Prims.snd a))
end))

let whnf = (fun ( env ) ( t ) -> (Microsoft_FStar_Absyn_Util.compress_typ (Microsoft_FStar_Tc_Normalize.whnf env t)))

let sn = (fun ( env ) ( t ) -> (Microsoft_FStar_Absyn_Util.compress_typ (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env t)))

let sn_binders = (fun ( env ) ( binders ) -> ((Support.List.map (fun ( _28_17 ) -> (match (_28_17) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((let _28_417 = a
in {Microsoft_FStar_Absyn_Syntax.v = _28_417.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env a.Microsoft_FStar_Absyn_Syntax.sort); Microsoft_FStar_Absyn_Syntax.p = _28_417.Microsoft_FStar_Absyn_Syntax.p})), imp)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((let _28_423 = x
in {Microsoft_FStar_Absyn_Syntax.v = _28_423.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = (norm_targ env x.Microsoft_FStar_Absyn_Syntax.sort); Microsoft_FStar_Absyn_Syntax.p = _28_423.Microsoft_FStar_Absyn_Syntax.p})), imp)
end))) binders))

let whnf_k = (fun ( env ) ( k ) -> (Microsoft_FStar_Absyn_Util.compress_kind (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env k)))

let whnf_e = (fun ( env ) ( e ) -> (Microsoft_FStar_Absyn_Util.compress_exp (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env e)))

let rec compress_k = (fun ( env ) ( wl ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, actuals)) -> begin
(match ((find_uvar_k uv wl.subst)) with
| None -> begin
k
end
| Some (k') -> begin
(match (k'.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((formals, body)) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind (Microsoft_FStar_Absyn_Util.subst_of_list formals actuals) body)
in (compress_k env wl k))
end
| _ -> begin
if ((Support.List.length actuals) = 0) then begin
(compress_k env wl k')
end else begin
(failwith "Wrong arity for kind unifier")
end
end)
end)
end
| _ -> begin
k
end)))

let rec compress = (fun ( env ) ( wl ) ( t ) -> (let t = (whnf env (Microsoft_FStar_Absyn_Util.unmeta_typ t))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _ -> begin
t
end)
end
| _ -> begin
t
end)))

let rec compress_e = (fun ( env ) ( wl ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(compress_e env wl e')
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.Microsoft_FStar_Absyn_Syntax.pos))
end)
end
| _ -> begin
e
end)))

let normalize_refinement = (fun ( env ) ( wl ) ( t0 ) -> (Microsoft_FStar_Tc_Normalize.normalize_refinement env (compress env wl t0)))

let base_and_refinement = (fun ( env ) ( wl ) ( t1 ) -> (let rec aux = (fun ( norm ) ( t1 ) -> (match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
if norm then begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement env wl t1)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "impossible: Got %s ... %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string tt) (Microsoft_FStar_Absyn_Print.tag_of_typ tt)))
end)
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(let _28_554 = (aux true (normalize_refinement env wl t1))
in (match (_28_554) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _ -> begin
(t2', refinement)
end)
end))
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "impossible (outer): Got %s ... %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.tag_of_typ t1)))
end))
in (aux false (compress env wl t1))))

let unrefine = (fun ( env ) ( t ) -> ((Support.Prims.fst) (base_and_refinement env (empty_worklist env) t)))

let trivial_refinement = (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t), Microsoft_FStar_Absyn_Util.t_true))

let as_refinement = (fun ( env ) ( wl ) ( t ) -> (let _28_588 = (base_and_refinement env wl t)
in (match (_28_588) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some ((x, phi)) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun ( _28_596 ) -> (match (_28_596) with
| (t_base, refopt) -> begin
(let _28_604 = (match (refopt) with
| Some ((y, phi)) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_28_604) with
| (y, phi) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in ((Support.Microsoft.FStar.Util.for_some (fun ( _28_613 ) -> (match (_28_613) with
| (uvt, _) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uvt (Support.Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end))) ((Support.Microsoft.FStar.Util.set_elements) uvs.Microsoft_FStar_Absyn_Syntax.uvars_t))))

let occurs_check = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let occurs_ok = (not ((occurs env wl uk t)))
in (let msg = if occurs_ok then begin
None
end else begin
Some ((Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" (Microsoft_FStar_Absyn_Print.uvar_t_to_string uk) (Microsoft_FStar_Absyn_Print.typ_to_string t) ((Support.String.concat ", ") ((Support.List.map (uvi_to_string env)) wl.subst))))
end
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun ( env ) ( wl ) ( uk ) ( fvs ) ( t ) -> (let fvs_t = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (let _28_647 = (occurs_check env wl uk t)
in (match (_28_647) with
| (occurs_ok, msg) -> begin
(occurs_ok, (Microsoft_FStar_Absyn_Util.fvs_included fvs_t fvs), (msg, fvs, fvs_t))
end))))

let occurs_check_e = (fun ( env ) ( ut ) ( e ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((Support.Microsoft.FStar.Util.set_mem ut uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)))
in (let msg = if occurs_ok then begin
None
end else begin
Some ((Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" (Microsoft_FStar_Absyn_Print.uvar_e_to_string ut) ((Support.String.concat ", ") ((Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string) (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e))) (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)))
end
in (occurs_ok, msg)))))

let intersect_vars = (fun ( v1 ) ( v2 ) -> (let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v2)
in (Microsoft_FStar_Absyn_Syntax.binders_of_freevars {Microsoft_FStar_Absyn_Syntax.ftvs = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs); Microsoft_FStar_Absyn_Syntax.fxvs = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)}))))

let binders_eq = (fun ( v1 ) ( v2 ) -> (((Support.List.length v1) = (Support.List.length v2)) && (Support.List.forall2 (fun ( ax1 ) ( ax2 ) -> (match (((Support.Prims.fst ax1), (Support.Prims.fst ax2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq x y)
end
| _ -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun ( env ) ( seen ) ( arg ) -> (let hd = (norm_arg env arg)
in (match (((Support.Prims.fst) hd)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun ( _28_18 ) -> (match (_28_18) with
| (Support.Microsoft.FStar.Util.Inl (b), _) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))) seen) then begin
None
end else begin
Some ((Support.Microsoft.FStar.Util.Inl (a), (Support.Prims.snd hd)))
end
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_bvar (x); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun ( _28_19 ) -> (match (_28_19) with
| (Support.Microsoft.FStar.Util.Inr (y), _) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))) seen) then begin
None
end else begin
Some ((Support.Microsoft.FStar.Util.Inr (x), (Support.Prims.snd hd)))
end
end
| _ -> begin
None
end)))

let rec pat_vars = (fun ( env ) ( seen ) ( args ) -> (match (args) with
| [] -> begin
Some ((Support.List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _28_728 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Not a pattern: %s\n" (Microsoft_FStar_Absyn_Print.arg_to_string hd))
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

let destruct_flex_t = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(t, uv, k, [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(t, uv, k, args)
end
| _ -> begin
(failwith "Not a flex-uvar")
end))

let destruct_flex_e = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)) -> begin
(e, uv, k, [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(e, uv, k, args)
end
| _ -> begin
(failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun ( env ) ( t ) -> (let _28_784 = (destruct_flex_t t)
in (match (_28_784) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _ -> begin
((t, uv, k, args), None)
end)
end)))

type match_result =
| MisMatch
| HeadMatch
| FullMatch

let head_match = (fun ( _28_20 ) -> (match (_28_20) with
| MisMatch -> begin
MisMatch
end
| _ -> begin
HeadMatch
end))

let rec head_matches = (fun ( env ) ( t1 ) ( t2 ) -> (match (((Microsoft_FStar_Absyn_Util.unmeta_typ t1).Microsoft_FStar_Absyn_Syntax.n, (Microsoft_FStar_Absyn_Util.unmeta_typ t2).Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (x), Microsoft_FStar_Absyn_Syntax.Typ_btvar (y)) -> begin
if (Microsoft_FStar_Absyn_Util.bvar_eq x y) then begin
FullMatch
end else begin
MisMatch
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (f), Microsoft_FStar_Absyn_Syntax.Typ_const (g)) -> begin
if (Microsoft_FStar_Absyn_Util.fvar_eq f g) then begin
FullMatch
end else begin
MisMatch
end
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) -> begin
MisMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _))) -> begin
(head_match (head_matches env x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), _) -> begin
(head_match (head_matches env x.Microsoft_FStar_Absyn_Syntax.sort t2))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _))) -> begin
(head_match (head_matches env t1 x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_), Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) -> begin
HeadMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _)), Microsoft_FStar_Absyn_Syntax.Typ_app ((head', _))) -> begin
(head_matches env head head')
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _)), _) -> begin
(head_matches env head t2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _))) -> begin
(head_matches env t1 head)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _))) -> begin
if (Support.Microsoft.FStar.Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
HeadMatch
end
| _ -> begin
MisMatch
end))

let head_matches_delta = (fun ( env ) ( wl ) ( t1 ) ( t2 ) -> (let success = (fun ( d ) ( r ) ( t1 ) ( t2 ) -> (r, if d then begin
Some ((t1, t2))
end else begin
None
end))
in (let fail = (fun ( _28_910 ) -> (match (_28_910) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun ( d ) ( t1 ) ( t2 ) -> (match ((head_matches env t1 t2)) with
| MisMatch -> begin
if d then begin
(fail ())
end else begin
(let t1 = (normalize_refinement env wl t1)
in (let t2 = (normalize_refinement env wl t2)
in (aux true t1 t2)))
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux false t1 t2)))))

let decompose_binder = (fun ( bs ) ( v_ktec ) ( rebuild_base ) -> (let fail = (fun ( _28_924 ) -> (match (_28_924) with
| () -> begin
(failwith "Bad reconstruction")
end))
in (let rebuild = (fun ( ktecs ) -> (let rec aux = (fun ( new_bs ) ( bs ) ( ktecs ) -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (Support.List.rev new_bs) ktec)
end
| ((Support.Microsoft.FStar.Util.Inl (a), imp)::rest, Microsoft_FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inl ((let _28_946 = a
in {Microsoft_FStar_Absyn_Syntax.v = _28_946.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _28_946.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((Support.Microsoft.FStar.Util.Inr (x), imp)::rest, Microsoft_FStar_Absyn_Syntax.T ((t, _))::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inr ((let _28_962 = x
in {Microsoft_FStar_Absyn_Syntax.v = _28_962.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _28_962.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _ -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun ( _28_969 ) ( _28_21 ) -> (match (_28_969) with
| (binders, b_ktecs) -> begin
(match (_28_21) with
| [] -> begin
(Support.List.rev (((None, COVARIANT, v_ktec))::b_ktecs))
end
| hd::rest -> begin
(let bopt = if (Microsoft_FStar_Absyn_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (let b_ktec = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(bopt, CONTRAVARIANT, Microsoft_FStar_Absyn_Syntax.K (a.Microsoft_FStar_Absyn_Syntax.sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(bopt, CONTRAVARIANT, Microsoft_FStar_Absyn_Syntax.T ((x.Microsoft_FStar_Absyn_Syntax.sort, Some (Microsoft_FStar_Absyn_Syntax.ktype))))
end)
in (let binders' = (match (bopt) with
| None -> begin
binders
end
| Some (hd) -> begin
(Support.List.append binders ((hd)::[]))
end)
in (mk_b_ktecs (binders', (b_ktec)::b_ktecs) rest))))
end)
end))
in (rebuild, (mk_b_ktecs ([], []) bs))))))

let rec decompose_kind = (fun ( env ) ( k ) -> (let fail = (fun ( _28_988 ) -> (match (_28_988) with
| () -> begin
(failwith "Bad reconstruction")
end))
in (let k0 = k
in (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(let rebuild = (fun ( _28_22 ) -> (match (_28_22) with
| [] -> begin
k
end
| _ -> begin
(fail ())
end))
in (rebuild, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(decompose_binder bs (Microsoft_FStar_Absyn_Syntax.K (k)) (fun ( bs ) ( _28_23 ) -> (match (_28_23) with
| Microsoft_FStar_Absyn_Syntax.K (k) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(fail ())
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(decompose_kind env k)
end
| _ -> begin
(failwith "Impossible")
end)))))

let rec decompose_typ = (fun ( env ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun ( t' ) -> ((head_matches env t t') <> MisMatch))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((hd, args)) -> begin
(let rebuild = (fun ( args' ) -> (let args = (Support.List.map2 (fun ( x ) ( y ) -> (match ((x, y)) with
| ((Support.Microsoft.FStar.Util.Inl (_), imp), Microsoft_FStar_Absyn_Syntax.T ((t, _))) -> begin
(Support.Microsoft.FStar.Util.Inl (t), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (_), imp), Microsoft_FStar_Absyn_Syntax.E (e)) -> begin
(Support.Microsoft.FStar.Util.Inr (e), imp)
end
| _ -> begin
(failwith "Bad reconstruction")
end)) args args')
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let b_ktecs = ((Support.List.map (fun ( _28_24 ) -> (match (_28_24) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))) args)
in (rebuild, matches, b_ktecs)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _28_1074 = (decompose_binder bs (Microsoft_FStar_Absyn_Syntax.C (c)) (fun ( bs ) ( _28_25 ) -> (match (_28_25) with
| Microsoft_FStar_Absyn_Syntax.C (c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(failwith "Bad reconstruction")
end)))
in (match (_28_1074) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _ -> begin
(let rebuild = (fun ( _28_26 ) -> (match (_28_26) with
| [] -> begin
t
end
| _ -> begin
(failwith "Bad reconstruction")
end))
in (rebuild, (fun ( t ) -> true), []))
end))))

let un_T = (fun ( _28_27 ) -> (match (_28_27) with
| Microsoft_FStar_Absyn_Syntax.T ((x, _)) -> begin
x
end
| _ -> begin
(failwith "impossible")
end))

let arg_of_ktec = (fun ( _28_28 ) -> (match (_28_28) with
| Microsoft_FStar_Absyn_Syntax.T ((t, _)) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Microsoft_FStar_Absyn_Syntax.E (e) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| _ -> begin
(failwith "Impossible")
end))

let imitation_sub_probs = (fun ( orig ) ( env ) ( scope ) ( ps ) ( qs ) -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun ( scope ) ( args ) ( q ) -> (match (q) with
| (_, variance, Microsoft_FStar_Absyn_Syntax.K (ki)) -> begin
(let _28_1120 = (new_kvar r scope)
in (match (_28_1120) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (Microsoft_FStar_Absyn_Syntax.K (gi_xs), KProb ((mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm"))))
end))
end
| (_, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, kopt))) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(Microsoft_FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _28_1136 = (new_tvar r scope k)
in (match (_28_1136) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, Some (k))), TProb ((mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm"))))
end)))
end
| (_, variance, Microsoft_FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.recompute_typ ei)
in (let _28_1147 = (new_evar r scope t)
in (match (_28_1147) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (Microsoft_FStar_Absyn_Syntax.E (gi_xs), EProb ((mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm"))))
end)))
end
| (_, _, Microsoft_FStar_Absyn_Syntax.C (_)) -> begin
(failwith "impos")
end))
in (let rec aux = (fun ( scope ) ( args ) ( qs ) -> (match (qs) with
| [] -> begin
([], [], Microsoft_FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _28_1230 = (match (q) with
| (bopt, variance, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Total (ti); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match ((sub_prob scope args (bopt, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))) with
| (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, _)), prob) -> begin
(Microsoft_FStar_Absyn_Syntax.C ((Microsoft_FStar_Absyn_Syntax.mk_Total gi_xs)), (prob)::[])
end
| _ -> begin
(failwith "impossible")
end)
end
| (_, _, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (c); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let components = ((Support.List.map (fun ( _28_29 ) -> (match (_28_29) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))) c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let components = ((None, COVARIANT, Microsoft_FStar_Absyn_Syntax.T ((c.Microsoft_FStar_Absyn_Syntax.result_typ, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))::components
in (let _28_1221 = ((Support.List.unzip) (Support.List.map (sub_prob scope args) components))
in (match (_28_1221) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = (un_T (Support.List.hd ktecs)); Microsoft_FStar_Absyn_Syntax.effect_args = ((Support.List.map arg_of_ktec) (Support.List.tl ktecs)); Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags})
in (Microsoft_FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _ -> begin
(let _28_1227 = (sub_prob scope args q)
in (match (_28_1227) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_28_1230) with
| (ktec, probs) -> begin
(let _28_1243 = (match (q) with
| (Some (b), _, _) -> begin
(Some (b), (b)::scope, ((Microsoft_FStar_Absyn_Util.arg_of_non_null_binder b))::args)
end
| _ -> begin
(None, scope, args)
end)
in (match (_28_1243) with
| (bopt, scope, args) -> begin
(let _28_1247 = (aux scope args qs)
in (match (_28_1247) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(Microsoft_FStar_Absyn_Util.mk_conj_l ((f)::((Support.List.map (fun ( prob ) -> ((Support.Prims.fst) (p_guard prob)))) probs)))
end
| Some (b) -> begin
(Microsoft_FStar_Absyn_Util.mk_conj_l (((Microsoft_FStar_Absyn_Util.close_forall ((b)::[]) f))::((Support.List.map (fun ( prob ) -> ((Support.Prims.fst) (p_guard prob)))) probs)))
end)
in ((Support.List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); upper : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); flag : bool ref}

let fix_slack_uv = (fun ( _28_1260 ) ( mul ) -> (match (_28_1260) with
| (uv, k) -> begin
(let inst = if mul then begin
(Microsoft_FStar_Absyn_Util.close_for_kind Microsoft_FStar_Absyn_Util.t_true k)
end else begin
(Microsoft_FStar_Absyn_Util.close_for_kind Microsoft_FStar_Absyn_Util.t_false k)
end
in (Microsoft_FStar_Absyn_Util.unchecked_unify uv inst))
end))

let fix_slack_vars = (fun ( slack ) -> ((Support.List.iter (fun ( _28_1266 ) -> (match (_28_1266) with
| (mul, s) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_typ s).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(fix_slack_uv (uv, k) mul)
end
| _ -> begin
()
end)
end))) slack))

let fix_slack = (fun ( slack ) -> (let _28_1280 = ((destruct_flex_t) (Support.Prims.snd slack.lower))
in (match (_28_1280) with
| (_, ul, kl, _) -> begin
(let _28_1287 = ((destruct_flex_t) (Support.Prims.snd slack.upper))
in (match (_28_1287) with
| (_, uh, kh, _) -> begin
(let _28_1288 = (fix_slack_uv (ul, kl) false)
in (let _28_1290 = (fix_slack_uv (uh, kh) true)
in (let _28_1292 = (Support.ST.op_Colon_Equals slack.flag true)
in (Microsoft_FStar_Absyn_Util.mk_conj (Support.Prims.fst slack.lower) (Support.Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun ( env ) ( slack ) -> (let xs = ((Support.Microsoft.FStar.Util.must) ((Support.Prims.snd) (destruct_flex_pattern env (Support.Prims.snd slack.lower))))
in ((new_tvar (Support.Prims.fst slack.lower).Microsoft_FStar_Absyn_Syntax.pos xs Microsoft_FStar_Absyn_Syntax.ktype), xs)))

let new_slack_formula = (fun ( p ) ( env ) ( wl ) ( xs ) ( low ) ( high ) -> (let _28_1305 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_28_1305) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _28_1309 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_28_1309) with
| (high_var, uv2) -> begin
(let wl = (add_slack_mul uv2 wl)
in (let low = (match (low) with
| None -> begin
(Microsoft_FStar_Absyn_Util.mk_disj Microsoft_FStar_Absyn_Util.t_false low_var)
end
| Some (f) -> begin
(Microsoft_FStar_Absyn_Util.mk_disj f low_var)
end)
in (let high = (match (high) with
| None -> begin
(Microsoft_FStar_Absyn_Util.mk_conj Microsoft_FStar_Absyn_Util.t_true high_var)
end
| Some (f) -> begin
(Microsoft_FStar_Absyn_Util.mk_conj f high_var)
end)
in ((Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((low, high, (Support.Microsoft.FStar.Util.mk_ref false))))), wl))))
end)))
end)))

let destruct_slack = (fun ( env ) ( wl ) ( phi ) -> (let rec destruct = (fun ( conn_lid ) ( mk_conn ) ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl (lhs), _)::(Support.Microsoft.FStar.Util.Inl (rhs), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
Some ((lhs, rhs))
end
| _ -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some ((rest, uvar)) -> begin
Some (((mk_conn lhs rest), uvar))
end)
end))
end
| _ -> begin
None
end))
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((phi1, phi2, flag))) -> begin
if (! (flag)) then begin
Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.unmeta_typ phi))
end else begin
(let low = ((destruct Microsoft_FStar_Absyn_Const.or_lid Microsoft_FStar_Absyn_Util.mk_disj) (compress env wl phi1))
in (let hi = ((destruct Microsoft_FStar_Absyn_Const.and_lid Microsoft_FStar_Absyn_Util.mk_disj) (compress env wl phi2))
in (match ((low, hi)) with
| (None, None) -> begin
(let _28_1391 = (Support.ST.op_Colon_Equals flag true)
in Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.unmeta_typ phi)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
Support.Microsoft.FStar.Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end
end
| _ -> begin
Support.Microsoft.FStar.Util.Inl (phi)
end))))

let rec eq_typ = (fun ( t1 ) ( t2 ) -> (let t1 = (Microsoft_FStar_Absyn_Util.compress_typ t1)
in (let t2 = (Microsoft_FStar_Absyn_Util.compress_typ t2)
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (f), Microsoft_FStar_Absyn_Syntax.Typ_const (g)) -> begin
(Microsoft_FStar_Absyn_Util.fvar_eq f g)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u1, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u2, _))) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent u1 u2)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Typ_app ((h2, args2))) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _ -> begin
false
end))))
and eq_exp = (fun ( e1 ) ( e2 ) -> (let e1 = (Microsoft_FStar_Absyn_Util.compress_exp e1)
in (let e2 = (Microsoft_FStar_Absyn_Util.compress_exp e2)
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (a), Microsoft_FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _))) -> begin
(Microsoft_FStar_Absyn_Util.fvar_eq f g)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (c), Microsoft_FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((h2, args2))) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _ -> begin
false
end))))
and eq_args = (fun ( a1 ) ( a2 ) -> if ((Support.List.length a1) = (Support.List.length a2)) then begin
(Support.List.forall2 (fun ( a1 ) ( a2 ) -> (match ((a1, a2)) with
| ((Support.Microsoft.FStar.Util.Inl (t), _), (Support.Microsoft.FStar.Util.Inl (s), _)) -> begin
(eq_typ t s)
end
| ((Support.Microsoft.FStar.Util.Inr (e), _), (Support.Microsoft.FStar.Util.Inr (f), _)) -> begin
(eq_exp e f)
end
| _ -> begin
false
end)) a1 a2)
end else begin
false
end)

type flex_t =
(Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd * Microsoft_FStar_Absyn_Syntax.args)

type im_or_proj_t =
((Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd) * Microsoft_FStar_Absyn_Syntax.arg list * Microsoft_FStar_Absyn_Syntax.binders * ((Microsoft_FStar_Absyn_Syntax.ktec list  ->  Microsoft_FStar_Absyn_Syntax.typ) * (Microsoft_FStar_Absyn_Syntax.typ  ->  bool) * (Microsoft_FStar_Absyn_Syntax.binder option * variance * Microsoft_FStar_Absyn_Syntax.ktec) list))

let rigid_rigid = 0

let flex_rigid_eq = 1

let flex_refine_inner = 2

let flex_refine = 3

let flex_rigid = 4

let rigid_flex = 5

let refine_flex = 6

let flex_flex = 7

let compress_prob = (fun ( wl ) ( p ) -> (match (p) with
| KProb (p) -> begin
KProb ((let _28_1514 = p
in {lhs = (compress_k wl.tcenv wl p.lhs); relation = _28_1514.relation; rhs = (compress_k wl.tcenv wl p.rhs); element = _28_1514.element; logical_guard = _28_1514.logical_guard; scope = _28_1514.scope; reason = _28_1514.reason; loc = _28_1514.loc; rank = _28_1514.rank}))
end
| TProb (p) -> begin
TProb ((let _28_1518 = p
in {lhs = (compress wl.tcenv wl p.lhs); relation = _28_1518.relation; rhs = (compress wl.tcenv wl p.rhs); element = _28_1518.element; logical_guard = _28_1518.logical_guard; scope = _28_1518.scope; reason = _28_1518.reason; loc = _28_1518.loc; rank = _28_1518.rank}))
end
| EProb (p) -> begin
EProb ((let _28_1522 = p
in {lhs = (compress_e wl.tcenv wl p.lhs); relation = _28_1522.relation; rhs = (compress_e wl.tcenv wl p.rhs); element = _28_1522.element; logical_guard = _28_1522.logical_guard; scope = _28_1522.scope; reason = _28_1522.reason; loc = _28_1522.loc; rank = _28_1522.rank}))
end
| CProb (_) -> begin
p
end))

let rank = (fun ( wl ) ( prob ) -> (let prob = (maybe_invert_p (compress_prob wl prob))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.Microsoft_FStar_Absyn_Syntax.n, kp.rhs.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_), Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
flex_flex
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_), _) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
flex_rigid
end
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
rigid_flex
end
end
| (_, _) -> begin
rigid_rigid
end)
in (rank, KProb ((let _28_1557 = kp
in {lhs = _28_1557.lhs; relation = _28_1557.relation; rhs = _28_1557.rhs; element = _28_1557.element; logical_guard = _28_1557.logical_guard; scope = _28_1557.scope; reason = _28_1557.reason; loc = _28_1557.loc; rank = Some (rank)}))))
end
| TProb (tp) -> begin
(let _28_1564 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_28_1564) with
| (lh, _) -> begin
(let _28_1568 = (Microsoft_FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_28_1568) with
| (rh, _) -> begin
(let _28_1624 = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(flex_flex, tp)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _) -> begin
(let _28_1596 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_28_1596) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _ -> begin
(let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (rank, (let _28_1601 = tp
in {lhs = _28_1601.lhs; relation = _28_1601.relation; rhs = (force_refinement (b, ref_opt)); element = _28_1601.element; logical_guard = _28_1601.logical_guard; scope = _28_1601.scope; reason = _28_1601.reason; loc = _28_1601.loc; rank = _28_1601.rank})))
end)
end))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(let _28_1611 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_28_1611) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _ -> begin
(refine_flex, (let _28_1615 = tp
in {lhs = (force_refinement (b, ref_opt)); relation = _28_1615.relation; rhs = _28_1615.rhs; element = _28_1615.element; logical_guard = _28_1615.logical_guard; scope = _28_1615.scope; reason = _28_1615.reason; loc = _28_1615.loc; rank = _28_1615.rank}))
end)
end))
end
| (_, _) -> begin
(rigid_rigid, tp)
end)
in (match (_28_1624) with
| (rank, tp) -> begin
(rank, TProb ((let _28_1625 = tp
in {lhs = _28_1625.lhs; relation = _28_1625.relation; rhs = _28_1625.rhs; element = _28_1625.element; logical_guard = _28_1625.logical_guard; scope = _28_1625.scope; reason = _28_1625.reason; loc = _28_1625.loc; rank = Some (rank)})))
end))
end))
end))
end
| EProb (ep) -> begin
(let _28_1632 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_28_1632) with
| (lh, _) -> begin
(let _28_1636 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_28_1636) with
| (rh, _) -> begin
(let rank = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
flex_flex
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_, _) -> begin
rigid_rigid
end)
in (rank, EProb ((let _28_1662 = ep
in {lhs = _28_1662.lhs; relation = _28_1662.relation; rhs = _28_1662.rhs; element = _28_1662.element; logical_guard = _28_1662.logical_guard; scope = _28_1662.scope; reason = _28_1662.reason; loc = _28_1662.loc; rank = Some (rank)}))))
end))
end))
end
| CProb (cp) -> begin
(rigid_rigid, CProb ((let _28_1666 = cp
in {lhs = _28_1666.lhs; relation = _28_1666.relation; rhs = _28_1666.rhs; element = _28_1666.element; logical_guard = _28_1666.logical_guard; scope = _28_1666.scope; reason = _28_1666.reason; loc = _28_1666.loc; rank = Some (rigid_rigid)})))
end)))

let next_prob = (fun ( wl ) -> (let rec aux = (fun ( _28_1673 ) ( probs ) -> (match (_28_1673) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _28_1681 = (rank wl hd)
in (match (_28_1681) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
(Some (hd), (Support.List.append out tl), rank)
end
| Some (m) -> begin
(Some (hd), (Support.List.append out ((m)::tl)), rank)
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux (rank, Some (hd), out) tl)
end
| Some (m) -> begin
(aux (rank, Some (hd), (m)::out) tl)
end)
end else begin
(aux (min_rank, min, (hd)::out) tl)
end
end
end))
end)
end))
in (aux ((flex_flex + 1), None, []) wl.attempting)))

let is_flex_rigid = (fun ( rank ) -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

let rec solve_flex_rigid_join = (fun ( env ) ( tp ) ( wl ) -> (let _28_1692 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Trying to solve by joining refinements:%s\n" (prob_to_string env (TProb (tp))))
end
in (let _28_1696 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_28_1696) with
| (u, args) -> begin
(let _28_1702 = (0, 1, 2, 3, 4)
in (match (_28_1702) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun ( i ) ( j ) -> if (i < j) then begin
j
end else begin
i
end)
in (let base_types_match = (fun ( t1 ) ( t2 ) -> (let _28_1711 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_28_1711) with
| (h1, args1) -> begin
(let _28_1715 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_28_1715) with
| (h2, _) -> begin
(match ((h1.Microsoft_FStar_Absyn_Syntax.n, h2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (tc1), Microsoft_FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals tc1.Microsoft_FStar_Absyn_Syntax.v tc2.Microsoft_FStar_Absyn_Syntax.v) then begin
if ((Support.List.length args1) = 0) then begin
Some ([])
end else begin
Some ((TProb ((new_problem env t1 EQ t2 None t1.Microsoft_FStar_Absyn_Syntax.pos "joining refinements")))::[])
end
end else begin
None
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (Microsoft_FStar_Absyn_Util.bvar_eq a b) then begin
Some ([])
end else begin
None
end
end
| _ -> begin
None
end)
end))
end)))
in (let conjoin = (fun ( t1 ) ( t2 ) -> (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi1)), Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, phi2))) -> begin
(let m = (base_types_match x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ (Microsoft_FStar_Absyn_Util.mk_subst_one_binder (Microsoft_FStar_Absyn_Syntax.v_binder x) (Microsoft_FStar_Absyn_Syntax.v_binder y)) phi2)
in Some (((Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, (Microsoft_FStar_Absyn_Util.mk_conj phi1 phi2)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t1.Microsoft_FStar_Absyn_Syntax.pos), m)))
end))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _))) -> begin
(let m = (base_types_match t1 y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), _) -> begin
(let m = (base_types_match x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _ -> begin
(let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end))
in (let tt = u
in (match (tt.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)) -> begin
(let _28_1803 = ((Support.List.partition (fun ( _28_30 ) -> (match (_28_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _28_1789 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_28_1789) with
| (u', _) -> begin
(match ((compress env wl u').Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv uv')
end
| _ -> begin
false
end)
end))
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))) wl.attempting)
in (match (_28_1803) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun ( _28_1807 ) ( tps ) -> (match (_28_1807) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((conjoin bound (compress env wl hd.rhs))) with
| Some ((bound, sub)) -> begin
(make_upper_bound (bound, (Support.List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _ -> begin
None
end)
end))
in (match ((make_upper_bound ((compress env wl tp.rhs), []) upper_bounds)) with
| None -> begin
(let _28_1822 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.print_string "No upper bounds\n")
end
in None)
end
| Some ((rhs_bound, sub_probs)) -> begin
(let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (let _28_1829 = wl
in {attempting = sub_probs; deferred = _28_1829.deferred; subst = _28_1829.subst; ctr = _28_1829.ctr; slack_vars = _28_1829.slack_vars; defer_ok = _28_1829.defer_ok; smt_ok = _28_1829.smt_ok; tcenv = _28_1829.tcenv}))) with
| Success ((subst, _)) -> begin
(let wl = (let _28_1836 = wl
in {attempting = rest; deferred = _28_1836.deferred; subst = []; ctr = _28_1836.ctr; slack_vars = _28_1836.slack_vars; defer_ok = _28_1836.defer_ok; smt_ok = _28_1836.smt_ok; tcenv = _28_1836.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _28_1842 = (Support.List.fold_left (fun ( wl ) ( p ) -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _ -> begin
None
end))
end))
end))
end
| _ -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve = (fun ( env ) ( probs ) -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _28_1855 = probs
in {attempting = tl; deferred = _28_1855.deferred; subst = _28_1855.subst; ctr = _28_1855.ctr; slack_vars = _28_1855.slack_vars; defer_ok = _28_1855.defer_ok; smt_ok = _28_1855.smt_ok; tcenv = _28_1855.tcenv})
in (match (hd) with
| KProb (kp) -> begin
(solve_k' env (maybe_invert kp) probs)
end
| TProb (tp) -> begin
if ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) && (not ((! (Microsoft_FStar_Options.no_slack))))) then begin
(match ((solve_flex_rigid_join env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end else begin
(solve_t' env (maybe_invert tp) probs)
end
end
| EProb (ep) -> begin
(solve_e' env (maybe_invert ep) probs)
end
| CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end))
end
| (None, _, _) -> begin
(match (probs.deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _ -> begin
(let _28_1886 = ((Support.List.partition (fun ( _28_1883 ) -> (match (_28_1883) with
| (c, _, _) -> begin
(c < probs.ctr)
end))) probs.deferred)
in (match (_28_1886) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
Success ((probs.subst, {carry = (Support.List.map (fun ( _28_1892 ) -> (match (_28_1892) with
| (_, x, y) -> begin
(x, y)
end)) probs.deferred); slack = probs.slack_vars}))
end
| _ -> begin
(solve env (let _28_1895 = probs
in {attempting = ((Support.List.map (fun ( _28_1902 ) -> (match (_28_1902) with
| (_, _, y) -> begin
y
end))) attempt); deferred = rest; subst = _28_1895.subst; ctr = _28_1895.ctr; slack_vars = _28_1895.slack_vars; defer_ok = _28_1895.defer_ok; smt_ok = _28_1895.smt_ok; tcenv = _28_1895.tcenv}))
end)
end))
end)
end))
and solve_binders = (fun ( env ) ( bs1 ) ( bs2 ) ( orig ) ( wl ) ( rhs ) -> (let rec aux = (fun ( scope ) ( env ) ( subst ) ( xs ) ( ys ) -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs scope env subst)
in (let formula = ((Support.Prims.fst) (p_guard rhs_prob))
in Support.Microsoft.FStar.Util.Inl (((rhs_prob)::[], formula))))
end
| (((Support.Microsoft.FStar.Util.Inl (_), _)::_, (Support.Microsoft.FStar.Util.Inr (_), _)::_)) | (((Support.Microsoft.FStar.Util.Inr (_), _)::_, (Support.Microsoft.FStar.Util.Inl (_), _)::_)) -> begin
Support.Microsoft.FStar.Util.Inr ("sort mismatch")
end
| (hd1::xs, hd2::ys) -> begin
(let subst = (Support.List.append (Microsoft_FStar_Absyn_Util.mk_subst_one_binder hd2 hd1) subst)
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.binding_of_binder hd2))
in (let prob = (match (((Support.Prims.fst hd1), (Support.Prims.fst hd2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
KProb ((mk_problem ((hd2)::scope) orig (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort) (invert_rel (p_rel orig)) b.Microsoft_FStar_Absyn_Syntax.sort None "Formal type parameter"))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
TProb ((mk_problem ((hd2)::scope) orig (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort) (invert_rel (p_rel orig)) y.Microsoft_FStar_Absyn_Syntax.sort None "Formal value parameter"))
end
| _ -> begin
(failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
Support.Microsoft.FStar.Util.Inr (msg)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let phi = (Microsoft_FStar_Absyn_Util.mk_conj ((Support.Prims.fst) (p_guard prob)) (Microsoft_FStar_Absyn_Util.close_forall ((hd2)::[]) phi))
in Support.Microsoft.FStar.Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _ -> begin
Support.Microsoft.FStar.Util.Inr ("arity mismatch")
end))
in (let scope = (Microsoft_FStar_Tc_Env.binders env)
in (match ((aux scope env [] bs1 bs2)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
(giveup env msg orig)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_k = (fun ( env ) ( problem ) ( wl ) -> (match ((compress_prob wl (KProb (problem)))) with
| KProb (p) -> begin
(solve_k' env p wl)
end
| _ -> begin
(failwith "impossible")
end))
and solve_k' = (fun ( env ) ( problem ) ( wl ) -> (let orig = KProb (problem)
in if (Support.Microsoft.FStar.Util.physical_equality problem.lhs problem.rhs) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in if (Support.Microsoft.FStar.Util.physical_equality k1 k2) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let imitate_k = (fun ( _28_2019 ) -> (match (_28_2019) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _28_2024 = (imitation_sub_probs orig env xs ps qs)
in (match (_28_2024) with
| (sub_probs, gs_xs, f) -> begin
(let im = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, (h gs_xs)) r)
in (let wl = (solve_prob orig (Some (f)) ((UK ((u, im)))::[]) wl)
in (solve env (attempt sub_probs wl))))
end)))
end))
in (let flex_rigid = (fun ( rel ) ( u ) ( args ) ( k ) -> (let maybe_vars1 = (pat_vars env [] args)
in (match (maybe_vars1) with
| Some (xs) -> begin
(let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (Microsoft_FStar_Absyn_Util.freevars_kind k2)
in (let uvs2 = (Microsoft_FStar_Absyn_Util.uvars_in_kind k2)
in if (((Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)) && (not ((Support.Microsoft.FStar.Util.set_mem u uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k)))) then begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, k2) r)
in (solve env (solve_prob orig None ((UK ((u, k1)))::[]) wl)))
end else begin
(imitate_k (rel, u, (Microsoft_FStar_Absyn_Util.args_of_non_null_binders xs), xs, (decompose_kind env k)))
end)))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.Microsoft_FStar_Absyn_Syntax.n, k2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_type, Microsoft_FStar_Absyn_Syntax.Kind_type)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, Microsoft_FStar_Absyn_Syntax.Kind_effect)) -> begin
((solve env) (solve_prob orig None [] wl))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k1)), _) -> begin
(solve_k env (let _28_2054 = problem
in {lhs = k1; relation = _28_2054.relation; rhs = _28_2054.rhs; element = _28_2054.element; logical_guard = _28_2054.logical_guard; scope = _28_2054.scope; reason = _28_2054.reason; loc = _28_2054.loc; rank = _28_2054.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k2))) -> begin
(solve_k env (let _28_2064 = problem
in {lhs = _28_2064.lhs; relation = _28_2064.relation; rhs = k2; element = _28_2064.element; logical_guard = _28_2064.logical_guard; scope = _28_2064.scope; reason = _28_2064.reason; loc = _28_2064.loc; rank = _28_2064.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs1, k1')), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs2, k2'))) -> begin
(let sub_prob = (fun ( scope ) ( env ) ( subst ) -> KProb ((mk_problem scope orig (Microsoft_FStar_Absyn_Util.subst_kind subst k1') problem.relation k2' None "Arrow-kind result")))
in (solve_binders env bs1 bs2 orig wl sub_prob))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u1, args1)), Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u2, args2))) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
(giveup env "flex-flex: non patterns" (KProb (problem)))
end
| (Some (xs), Some (ys)) -> begin
if ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env wl)
end else begin
(let zs = (intersect_vars xs ys)
in (let _28_2107 = (new_kvar r zs)
in (match (_28_2107) with
| (u, _) -> begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args)), _) -> begin
(flex_rigid problem.relation u args k2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args))) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((Microsoft_FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_unknown)) -> begin
(failwith "Impossible")
end
| _ -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end))
end))
and solve_t = (fun ( env ) ( problem ) ( wl ) -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _ -> begin
(failwith "Impossible")
end)))
and solve_t' = (fun ( env ) ( problem ) ( wl ) -> (let giveup_or_defer = (fun ( orig ) ( msg ) -> if wl.defer_ok then begin
(let _28_2161 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" (prob_to_string env orig) msg)
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
in (let imitate_t = (fun ( orig ) ( env ) ( wl ) ( p ) -> (let _28_2178 = p
in (match (_28_2178) with
| ((u, k), ps, xs, (h, _, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _28_2184 = (imitation_sub_probs orig env xs ps qs)
in (match (_28_2184) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, (h gs_xs)) None r)
in (let _28_2186 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" (Microsoft_FStar_Absyn_Print.typ_to_string im) (Microsoft_FStar_Absyn_Print.tag_of_typ im) ((Support.String.concat ", ") (Support.List.map (prob_to_string env) sub_probs)) (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env formula))
end
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun ( orig ) ( env ) ( wl ) ( i ) ( p ) -> (let _28_2202 = p
in (match (_28_2202) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let pi = (Support.List.nth ps i)
in (let rec gs = (fun ( k ) -> (let _28_2209 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (match (_28_2209) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _28_2238 = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k_a = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _28_2222 = (new_tvar r xs k_a)
in (match (_28_2222) with
| (gi_xs, gi) -> begin
(let gi_xs = (Microsoft_FStar_Tc_Normalize.eta_expand env gi_xs)
in (let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, ps) (Some (k_a)) r)
in (let subst = if (Microsoft_FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, gi_xs)))::subst
end
in ((Microsoft_FStar_Absyn_Syntax.targ gi_xs), (Microsoft_FStar_Absyn_Syntax.targ gi_ps), subst))))
end)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t_x = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _28_2231 = (new_evar r xs t_x)
in (match (_28_2231) with
| (gi_xs, gi) -> begin
(let gi_xs = (Microsoft_FStar_Tc_Normalize.eta_expand_exp env gi_xs)
in (let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, ps) (Some (t_x)) r)
in (let subst = if (Microsoft_FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, gi_xs)))::subst
end
in ((Microsoft_FStar_Absyn_Syntax.varg gi_xs), (Microsoft_FStar_Absyn_Syntax.varg gi_ps), subst))))
end)))
end)
in (match (_28_2238) with
| (gi_xs, gi_ps, subst) -> begin
(let _28_2241 = (aux subst tl)
in (match (_28_2241) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match (((Support.Prims.fst pi), ((Support.Prims.fst) (Support.List.nth xs i)))) with
| (Support.Microsoft.FStar.Util.Inl (pi), Support.Microsoft.FStar.Util.Inl (xi)) -> begin
if (not ((matches pi))) then begin
None
end else begin
(let _28_2250 = (gs xi.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_28_2250) with
| (g_xs, _) -> begin
(let xi = (Microsoft_FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (xs, (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)) None r)
in (let sub = TProb ((mk_problem (p_scope orig) orig (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r) (p_rel orig) (h (Support.List.map (fun ( _28_2258 ) -> (match (_28_2258) with
| (_, _, y) -> begin
y
end)) qs)) None "projection"))
in (let _28_2260 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Projecting %s\n\tsubprob=%s\n" (Microsoft_FStar_Absyn_Print.typ_to_string proj) (prob_to_string env sub))
end
in (let wl = (solve_prob orig (Some (((Support.Prims.fst) (p_guard sub)))) ((UT ((u, proj)))::[]) wl)
in ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (solve env (attempt ((sub)::[]) wl))))))))
end))
end
end
| _ -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun ( orig ) ( lhs ) ( t2 ) ( wl ) -> (let _28_2276 = lhs
in (match (_28_2276) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ( ps ) -> (let xs = ((Support.Prims.fst) (Microsoft_FStar_Absyn_Util.kind_formals k))
in (let xs = (Microsoft_FStar_Absyn_Util.name_binders xs)
in ((uv, k), ps, xs, (decompose_typ env t2)))))
in (let rec imitate_or_project = (fun ( n ) ( st ) ( i ) -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
if (i = (- (1))) then begin
(match ((imitate_t orig env wl st)) with
| Failed (_) -> begin
(imitate_or_project n st (i + 1))
end
| sol -> begin
sol
end)
end else begin
(match ((project_t orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(imitate_or_project n st (i + 1))
end
| Some (sol) -> begin
sol
end)
end
end)
in (let check_head = (fun ( fvs1 ) ( t2 ) -> (let _28_2302 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_28_2302) with
| (hd, _) -> begin
(match (hd.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _ -> begin
(let fvs_hd = (Microsoft_FStar_Absyn_Util.freevars_typ hd)
in if (Microsoft_FStar_Absyn_Util.fvs_included fvs_hd fvs1) then begin
true
end else begin
(let _28_2315 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Free variables are %s" (Microsoft_FStar_Absyn_Print.freevars_to_string fvs_hd))
end
in false)
end)
end)
end)))
in (let imitate_ok = (fun ( t2 ) -> (let fvs_hd = (Microsoft_FStar_Absyn_Util.freevars_typ ((Support.Prims.fst) (Microsoft_FStar_Absyn_Util.head_and_args t2)))
in if (Support.Microsoft.FStar.Util.set_is_empty fvs_hd.Microsoft_FStar_Absyn_Syntax.ftvs) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(let t1 = (sn env t1)
in (let t2 = (sn env t2)
in (let fvs1 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (let fvs2 = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _28_2328 = (occurs_check env wl (uv, k) t2)
in (match (_28_2328) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig (Support.String.strcat "occurs-check failed: " (Support.Option.get msg)))
end else begin
if (Microsoft_FStar_Absyn_Util.fvs_included fvs2 fvs1) then begin
if ((Microsoft_FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ)) then begin
(imitate_t orig env wl (subterms args_lhs))
end else begin
(let _28_2329 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1) (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2))
end
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((sn_binders env vars), t2) None t1.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let wl = (solve_prob orig None ((UT (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(let _28_2336 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1) (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2))
end
in (imitate_or_project (Support.List.length args_lhs) (subterms args_lhs) (- (1))))
end else begin
(giveup env "free-variable check failed on a non-redex" orig)
end
end
end
end
end))))))
end
| None -> begin
if wl.defer_ok then begin
(solve env (defer "not a pattern" orig wl))
end else begin
if (check_head (Microsoft_FStar_Absyn_Util.freevars_typ t1) t2) then begin
(let im_ok = (imitate_ok t2)
in (let _28_2340 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Not a pattern (%s) ... %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end))
end
in (imitate_or_project (Support.List.length args_lhs) (subterms args_lhs) im_ok)))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (let flex_flex = (fun ( orig ) ( lhs ) ( rhs ) -> if (wl.defer_ok && ((p_rel orig) <> EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(let force_quasi_pattern = (fun ( xs_opt ) ( _28_2352 ) -> (match (_28_2352) with
| (t, u, k, args) -> begin
(let rec aux = (fun ( binders ) ( ys ) ( args ) -> (match (args) with
| [] -> begin
(let ys = (Support.List.rev ys)
in (let binders = (Support.List.rev binders)
in (let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _28_2364 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos ys kk)
in (match (_28_2364) with
| (t', _) -> begin
(let _28_2370 = (destruct_flex_t t')
in (match (_28_2370) with
| (u1_ys, u1, k1, _) -> begin
(let sol = UT (((u, k), (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun ( hd ) -> (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Syntax.t_binder ((Microsoft_FStar_Absyn_Util.gen_bvar_p a.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Tc_Recheck.recompute_kind a)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Syntax.v_binder ((Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Tc_Recheck.recompute_typ x)))
end))
in (let _28_2389 = (match ((pat_var_opt env ys hd)) with
| None -> begin
((new_binder hd), ys)
end
| Some (y) -> begin
(match (xs_opt) with
| None -> begin
(y, (y)::ys)
end
| Some (xs) -> begin
if ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Util.eq_binder y)) xs) then begin
(y, (y)::ys)
end else begin
((new_binder hd), ys)
end
end)
end)
in (match (_28_2389) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun ( wl ) ( _28_2395 ) ( _28_2399 ) ( k ) ( r ) -> (match ((_28_2395, _28_2399)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _28_2408 = (new_tvar r zs k)
in (match (_28_2408) with
| (u_zs, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _28_2412 = (occurs_check env wl (u1, k1) sub1)
in (match (_28_2412) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(let sol1 = UT (((u1, k1), sub1))
in if (Support.Microsoft.FStar.Unionfind.equivalent u1 u2) then begin
(let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (ys, u_zs) (Some (k2)) r)
in (let _28_2418 = (occurs_check env wl (u2, k2) sub2)
in (match (_28_2418) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(let sol2 = UT (((u2, k2), sub2))
in (let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end)))))
end
end))
in (let solve_one_pat = (fun ( _28_2426 ) ( _28_2431 ) -> (match ((_28_2426, _28_2431)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _28_2432 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.typ_to_string t2))
end
in if (Support.Microsoft.FStar.Unionfind.equivalent u1 u2) then begin
(let sub_probs = (Support.List.map2 (fun ( a ) ( b ) -> (let a = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Support.Prims.fst a), (Support.Prims.fst b))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
TProb ((mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index"))
end
| (Support.Microsoft.FStar.Util.Inr (t1), Support.Microsoft.FStar.Util.Inr (t2)) -> begin
EProb ((mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index"))
end
| _ -> begin
(failwith "Impossible")
end))) xs args2)
in (let guard = (Microsoft_FStar_Absyn_Util.mk_conj_l (Support.List.map (fun ( p ) -> ((Support.Prims.fst) (p_guard p))) sub_probs))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(let t2 = (sn env t2)
in (let rhs_vars = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _28_2458 = (occurs_check env wl (u1, k1) t2)
in (match (_28_2458) with
| (occurs_ok, _) -> begin
(let lhs_vars = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in if (occurs_ok && (Microsoft_FStar_Absyn_Util.fvs_included rhs_vars lhs_vars)) then begin
(let sol = UT (((u1, k1), (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.Microsoft_FStar_Absyn_Syntax.pos)))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (not (wl.defer_ok))) then begin
(let _28_2469 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_28_2469) with
| (sol, (_, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _28_2471 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (2): %s\n" (uvi_to_string env sol))
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _ -> begin
(giveup env "impossible" orig)
end)))
end))
end else begin
(giveup_or_defer orig "flex-flex constraint")
end
end)
end))))
end)
end))
in (let _28_2481 = lhs
in (match (_28_2481) with
| (t1, u1, k1, args1) -> begin
(let _28_2486 = rhs
in (match (_28_2486) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.Microsoft_FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl (u1, k1, xs) (u2, k2, ys) (Microsoft_FStar_Tc_Recheck.recompute_kind t2) t2.Microsoft_FStar_Absyn_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _ -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(let _28_2508 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_28_2508) with
| (sol, _) -> begin
(let wl = (extend_solution sol wl)
in (let _28_2510 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (1): %s\n" (uvi_to_string env sol))
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _ -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (let orig = TProb (problem)
in if (Support.Microsoft.FStar.Util.physical_equality problem.lhs problem.rhs) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in if (Support.Microsoft.FStar.Util.physical_equality t1 t2) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let _28_2519 = if (Microsoft_FStar_Tc_Env.debug env (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Attempting %s\n\tSubst is %s\n" (prob_to_string env orig) ((Support.String.concat "; ") (Support.List.map (uvi_to_string wl.tcenv) wl.subst)))
end
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun ( _28_2524 ) ( _28_2527 ) -> (match ((_28_2524, _28_2527)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun ( n ) ( bs ) ( mk_cod ) -> (let _28_2534 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_28_2534) with
| (bs, rest) -> begin
(bs, (mk_cod rest))
end)))
in (let l1 = (Support.List.length bs1)
in (let l2 = (Support.List.length bs2)
in if (l1 = l2) then begin
((bs1, (mk_cod1 [])), (bs2, (mk_cod2 [])))
end else begin
if (l1 > l2) then begin
((curry l2 bs1 mk_cod1), (bs2, (mk_cod2 [])))
end else begin
((bs1, (mk_cod1 [])), (curry l1 bs2 mk_cod2))
end
end)))
end))
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(solve env (solve_prob orig ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)) [] wl))
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs1, c1)), Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs2, c2))) -> begin
(let mk_c = (fun ( c ) ( _28_31 ) -> (match (_28_31) with
| [] -> begin
c
end
| bs -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.Microsoft_FStar_Absyn_Syntax.pos))
end))
in (let _28_2565 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_28_2565) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst c1)
in (let rel = if (! (Microsoft_FStar_Options.use_eq_at_higher_order)) then begin
EQ
end else begin
problem.relation
end
in (let _28_2571 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "(%s) Using relation %s at higher order\n" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range env)) (rel_to_string rel))
end
in CProb ((mk_problem scope orig c1 rel c2 None "function co-domain")))))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs1, t1')), Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs2, t2'))) -> begin
(let mk_t = (fun ( t ) ( _28_32 ) -> (match (_28_32) with
| [] -> begin
t
end
| bs -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let _28_2593 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_28_2593) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let t1' = (Microsoft_FStar_Absyn_Util.subst_typ subst t1')
in TProb ((mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let _28_2607 = (as_refinement env wl t1)
in (match (_28_2607) with
| (x1, phi1) -> begin
(let _28_2610 = (as_refinement env wl t2)
in (match (_28_2610) with
| (x2, phi2) -> begin
(let base_prob = TProb ((mk_problem (p_scope orig) orig x1.Microsoft_FStar_Absyn_Syntax.sort problem.relation x2.Microsoft_FStar_Absyn_Syntax.sort problem.element "refinement base type"))
in (let x1_for_x2 = (Microsoft_FStar_Absyn_Util.mk_subst_one_binder (Microsoft_FStar_Absyn_Syntax.v_binder x1) (Microsoft_FStar_Absyn_Syntax.v_binder x2))
in (let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun ( imp ) ( phi1 ) ( phi2 ) -> ((guard_on_element problem x1) (imp phi1 phi2)))
in (let fallback = (fun ( _28_2619 ) -> (match (_28_2619) with
| () -> begin
(let impl = if (problem.relation = EQ) then begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_iff phi1 phi2)
end else begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_imp phi1 phi2)
end
in (let guard = (Microsoft_FStar_Absyn_Util.mk_conj ((Support.Prims.fst) (p_guard base_prob)) impl)
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.relation = EQ) then begin
(let ref_prob = TProb ((mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula"))
in (match ((solve env (let _28_2624 = wl
in {attempting = (ref_prob)::[]; deferred = []; subst = _28_2624.subst; ctr = _28_2624.ctr; slack_vars = _28_2624.slack_vars; defer_ok = false; smt_ok = _28_2624.smt_ok; tcenv = _28_2624.tcenv}))) with
| Failed (_) -> begin
(fallback ())
end
| Success ((subst, _)) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_conj ((Support.Prims.fst) (p_guard base_prob)) ((guard_on_element problem x1) ((Support.Prims.fst) (p_guard ref_prob))))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))
end))
end else begin
(fallback ())
end)))))
end))
end))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(flex_flex orig (destruct_flex_t t1) (destruct_flex_t t2))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) when (problem.relation = EQ) -> begin
(solve_t_flex_rigid orig (destruct_flex_pattern env t1) t2 wl)
end
| ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) when (problem.relation = EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(let new_rel = if (! (Microsoft_FStar_Options.no_slack)) then begin
EQ
end else begin
problem.relation
end
in if (not ((is_top_level_prob orig))) then begin
(solve_t_flex_rigid (TProb ((let _28_2792 = problem
in {lhs = _28_2792.lhs; relation = new_rel; rhs = _28_2792.rhs; element = _28_2792.element; logical_guard = _28_2792.logical_guard; scope = _28_2792.scope; reason = _28_2792.reason; loc = _28_2792.loc; rank = _28_2792.rank}))) (destruct_flex_pattern env t1) t2 wl)
end else begin
(let _28_2796 = (base_and_refinement env wl t2)
in (match (_28_2796) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(solve_t_flex_rigid (TProb ((let _28_2798 = problem
in {lhs = _28_2798.lhs; relation = new_rel; rhs = _28_2798.rhs; element = _28_2798.element; logical_guard = _28_2798.logical_guard; scope = _28_2798.scope; reason = _28_2798.reason; loc = _28_2798.loc; rank = _28_2798.rank}))) (destruct_flex_pattern env t1) t_base wl)
end
| Some ((y, phi)) -> begin
(let y' = (let _28_2804 = y
in {Microsoft_FStar_Absyn_Syntax.v = _28_2804.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _28_2804.Microsoft_FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = TProb ((mk_problem problem.scope orig t1 new_rel y.Microsoft_FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type"))
in (let guard = (Microsoft_FStar_Absyn_Util.mk_conj ((Support.Prims.fst) (p_guard base_prob)) impl)
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end)
end
end
| ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
if wl.defer_ok then begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end else begin
(let _28_2839 = (base_and_refinement env wl t1)
in (match (_28_2839) with
| (t_base, _) -> begin
(solve_t env (let _28_2840 = problem
in {lhs = t_base; relation = EQ; rhs = _28_2840.rhs; element = _28_2840.element; logical_guard = _28_2840.logical_guard; scope = _28_2840.scope; reason = _28_2840.reason; loc = _28_2840.loc; rank = _28_2840.rank}) wl)
end))
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), _) -> begin
(let t2 = (force_refinement (base_and_refinement env wl t2))
in (solve_t env (let _28_2849 = problem
in {lhs = _28_2849.lhs; relation = _28_2849.relation; rhs = t2; element = _28_2849.element; logical_guard = _28_2849.logical_guard; scope = _28_2849.scope; reason = _28_2849.reason; loc = _28_2849.loc; rank = _28_2849.rank}) wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let t1 = (force_refinement (base_and_refinement env wl t1))
in (solve_t env (let _28_2858 = problem
in {lhs = t1; relation = _28_2858.relation; rhs = _28_2858.rhs; element = _28_2858.element; logical_guard = _28_2858.logical_guard; scope = _28_2858.scope; reason = _28_2858.reason; loc = _28_2858.loc; rank = _28_2858.rank}) wl))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _28_2898 = (head_matches_delta env wl t1 t2)
in (match (_28_2898) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _) -> begin
(let head1 = ((Support.Prims.fst) (Microsoft_FStar_Absyn_Util.head_and_args t1))
in (let head2 = ((Support.Prims.fst) (Microsoft_FStar_Absyn_Util.head_and_args t2))
in (let may_equate = (fun ( head ) -> (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Tc_Env.is_projector env tc.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(solve env (solve_prob orig ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)) [] wl))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_, Some ((t1, t2))) -> begin
(solve_t env (let _28_2921 = problem
in {lhs = t1; relation = _28_2921.relation; rhs = t2; element = _28_2921.element; logical_guard = _28_2921.logical_guard; scope = _28_2921.scope; reason = _28_2921.reason; loc = _28_2921.loc; rank = _28_2921.rank}) wl)
end
| (_, None) -> begin
(let _28_2927 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Head matches: %s and %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.typ_to_string t2))
end
in (let _28_2931 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_28_2931) with
| (head, args) -> begin
(let _28_2934 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_28_2934) with
| (head', args') -> begin
(let nargs = (Support.List.length args)
in if (nargs <> (Support.List.length args')) then begin
(giveup env (Support.Microsoft.FStar.Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" (Microsoft_FStar_Absyn_Print.typ_to_string head) (Microsoft_FStar_Absyn_Print.args_to_string args) (Microsoft_FStar_Absyn_Print.typ_to_string head') (Microsoft_FStar_Absyn_Print.args_to_string args')) orig)
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let _28_2938 = (base_and_refinement env wl t1)
in (match (_28_2938) with
| (base1, refinement1) -> begin
(let _28_2941 = (base_and_refinement env wl t2)
in (match (_28_2941) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _28_2945 = if ((head_matches env head head) <> FullMatch) then begin
(failwith (Support.Microsoft.FStar.Util.format2 "Assertion failed: expected full match of %s and %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string head) (Microsoft_FStar_Absyn_Print.typ_to_string head')))
end
in (let subprobs = (Support.List.map2 (fun ( a ) ( a' ) -> (match (((Support.Prims.fst a), (Support.Prims.fst a'))) with
| (Support.Microsoft.FStar.Util.Inl (t), Support.Microsoft.FStar.Util.Inl (t')) -> begin
TProb ((mk_problem (p_scope orig) orig t EQ t' None "type index"))
end
| (Support.Microsoft.FStar.Util.Inr (v), Support.Microsoft.FStar.Util.Inr (v')) -> begin
EProb ((mk_problem (p_scope orig) orig v EQ v' None "term index"))
end
| _ -> begin
(failwith "Impossible")
end)) args args')
in (let formula = (Microsoft_FStar_Absyn_Util.mk_conj_l (Support.List.map (fun ( p ) -> (Support.Prims.fst (p_guard p))) subprobs))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _ -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _28_2969 = problem
in {lhs = lhs; relation = _28_2969.relation; rhs = rhs; element = _28_2969.element; logical_guard = _28_2969.logical_guard; scope = _28_2969.scope; reason = _28_2969.reason; loc = _28_2969.loc; rank = _28_2969.rank}) wl)))
end)
end))
end))
end
end)
end))
end)))
end)
end))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_meta (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_delayed (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_meta (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_delayed (_))) -> begin
(failwith "Impossible")
end
| _ -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c = (fun ( env ) ( problem ) ( wl ) -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun ( t1 ) ( rel ) ( t2 ) ( reason ) -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun ( c1_comp ) ( c2_comp ) -> (let _28_3025 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ"))) then begin
(Support.Microsoft.FStar.Util.print_string "solve_c is using an equality constraint\n")
end
in (let sub_probs = (Support.List.map2 (fun ( arg1 ) ( arg2 ) -> (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
TProb ((sub_prob t1 EQ t2 "effect arg"))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
EProb ((sub_prob e1 EQ e2 "effect arg"))
end
| _ -> begin
(failwith "impossible")
end)) c1_comp.Microsoft_FStar_Absyn_Syntax.effect_args c2_comp.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let guard = (Microsoft_FStar_Absyn_Util.mk_conj_l (Support.List.map (fun ( p ) -> ((Support.Prims.fst) (p_guard p))) sub_probs))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (Support.Microsoft.FStar.Util.physical_equality c1 c2) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(let _28_3045 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "solve_c %s %s %s\n" (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1) (rel_to_string problem.relation) (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2))
end
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _28_3050 = (c1, c2)
in (match (_28_3050) with
| (c1_0, c2_0) -> begin
(match ((c1.Microsoft_FStar_Absyn_Syntax.n, c2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Total (t1), Microsoft_FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (Microsoft_FStar_Absyn_Syntax.Total (_), Microsoft_FStar_Absyn_Syntax.Comp (_)) -> begin
(solve_c env (let _28_3063 = problem
in {lhs = (Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)); relation = _28_3063.relation; rhs = _28_3063.rhs; element = _28_3063.element; logical_guard = _28_3063.logical_guard; scope = _28_3063.scope; reason = _28_3063.reason; loc = _28_3063.loc; rank = _28_3063.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Total (_)) -> begin
(solve_c env (let _28_3072 = problem
in {lhs = _28_3072.lhs; relation = _28_3072.relation; rhs = (Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2)); element = _28_3072.element; logical_guard = _28_3072.logical_guard; scope = _28_3072.scope; reason = _28_3072.reason; loc = _28_3072.loc; rank = _28_3072.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Comp (_)) -> begin
if (((Microsoft_FStar_Absyn_Util.is_ml_comp c1) && (Microsoft_FStar_Absyn_Util.is_ml_comp c2)) || ((Microsoft_FStar_Absyn_Util.is_total_comp c1) && ((Microsoft_FStar_Absyn_Util.is_total_comp c2) || (Microsoft_FStar_Absyn_Util.is_ml_comp c2)))) then begin
(solve_t env (problem_using_guard orig (Microsoft_FStar_Absyn_Util.comp_result c1) problem.relation (Microsoft_FStar_Absyn_Util.comp_result c2) None "result type") wl)
end else begin
(let c1_comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in (let c2_comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2)
in if ((problem.relation = EQ) && (Microsoft_FStar_Absyn_Syntax.lid_equals c1_comp.Microsoft_FStar_Absyn_Syntax.effect_name c2_comp.Microsoft_FStar_Absyn_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _28_3085 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "solve_c for %s and %s\n" c1.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str c2.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str)
end
in (match ((Microsoft_FStar_Tc_Env.monad_leq env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(giveup env (Support.Microsoft.FStar.Util.format2 "incompatible monad ordering: %s </: %s" (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name) (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)) orig)
end
| Some (edge) -> begin
if (problem.relation = EQ) then begin
(let _28_3105 = (match (c1.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp1), _)::(Support.Microsoft.FStar.Util.Inl (wlp1), _)::[] -> begin
(wp1, wlp1)
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Unexpected number of indices on a normalized effect (%s)" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Absyn_Syntax.range_of_lid c1.Microsoft_FStar_Absyn_Syntax.effect_name))))
end)
in (match (_28_3105) with
| (wp, wlp) -> begin
(let c1 = {Microsoft_FStar_Absyn_Syntax.effect_name = c2.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = ((Microsoft_FStar_Absyn_Syntax.targ (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wp)))::((Microsoft_FStar_Absyn_Syntax.targ (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wlp)))::[]; Microsoft_FStar_Absyn_Syntax.flags = c1.Microsoft_FStar_Absyn_Syntax.flags}
in (solve_eq c1 c2))
end))
end else begin
(let is_null_wp_2 = ((Support.Microsoft.FStar.Util.for_some (fun ( _28_33 ) -> (match (_28_33) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.MLEFFECT) | (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _ -> begin
false
end))) c2.Microsoft_FStar_Absyn_Syntax.flags)
in (let _28_3135 = (match ((c1.Microsoft_FStar_Absyn_Syntax.effect_args, c2.Microsoft_FStar_Absyn_Syntax.effect_args)) with
| ((Support.Microsoft.FStar.Util.Inl (wp1), _)::_, (Support.Microsoft.FStar.Util.Inl (wp2), _)::_) -> begin
(wp1, wp2)
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "Got effects %s and %s, expected normalized effects" (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name) (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)))
end)
in (match (_28_3135) with
| (wpc1, wpc2) -> begin
if (Support.Microsoft.FStar.Util.physical_equality wpc1 wpc2) then begin
(solve_t env (problem_using_guard orig c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ None "result type") wl)
end else begin
(let c2_decl = (Microsoft_FStar_Tc_Env.get_effect_decl env c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let g = if is_null_wp_2 then begin
(let _28_3137 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.print_string "Using trivial wp ... \n")
end
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (c2_decl.Microsoft_FStar_Absyn_Syntax.trivial, ((Microsoft_FStar_Absyn_Syntax.targ c1.Microsoft_FStar_Absyn_Syntax.result_typ))::((Microsoft_FStar_Absyn_Syntax.targ (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)))::[]) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r))
end else begin
(let wp2_imp_wp1 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_binop, ((Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ))::((Microsoft_FStar_Absyn_Syntax.targ wpc2))::((Microsoft_FStar_Absyn_Syntax.targ (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.imp_lid (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype))))::((Microsoft_FStar_Absyn_Syntax.targ (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)))::[]) None r)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_as_type, ((Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ))::((Microsoft_FStar_Absyn_Syntax.targ wp2_imp_wp1))::[]) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r))
end
in (let base_prob = TProb ((sub_prob c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ "result type"))
in (let wl = (solve_prob orig ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.mk_conj ((Support.Prims.fst) (p_guard base_prob)) g)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end
end))))
end))
end
end)
end))))
end))))))
and solve_e = (fun ( env ) ( problem ) ( wl ) -> (match ((compress_prob wl (EProb (problem)))) with
| EProb (p) -> begin
(solve_e' env p wl)
end
| _ -> begin
(failwith "Impossible")
end))
and solve_e' = (fun ( env ) ( problem ) ( wl ) -> (let problem = (let _28_3153 = problem
in {lhs = _28_3153.lhs; relation = EQ; rhs = _28_3153.rhs; element = _28_3153.element; logical_guard = _28_3153.logical_guard; scope = _28_3153.scope; reason = _28_3153.reason; loc = _28_3153.loc; rank = _28_3153.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun ( lhs ) ( rhs ) ( reason ) -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _28_3165 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Attempting:\n%s\n" (prob_to_string env orig))
end
in (let flex_rigid = (fun ( _28_3172 ) ( e2 ) -> (match (_28_3172) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun ( xs ) ( args2 ) -> (let _28_3199 = ((Support.List.unzip) ((Support.List.map (fun ( _28_34 ) -> (match (_28_34) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _28_3186 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos xs kk)
in (match (_28_3186) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in ((Support.Microsoft.FStar.Util.Inl (gi_xi), imp), TProb ((sub_prob gi_pi t "type index"))))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (let _28_3195 = (new_evar v.Microsoft_FStar_Absyn_Syntax.pos xs tt)
in (match (_28_3195) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.Microsoft_FStar_Absyn_Syntax.pos)
in ((Support.Microsoft.FStar.Util.Inr (gi_xi), imp), EProb ((sub_prob gi_pi v "expression index"))))
end)))
end))) args2))
in (match (_28_3199) with
| (gi_xi, gi_pi) -> begin
(let formula = (Microsoft_FStar_Absyn_Util.mk_conj_l (Support.List.map (fun ( p ) -> ((Support.Prims.fst) (p_guard p))) gi_pi))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun ( head2 ) ( args2 ) -> (let giveup = (fun ( reason ) -> (giveup env (Support.Microsoft.FStar.Util.format1 "flex-rigid: refusing to project expressions (%s)" reason) orig))
in (match ((Microsoft_FStar_Absyn_Util.compress_exp head2).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _28_3216 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_28_3216) with
| (all_xs, tres) -> begin
if ((Support.List.length all_xs) <> (Support.List.length args1)) then begin
(giveup (Support.Microsoft.FStar.Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" (Microsoft_FStar_Absyn_Print.binders_to_string ", " all_xs) (Microsoft_FStar_Absyn_Print.args_to_string args2)))
end else begin
(let rec aux = (fun ( xs ) ( args ) -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(failwith "impossible")
end
| ((Support.Microsoft.FStar.Util.Inl (_), _)::xs, (Support.Microsoft.FStar.Util.Inl (_), _)::args) -> begin
(aux xs args)
end
| ((Support.Microsoft.FStar.Util.Inr (xi), _)::xs, (Support.Microsoft.FStar.Util.Inr (arg), _)::args) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_exp arg).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (z) -> begin
if (Microsoft_FStar_Absyn_Util.bvar_eq y z) then begin
(let _28_3268 = (sub_problems all_xs args2)
in (match (_28_3268) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (all_xs, (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' ((Microsoft_FStar_Absyn_Util.bvar_to_exp xi), gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _28_3270 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1)) (Microsoft_FStar_Absyn_Print.exp_to_string sol) ((Support.String.concat "\n") ((Support.List.map (prob_to_string env)) gi_pi)))
end
in (solve env (attempt gi_pi (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)))))
end))
end else begin
(aux xs args)
end
end
| _ -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(giveup (Support.Microsoft.FStar.Util.format2 "type incorrect term---impossible: expected %s; got %s\n" (Microsoft_FStar_Absyn_Print.binder_to_string x) (Microsoft_FStar_Absyn_Print.arg_to_string arg)))
end))
in (aux (Support.List.rev all_xs) (Support.List.rev args1)))
end
end))
end
| _ -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun ( _28_3284 ) -> (match (_28_3284) with
| () -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end else begin
(let _28_3285 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Imitating expressions: %s =?= %s\n" (Microsoft_FStar_Absyn_Print.exp_to_string e1) (Microsoft_FStar_Absyn_Print.exp_to_string e2))
end
in (let _28_3289 = (Microsoft_FStar_Absyn_Util.head_and_args_e e2)
in (match (_28_3289) with
| (head2, args2) -> begin
(let fvhead = (Microsoft_FStar_Absyn_Util.freevars_exp head2)
in (let _28_3294 = (occurs_check_e env (u1, t1) head2)
in (match (_28_3294) with
| (occurs_ok, _) -> begin
if ((Microsoft_FStar_Absyn_Util.fvs_included fvhead Microsoft_FStar_Absyn_Syntax.no_fvs) && occurs_ok) then begin
(let _28_3302 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_28_3302) with
| (xs, tres) -> begin
(let _28_3306 = (sub_problems xs args2)
in (match (_28_3306) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)) None e1.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let _28_3312 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1)) (Microsoft_FStar_Absyn_Print.exp_to_string sol) ((Support.String.concat "\n") ((Support.List.map (prob_to_string env)) gi_pi)))
end
in (solve env (attempt gi_pi (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)))))
end))
end))
end else begin
if occurs_ok then begin
(project_e head2 args2)
end else begin
(giveup env "flex-rigid: occurs check failed" orig)
end
end
end)))
end)))
end
end))
in (match (maybe_vars1) with
| (None) | (Some ([])) -> begin
(imitate_or_project_e ())
end
| Some (xs) -> begin
(let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (Microsoft_FStar_Absyn_Util.freevars_exp e2)
in (let _28_3324 = (occurs_check_e env (u1, t1) e2)
in (match (_28_3324) with
| (occurs_ok, _) -> begin
if (((Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)) && occurs_ok) then begin
(let sol = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (solve env (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)))
end else begin
(imitate_or_project_e ())
end
end))))
end)))))
end))
in (let flex_flex = (fun ( _28_3331 ) ( _28_3336 ) -> (match ((_28_3331, _28_3336)) with
| ((e1, u1, t1, args1), (e2, u2, t2, args2)) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-flex: not a pattern" orig wl))
end else begin
(giveup env "flex-flex expressions not patterns" orig)
end
end
| (Some (xs), Some (ys)) -> begin
if ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env wl)
end else begin
(let zs = (intersect_vars xs ys)
in (let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (let _28_3357 = (new_evar (Microsoft_FStar_Tc_Env.get_range env) zs tt)
in (match (_28_3357) with
| (u, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (solve env (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl))))
end))))
end
end)))
end))
in (let smt_fallback = (fun ( e1 ) ( e2 ) -> if wl.smt_ok then begin
(let _28_3363 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Using SMT to solve:\n%s\n" (prob_to_string env orig))
end
in (let _28_3368 = (new_tvar (Microsoft_FStar_Tc_Env.get_range env) (Microsoft_FStar_Tc_Env.binders env) Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_28_3368) with
| (t, _) -> begin
(solve env (solve_prob orig ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)) [] wl))
end)))
end else begin
(giveup env "no SMT solution permitted" orig)
end)
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, _, _)), _) -> begin
(solve_e env (let _28_3379 = problem
in {lhs = e1; relation = _28_3379.relation; rhs = _28_3379.rhs; element = _28_3379.element; logical_guard = _28_3379.logical_guard; scope = _28_3379.scope; reason = _28_3379.reason; loc = _28_3379.loc; rank = _28_3379.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e2, _, _))) -> begin
(solve_e env (let _28_3391 = problem
in {lhs = _28_3391.lhs; relation = _28_3391.relation; rhs = e2; element = _28_3391.element; logical_guard = _28_3391.logical_guard; scope = _28_3391.scope; reason = _28_3391.reason; loc = _28_3391.loc; rank = _28_3391.rank}) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(flex_flex (destruct_flex_e e1) (destruct_flex_e e2))
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(flex_rigid (destruct_flex_e e1) e2)
end
| ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(flex_rigid (destruct_flex_e e2) e1)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1), Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
if (Microsoft_FStar_Absyn_Util.bvd_eq x1.Microsoft_FStar_Absyn_Syntax.v x1'.Microsoft_FStar_Absyn_Syntax.v) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(solve env (solve_prob orig ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.mk_eq (Microsoft_FStar_Tc_Recheck.recompute_typ e1) (Microsoft_FStar_Tc_Recheck.recompute_typ e2) e1 e2)) [] wl))
end
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1', _))) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv1'.Microsoft_FStar_Absyn_Syntax.v) then begin
(solve env (solve_prob orig None [] wl))
end else begin
(giveup env "free-variables unequal" orig)
end
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (s1), Microsoft_FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun ( s1 ) ( s2 ) -> (match ((s1, s2)) with
| (Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b1, _)), Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b2, _))) -> begin
(b1 = b2)
end
| (Microsoft_FStar_Absyn_Syntax.Const_string ((b1, _)), Microsoft_FStar_Absyn_Syntax.Const_string ((b2, _))) -> begin
(b1 = b2)
end
| _ -> begin
(s1 = s2)
end))
in if (const_eq s1 s1') then begin
(solve env (solve_prob orig None [] wl))
end else begin
(giveup env "constants unequal" orig)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _) -> begin
(solve_e env (let _28_3590 = problem
in {lhs = (whnf_e env e1); relation = _28_3590.relation; rhs = _28_3590.rhs; element = _28_3590.element; logical_guard = _28_3590.logical_guard; scope = _28_3590.scope; reason = _28_3590.reason; loc = _28_3590.loc; rank = _28_3590.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(solve_e env (let _28_3611 = problem
in {lhs = _28_3611.lhs; relation = _28_3611.relation; rhs = (whnf_e env e2); element = _28_3611.element; logical_guard = _28_3611.logical_guard; scope = _28_3611.scope; reason = _28_3611.reason; loc = _28_3611.loc; rank = _28_3611.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((head1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((head2, args2))) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun ( sub_probs ) ( wl ) ( args1 ) ( args2 ) -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_conj_l ((Support.List.map (Support.Prims.fst)) (Support.List.map p_guard sub_probs)))
in (let g = (simplify_formula env guard)
in (let g = (Microsoft_FStar_Absyn_Util.compress_typ g)
in (match (g.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
(solve env (solve_prob orig None wl.subst (let _28_3636 = orig_wl
in {attempting = _28_3636.attempting; deferred = _28_3636.deferred; subst = []; ctr = _28_3636.ctr; slack_vars = _28_3636.slack_vars; defer_ok = _28_3636.defer_ok; smt_ok = _28_3636.smt_ok; tcenv = _28_3636.tcenv})))
end
| _ -> begin
(let _28_3643 = (new_tvar (Microsoft_FStar_Tc_Env.get_range env) (Microsoft_FStar_Tc_Env.binders env) Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_28_3643) with
| (t, _) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_disj g (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2))
in (solve env (solve_prob orig (Some (guard)) wl.subst (let _28_3645 = orig_wl
in {attempting = _28_3645.attempting; deferred = _28_3645.deferred; subst = []; ctr = _28_3645.ctr; slack_vars = _28_3645.slack_vars; defer_ok = _28_3645.defer_ok; smt_ok = _28_3645.smt_ok; tcenv = _28_3645.tcenv}))))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
TProb ((mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg"))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
EProb ((mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg"))
end
| _ -> begin
(failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (let _28_3667 = wl
in {attempting = (prob)::[]; deferred = []; subst = _28_3667.subst; ctr = _28_3667.ctr; slack_vars = _28_3667.slack_vars; defer_ok = false; smt_ok = false; tcenv = _28_3667.tcenv}))) with
| Failed (_) -> begin
(smt_fallback e1 e2)
end
| Success ((subst, _)) -> begin
(solve_args ((prob)::sub_probs) (let _28_3677 = wl
in {attempting = _28_3677.attempting; deferred = _28_3677.deferred; subst = subst; ctr = _28_3677.ctr; slack_vars = _28_3677.slack_vars; defer_ok = _28_3677.defer_ok; smt_ok = _28_3677.smt_ok; tcenv = _28_3677.tcenv}) rest1 rest2)
end))
end
| _ -> begin
(failwith "Impossible: lengths defer")
end))
in (let rec match_head_and_args = (fun ( head1 ) ( head2 ) -> (match (((Microsoft_FStar_Absyn_Util.compress_exp head1).Microsoft_FStar_Absyn_Syntax.n, (Microsoft_FStar_Absyn_Util.compress_exp head2).Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) when ((Microsoft_FStar_Absyn_Util.bvar_eq x y) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _))) when (((Microsoft_FStar_Absyn_Util.fvar_eq f g) && (not ((Microsoft_FStar_Absyn_Util.is_interpreted f.Microsoft_FStar_Absyn_Syntax.v)))) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)), _) -> begin
(match_head_and_args e head2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _))) -> begin
(match_head_and_args head1 e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_), _) -> begin
(solve_e env (let _28_3726 = problem
in {lhs = (whnf_e env e1); relation = _28_3726.relation; rhs = _28_3726.rhs; element = _28_3726.element; logical_guard = _28_3726.logical_guard; scope = _28_3726.scope; reason = _28_3726.reason; loc = _28_3726.loc; rank = _28_3726.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(solve_e env (let _28_3734 = problem
in {lhs = _28_3734.lhs; relation = _28_3734.relation; rhs = (whnf_e env e2); element = _28_3734.element; logical_guard = _28_3734.logical_guard; scope = _28_3734.scope; reason = _28_3734.reason; loc = _28_3734.loc; rank = _28_3734.rank}) wl)
end
| _ -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _ -> begin
(let _28_3743 = (new_tvar (Microsoft_FStar_Tc_Env.get_range env) (Microsoft_FStar_Tc_Env.binders env) Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_28_3743) with
| (t, _) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _28_3745 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint1 "Emitting guard %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string guard))
end
in (solve env (solve_prob orig ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)) [] wl))))
end))
end)))))))))))

type guard_formula =
| Trivial
| NonTrivial of Microsoft_FStar_Absyn_Syntax.formula

type implicits =
((Microsoft_FStar_Absyn_Syntax.uvar_t * Support.Microsoft.FStar.Range.range), (Microsoft_FStar_Absyn_Syntax.uvar_e * Support.Microsoft.FStar.Range.range)) Support.Microsoft.FStar.Util.either list

type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}

let guard_to_string = (fun ( env ) ( g ) -> (let form = (match (g.guard_f) with
| Trivial -> begin
"trivial"
end
| NonTrivial (f) -> begin
if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
end else begin
"non-trivial"
end
end)
in (let carry = ((Support.String.concat ",\n") (Support.List.map (fun ( _28_3762 ) -> (match (_28_3762) with
| (_, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry))
in (Support.Microsoft.FStar.Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula = (fun ( g ) -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_f = (fun ( g ) -> g.guard_f)

let is_trivial = (fun ( g ) -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _} -> begin
true
end
| _ -> begin
false
end))

let trivial_guard = {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = []}

let abstract_guard = (fun ( x ) ( g ) -> (match (g) with
| (None) | (Some ({guard_f = Trivial; deferred = _; implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.guard_f) with
| NonTrivial (f) -> begin
f
end
| _ -> begin
(failwith "impossible")
end)
in Some ((let _28_3793 = g
in {guard_f = NonTrivial ((Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.v_binder x))::[], f) None f.Microsoft_FStar_Absyn_Syntax.pos)); deferred = _28_3793.deferred; implicits = _28_3793.implicits})))
end))

let apply_guard = (fun ( g ) ( e ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _28_3800 = g
in {guard_f = NonTrivial (((Microsoft_FStar_Absyn_Syntax.syn f.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (f, ((Microsoft_FStar_Absyn_Syntax.varg e))::[])))); deferred = _28_3800.deferred; implicits = _28_3800.implicits})
end))

let trivial = (fun ( t ) -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_) -> begin
(failwith "impossible")
end))

let conj_guard_f = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
NonTrivial ((Microsoft_FStar_Absyn_Util.mk_conj f1 f2))
end))

let check_trivial = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _ -> begin
NonTrivial (t)
end))

let imp_guard_f = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Trivial, g) -> begin
g
end
| (g, Trivial) -> begin
Trivial
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let imp = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

let binop_guard = (fun ( f ) ( g1 ) ( g2 ) -> {guard_f = (f g1.guard_f g2.guard_f); deferred = {carry = (Support.List.append g1.deferred.carry g2.deferred.carry); slack = (Support.List.append g1.deferred.slack g2.deferred.slack)}; implicits = (Support.List.append g1.implicits g2.implicits)})

let conj_guard = (fun ( g1 ) ( g2 ) -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun ( g1 ) ( g2 ) -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun ( binders ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _28_3850 = g
in {guard_f = NonTrivial ((Microsoft_FStar_Absyn_Util.close_forall binders f)); deferred = _28_3850.deferred; implicits = _28_3850.implicits})
end))

let mk_guard = (fun ( g ) ( ps ) ( slack ) ( locs ) -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel"))) then begin
(Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lhs) (rel_to_string rel) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env rhs))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun ( env ) ( t1 ) ( rel ) ( t2 ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar_p (Microsoft_FStar_Tc_Env.get_range env) t1)
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let p = (new_t_problem env t1 rel t2 ((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.bvar_to_exp x)) (Microsoft_FStar_Tc_Env.get_range env))
in (TProb (p), x)))))

let new_k_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel"))) then begin
(Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env lhs) (rel_to_string rel) (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env rhs))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let simplify_guard = (fun ( env ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _28_3884 = if (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High) then begin
(Support.Microsoft.FStar.Util.fprint1 "Simplifying guard %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string f))
end
in (let f = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _ -> begin
NonTrivial (f)
end)
in (let _28_3892 = g
in {guard_f = f; deferred = _28_3892.deferred; implicits = _28_3892.implicits}))))
end))

let solve_and_commit = (fun ( env ) ( probs ) ( err ) -> (let probs = if (! (Microsoft_FStar_Options.eager_inference)) then begin
(let _28_3897 = probs
in {attempting = _28_3897.attempting; deferred = _28_3897.deferred; subst = _28_3897.subst; ctr = _28_3897.ctr; slack_vars = _28_3897.slack_vars; defer_ok = false; smt_ok = _28_3897.smt_ok; tcenv = _28_3897.tcenv})
end else begin
probs
end
in (let sol = (solve env probs)
in (match (sol) with
| Success ((s, deferred)) -> begin
(let _28_3905 = (commit env s)
in Some (deferred))
end
| Failed ((d, s)) -> begin
(let _28_3911 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel"))) then begin
(Support.Microsoft.FStar.Util.print_string (explain env d s))
end
in (err (d, s)))
end))))

let with_guard = (fun ( env ) ( prob ) ( dopt ) -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
((fun ( __dataconst_1 ) -> Some (__dataconst_1)) (simplify_guard env {guard_f = NonTrivial (((Support.Prims.fst) (p_guard prob))); deferred = d; implicits = []}))
end))

let try_keq = (fun ( env ) ( k1 ) ( k2 ) -> (let _28_3922 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "try_keq of %s and %s\n" (Microsoft_FStar_Absyn_Print.kind_to_string k1) (Microsoft_FStar_Absyn_Print.kind_to_string k2))
end
in (let prob = KProb ((new_k_problem env (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1) EQ (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k2) None (Microsoft_FStar_Tc_Env.get_range env)))
in ((with_guard env prob) (solve_and_commit env (singleton env prob) (fun ( _28_3925 ) -> None))))))

let keq = (fun ( env ) ( t ) ( k1 ) ( k2 ) -> (match ((try_keq env k1 k2)) with
| None -> begin
(let r = (match (t) with
| None -> begin
(Microsoft_FStar_Tc_Env.get_range env)
end
| Some (t) -> begin
t.Microsoft_FStar_Absyn_Syntax.pos
end)
in (match (t) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.incompatible_kinds env k2 k1), r))))
end
| Some (t) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.expected_typ_of_kind env k2 t k1), r))))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun ( env ) ( k1 ) ( k2 ) -> (let _28_3944 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "(%s) subkind of %s and %s\n" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range env)) (Microsoft_FStar_Absyn_Print.kind_to_string k1) (Microsoft_FStar_Absyn_Print.kind_to_string k2))
end
in (let prob = KProb ((new_k_problem env (whnf_k env k1) SUB (whnf_k env k2) None (Microsoft_FStar_Tc_Env.get_range env)))
in (let res = (Support.Microsoft.FStar.Util.must ((with_guard env prob) (solve_and_commit env (singleton env prob) (fun ( _28_3947 ) -> (raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.incompatible_kinds env k1 k2), (Microsoft_FStar_Tc_Env.get_range env)))))))))
in res))))

let try_teq = (fun ( env ) ( t1 ) ( t2 ) -> (let _28_3953 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "try_teq of %s and %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.typ_to_string t2))
end
in (let prob = TProb ((new_t_problem env t1 EQ t2 None (Microsoft_FStar_Tc_Env.get_range env)))
in (let g = ((with_guard env prob) (solve_and_commit env (singleton env prob) (fun ( _28_3956 ) -> None)))
in g))))

let teq = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_teq env t1 t2)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1), (Microsoft_FStar_Tc_Env.get_range env)))))
end
| Some (g) -> begin
(let _28_3965 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "teq of %s and %s succeeded with guard %s\n" (Microsoft_FStar_Absyn_Print.typ_to_string t1) (Microsoft_FStar_Absyn_Print.typ_to_string t2) (guard_to_string env g))
end
in g)
end))

let try_subtype = (fun ( env ) ( t1 ) ( t2 ) -> (let _28_3970 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "try_subtype of %s and %s\n" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2))
end
in (let _28_3974 = (new_t_prob env t1 SUB t2)
in (match (_28_3974) with
| (prob, x) -> begin
(let g = ((with_guard env prob) (solve_and_commit env (singleton env prob) (fun ( _28_3975 ) -> None)))
in (let _28_3978 = if (((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && (Support.Microsoft.FStar.Util.is_some g)) then begin
(Support.Microsoft.FStar.Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2) (guard_to_string env (Support.Microsoft.FStar.Util.must g)))
end
in (abstract_guard x g)))
end))))

let subtype_fail = (fun ( env ) ( t1 ) ( t2 ) -> (raise (Microsoft_FStar_Absyn_Syntax.Error (((Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1), (Microsoft_FStar_Tc_Env.get_range env))))))

let subtype = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun ( env ) ( c1 ) ( c2 ) -> (let _28_3992 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "sub_comp of %s and %s\n" (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1) (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2))
end
in (let rel = if env.Microsoft_FStar_Tc_Env.use_eq then begin
EQ
end else begin
SUB
end
in (let prob = CProb ((new_problem env c1 rel c2 None (Microsoft_FStar_Tc_Env.get_range env) "sub_comp"))
in ((with_guard env prob) (solve_and_commit env (singleton env prob) (fun ( _28_3996 ) -> None)))))))

let solve_deferred_constraints = (fun ( env ) ( g ) -> (let fail = (fun ( _28_4003 ) -> (match (_28_4003) with
| (d, s) -> begin
(let msg = (explain env d s)
in (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _28_4008 = if (((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && ((Support.List.length g.deferred.carry) <> 0)) then begin
((Support.Microsoft.FStar.Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") ((Support.String.concat "\n") ((Support.List.map (fun ( _28_4007 ) -> (match (_28_4007) with
| (msg, x) -> begin
(Support.Microsoft.FStar.Util.format4 "(At %s) %s\n%s\nguard is %s\n" (Support.Microsoft.FStar.Range.string_of_range (p_loc x)) msg (prob_to_string env x) (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env ((Support.Prims.fst) (p_guard x))))
end))) g.deferred.carry)))
end
in (let gopt = (solve_and_commit env (wl_of_guard env g.deferred) fail)
in (match (gopt) with
| Some ({carry = _; slack = slack}) -> begin
(let _28_4016 = (fix_slack_vars slack)
in (let _28_4018 = g
in {guard_f = _28_4018.guard_f; deferred = no_deferred; implicits = _28_4018.implicits}))
end
| _ -> begin
(failwith "impossible")
end)))))

let try_discharge_guard = (fun ( env ) ( g ) -> (let g = (solve_deferred_constraints env g)
in if (not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str))) then begin
()
end else begin
(match (g.guard_f) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(let vc = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(let _28_4032 = if ((Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) then begin
(Microsoft_FStar_Tc_Errors.diag (Microsoft_FStar_Tc_Env.get_range env) (Support.Microsoft.FStar.Util.format1 "Checking VC=\n%s\n" (Microsoft_FStar_Absyn_Print.formula_to_string vc)))
end
in (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env vc))
end))
end)
end))




