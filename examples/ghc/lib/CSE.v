(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Import String.StringSyntax.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require CoreFVs.
Require CoreSubst.
Require CoreUtils.
Require Data.Foldable.
Require Data.Functor.Identity.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Core.Map.Expr.
Require GHC.Err.
Require GHC.Types.Tickish.
Require Id.
Require NestedRecursionHelpers.
Require Panic.
Require Util.

(* Converted type declarations: *)

Inductive CSEnv : Type :=
  | CS (cs_subst : Core.Subst) (cs_map : GHC.Core.Map.Expr.CoreMap Core.OutExpr)
  (cs_rec_map : GHC.Core.Map.Expr.CoreMap Core.OutExpr)
   : CSEnv.

#[global] Definition cs_map (arg_0__ : CSEnv) :=
  let 'CS _ cs_map _ := arg_0__ in
  cs_map.

#[global] Definition cs_rec_map (arg_0__ : CSEnv) :=
  let 'CS _ _ cs_rec_map := arg_0__ in
  cs_rec_map.

#[global] Definition cs_subst (arg_0__ : CSEnv) :=
  let 'CS cs_subst _ _ := arg_0__ in
  cs_subst.

(* Midamble *)

Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
#[global] Instance Default__CSEnv : HsToRocq.Err.Default CSEnv := {| HsToRocq.Err.default := CS Core.emptySubst GHC.Core.Map.Expr.emptyCoreMap GHC.Core.Map.Expr.emptyCoreMap |}.

(* Converted value declarations: *)

#[global] Definition addBinder : CSEnv -> Core.Var -> (CSEnv * Core.Var)%type :=
  fun cse v =>
    let 'pair sub' v' := CoreSubst.substBndr (cs_subst cse) v in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) v'.

#[global] Definition addBinders
   : CSEnv -> list Core.Var -> (CSEnv * list Core.Var)%type :=
  fun cse vs =>
    let 'pair sub' vs' := CoreSubst.substBndrs (cs_subst cse) vs in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) vs'.

#[global] Definition addRecBinders {f} `{Data.Traversable.Traversable f}
   : CSEnv -> f Core.Id -> (CSEnv * f Core.Id)%type :=
  fun cse vs =>
    let 'pair sub' vs' := CoreSubst.substRecBndrs (cs_subst cse) vs in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) vs'.

#[global] Definition combineAlts : list Core.OutAlt -> list Core.OutAlt :=
  fun alts =>
    let identical_alt :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | rhs1, Core.Mk_Alt _ _ rhs => GHC.Core.Map.Expr.eqCoreExpr rhs1 rhs
        end in
    let find_bndr_free_alt
     : list Core.CoreAlt -> (option Core.CoreAlt * list Core.CoreAlt)%type :=
      fix find_bndr_free_alt (arg_4__ : list Core.CoreAlt) : (option Core.CoreAlt *
                                                              list Core.CoreAlt)%type
        := match arg_4__ with
           | nil => pair None nil
           | cons (Core.Mk_Alt _ bndrs _ as alt) alts =>
               if Data.Foldable.null bndrs : bool then pair (Some alt) alts else
               let 'pair mb_bf alts := find_bndr_free_alt alts in
               pair mb_bf (cons alt alts)
           end in
    match find_bndr_free_alt alts with
    | pair (Some alt1) rest_alts =>
        let 'Core.Mk_Alt _ bndrs1 rhs1 := alt1 in
        let filtered_alts := Util.filterOut (identical_alt rhs1) rest_alts in
        if negb (Util.equalLength rest_alts filtered_alts) : bool
        then Panic.assertPpr (Data.Foldable.null bndrs1) (Panic.someSDoc) (cons
                                                                           (Core.Mk_Alt Core.DEFAULT nil rhs1)
                                                                           filtered_alts) else
        alts
    | _ => alts
    end.

#[global] Definition csEnvSubst : CSEnv -> Core.Subst :=
  cs_subst.

#[global] Definition delayInlining
   : BasicTypes.TopLevelFlag -> Core.Id -> Core.Id :=
  fun top_lvl bndr =>
    if andb (BasicTypes.isTopLevel top_lvl) (andb (BasicTypes.isAlwaysActive
                                                   (Id.idInlineActivation bndr)) (Id.idHasRules bndr)) : bool
    then Id.setInlineActivation bndr BasicTypes.activateAfterInitial else
    bndr.

#[global] Definition extendCSEnv
   : CSEnv -> Core.OutExpr -> Core.OutExpr -> CSEnv :=
  fun cse expr triv_expr =>
    let sexpr := expr in
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS cs_subst_0__ (GHC.Core.Map.Expr.extendCoreMap (cs_map cse) sexpr triv_expr)
       cs_rec_map_2__.

#[global] Definition extendCSSubst
   : CSEnv -> Core.Id -> Core.CoreExpr -> CSEnv :=
  fun cse x rhs =>
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS (CoreSubst.extendSubst (cs_subst cse) x rhs) cs_map_1__ cs_rec_map_2__.

#[global] Definition noCSE : Core.InId -> bool :=
  fun id =>
    let no_cse := true in
    let yes_cse := false in
    let user_activation_control :=
      andb (negb (BasicTypes.isAlwaysActive (Id.idInlineActivation id))) (negb
            (BasicTypes.noUserInlineSpec (BasicTypes.inlinePragmaSpec (Id.idInlinePragma
                                                                       id)))) in
    let unf := Id.idUnfolding id in
    if Id.isJoinId id : bool then no_cse else
    if Core.isStableUserUnfolding unf : bool then no_cse else
    if user_activation_control : bool then no_cse else
    yes_cse.

#[global] Definition extendCSEnvWithBinding
   : CSEnv ->
     Core.InVar -> Core.OutId -> Core.OutExpr -> bool -> (CSEnv * Core.OutId)%type :=
  fun env in_id out_id rhs' cse_done =>
    let use_subst := match rhs' with | Core.Mk_Var _ => true | _ => false end in
    let zapped_id := Id.zapIdUsageInfo out_id in
    let id_expr' := Core.varToCoreExpr out_id in
    if negb (Core.isId out_id) : bool
    then pair (extendCSSubst env in_id rhs') out_id else
    if noCSE out_id : bool then pair env out_id else
    if use_subst : bool then pair (extendCSSubst env in_id rhs') out_id else
    if cse_done : bool then pair env out_id else
    pair (extendCSEnv env rhs' id_expr') zapped_id.

#[global] Definition extendCSRecEnv
   : CSEnv -> Core.OutId -> Core.OutExpr -> Core.OutExpr -> CSEnv :=
  fun cse bndr expr triv_expr =>
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS cs_subst_0__ cs_map_1__ (GHC.Core.Map.Expr.extendCoreMap (cs_rec_map cse)
        (Core.Lam bndr expr) triv_expr).

#[global] Definition lookupCSEnv
   : CSEnv -> Core.OutExpr -> option Core.OutExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS _ csmap _, expr => GHC.Core.Map.Expr.lookupCoreMap csmap expr
    end.

#[global] Definition lookupCSRecEnv
   : CSEnv -> Core.OutId -> Core.OutExpr -> option Core.OutExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | CS _ _ csmap, bndr, expr =>
        GHC.Core.Map.Expr.lookupCoreMap csmap (Core.Lam bndr expr)
    end.

#[global] Definition lookupSubst : CSEnv -> Core.Id -> Core.OutExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS sub _ _, x => CoreSubst.lookupIdSubst sub x
    end.

#[local] Definition cse_identity_traverse {f} `{GHC.Base.Applicative f} {a b} (g
    : a -> f b) (x : Data.Functor.Identity.Identity a)
   : f (Data.Functor.Identity.Identity b) :=
  GHC.Base.fmap Data.Functor.Identity.Mk_Identity (g
                 (Data.Functor.Identity.runIdentity x)).

#[local] Definition cse_identity_traversable
   : Data.Traversable.Traversable Data.Functor.Identity.Identity :=
  fun _ k =>
    k (Data.Traversable.Traversable__Dict_Build Data.Functor.Identity.Identity
                                                (fun m a b HF HA HM => (@cse_identity_traverse m HF HA a b)) (fun m
                                                 a
                                                 HF
                                                 HA
                                                 HM =>
                                                   (@cse_identity_traverse m HF HA (m a) a (fun x => x))) (fun f
                                                 a
                                                 HF
                                                 HA =>
                                                   (@cse_identity_traverse f HF HA (f a) a (fun x => x))) (fun f
                                                 a
                                                 b
                                                 HF
                                                 HA =>
                                                   (@cse_identity_traverse f HF HA a b))).

#[global] Definition cseBind
   : BasicTypes.TopLevelFlag ->
     CSEnv -> Core.CoreBind -> (CSEnv * Core.CoreBind)%type :=
  fix cseExpr (arg_0__ : CSEnv) (arg_1__ : Core.InExpr) : Core.OutExpr
    := let try_for_cse (env : CSEnv) (expr : Core.InExpr)
        : (bool * Core.OutExpr)%type :=
         let expr' := cseExpr env expr in
         let expr'' := expr' in
         let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
         match lookupCSEnv env expr'' with
         | Some e => pair true e
         | _ => pair false expr'
         end in
       let tryForCSE (env : CSEnv) (expr : Core.InExpr) : Core.OutExpr :=
         Data.Tuple.snd (try_for_cse env expr) in
       let cseCase (env : CSEnv)
       (scrut : Core.InExpr)
       (bndr : Core.InId)
       (ty : Core.InType)
       (alts : list Core.InAlt)
        : Core.OutExpr :=
         let bndr1 := Id.zapIdOccInfo bndr in
         let 'pair env1 bndr2 := addBinder env bndr1 in
         let 'pair cse_done scrut1 := try_for_cse env scrut in
         let 'pair alt_env bndr3 := extendCSEnvWithBinding env1 bndr bndr2 scrut1
                                      cse_done in
         let con_target : Core.OutExpr := lookupSubst alt_env bndr in
         let arg_tys : list Core.OutType := Core.tyConAppArgs (Id.idType bndr3) in
         let cse_alt :=
           fun arg_6__ =>
             match arg_6__ with
             | Core.Mk_Alt (Core.DataAlt con) args rhs =>
                 let 'pair env' args' := addBinders alt_env args in
                 let con_expr := CoreUtils.mkAltExpr (Core.DataAlt con) args' arg_tys in
                 let new_env := extendCSEnv env' con_expr con_target in
                 Core.Mk_Alt (Core.DataAlt con) args' (tryForCSE new_env rhs)
             | Core.Mk_Alt con args rhs =>
                 let 'pair env' args' := addBinders alt_env args in
                 Core.Mk_Alt con args' (tryForCSE env' rhs)
             end in
         let ty' := CoreSubst.substTyUnchecked (csEnvSubst env) ty in
         Core.Case scrut1 bndr3 ty' (combineAlts (GHC.Base.map cse_alt alts)) in
       match arg_0__, arg_1__ with
       | env, Core.Mk_Type t =>
           Core.Mk_Type (CoreSubst.substTyUnchecked (csEnvSubst env) t)
       | env, Core.Mk_Coercion c =>
           Core.Mk_Coercion (CoreSubst.substCo (csEnvSubst env) c)
       | _, Core.Lit lit => Core.Lit lit
       | env, Core.Mk_Var v => lookupSubst env v
       | env, Core.App f a => Core.App (cseExpr env f) (tryForCSE env a)
       | env, Core.Cast e co =>
           Core.Cast (tryForCSE env e) (CoreSubst.substCo (csEnvSubst env) co)
       | env, Core.Lam b e =>
           let 'pair env' b' := addBinder env b in
           Core.Lam b' (cseExpr env' e)
       | env, Core.Let bind e =>
           let 'pair env' bind' := cseBind BasicTypes.NotTopLevel env bind in
           Core.Let bind' (cseExpr env' e)
       | env, Core.Case e bndr ty alts => cseCase env e bndr ty alts
       end
  with cseBind (arg_0__ : BasicTypes.TopLevelFlag) (arg_1__ : CSEnv) (arg_2__
                 : Core.CoreBind) : (CSEnv * Core.CoreBind)%type
    := let try_for_cse (env : CSEnv) (expr : Core.InExpr)
        : (bool * Core.OutExpr)%type :=
         let expr' := cseExpr env expr in
         let expr'' := expr' in
         let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
         match lookupCSEnv env expr'' with
         | Some e => pair true e
         | _ => pair false expr'
         end in
       let tryForCSE (env : CSEnv) (expr : Core.InExpr) : Core.OutExpr :=
         Data.Tuple.snd (try_for_cse env expr) in
       let cse_bind (arg_0__ : BasicTypes.TopLevelFlag)
       (arg_1__ arg_2__ : CSEnv)
       (arg_3__ : (Core.InId * Core.InExpr)%type)
       (arg_4__ : Core.OutId)
        : (CSEnv * (Core.OutId * Core.OutExpr)%type)%type :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
         | toplevel, env_rhs, env_body, pair in_id in_rhs, out_id =>
             let 'pair cse_done out_rhs := try_for_cse env_rhs in_rhs in
             let 'pair env_body' out_id' := extendCSEnvWithBinding env_body in_id out_id
                                              out_rhs cse_done in
             let out_id'' :=
               if cse_done : bool
               then Id.zapStableUnfolding (delayInlining toplevel out_id') else
               out_id' in
             if andb (BasicTypes.isTopLevel toplevel) (CoreUtils.exprIsTickedString
                      in_rhs) : bool
             then pair env_body' (pair out_id' in_rhs) else
             match Id.idJoinPointHood out_id with
             | Outputable.JoinPoint arity =>
                 NestedRecursionHelpers.collectNBinders_k arity in_rhs (fun params in_body =>
                                                             let 'pair env' params' := addBinders env_rhs params in
                                                             let out_body := tryForCSE env' in_body in
                                                             pair env_body (pair out_id (Core.mkLams params' out_body)))
             | _ => pair env_body' (pair out_id'' out_rhs)
             end
         end in
       match arg_0__, arg_1__, arg_2__ with
       | toplevel, env, Core.NonRec b e =>
           let 'pair env1 b1 := addBinder env b in
           let 'pair env2 (pair b2 e2) := cse_bind toplevel env env1 (pair b e) b1 in
           pair env2 (Core.NonRec b2 e2)
       | toplevel, env, Core.Rec (cons (pair in_id rhs) nil) =>
           let 'pair env1 (Data.Functor.Identity.Mk_Identity out_id) := (@addRecBinders
                                                                           Data.Functor.Identity.Identity
                                                                           Data.Functor.Identity.Functor__Identity
                                                                           Data.Functor.Identity.Foldable__Identity
                                                                           cse_identity_traversable env
                                                                           (Data.Functor.Identity.Mk_Identity in_id)) in
           let rhs' := cseExpr env1 rhs in
           let rhs'' := rhs' in
           let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
           let id_expr' := Core.varToCoreExpr out_id in
           let zapped_id := Id.zapIdUsageInfo out_id in
           if noCSE in_id : bool
           then pair env1 (Core.Rec (cons (pair out_id rhs') nil)) else
           match lookupCSRecEnv env out_id rhs'' with
           | Some previous =>
               let out_id' := delayInlining toplevel out_id in
               let previous' := previous in
               pair (extendCSSubst env1 in_id previous') (Core.NonRec out_id' previous')
           | _ =>
               pair (extendCSRecEnv env1 out_id rhs'' id_expr') (Core.Rec (cons (pair zapped_id
                                                                                      rhs') nil))
           end
       | _, _, _ =>
           match arg_0__, arg_1__, arg_2__ with
           | toplevel, env, Core.Rec pairs =>
               let do_one :=
                 fun arg_3__ arg_4__ =>
                   match arg_3__, arg_4__ with
                   | env, pair pr b1 => cse_bind toplevel env env pr b1
                   end in
               let 'pair env1 bndrs1 := addRecBinders env (GHC.Base.map Data.Tuple.fst
                                                           pairs) in
               let 'pair env2 pairs' := NestedRecursionHelpers.zipMapAccumL do_one env1 pairs
                                                                            bndrs1 in
               pair env2 (Core.Rec pairs')
           | _, _, _ => GHC.Err.patternFailure
           end
       end for cseBind.

#[global] Definition emptyCSEnv : CSEnv :=
  CS Core.emptySubst GHC.Core.Map.Expr.emptyCoreMap
     GHC.Core.Map.Expr.emptyCoreMap.

#[global] Definition cseProgram : Core.CoreProgram -> Core.CoreProgram :=
  fun binds =>
    Data.Tuple.snd (Data.Traversable.mapAccumL (cseBind BasicTypes.TopLevel)
                    emptyCSEnv binds).

#[global] Definition cseExpr : CSEnv -> Core.InExpr -> Core.OutExpr :=
  fix cseExpr (arg_0__ : CSEnv) (arg_1__ : Core.InExpr) : Core.OutExpr
    := let try_for_cse (env : CSEnv) (expr : Core.InExpr)
        : (bool * Core.OutExpr)%type :=
         let expr' := cseExpr env expr in
         let expr'' := expr' in
         let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
         match lookupCSEnv env expr'' with
         | Some e => pair true e
         | _ => pair false expr'
         end in
       let tryForCSE (env : CSEnv) (expr : Core.InExpr) : Core.OutExpr :=
         Data.Tuple.snd (try_for_cse env expr) in
       let cseCase (env : CSEnv)
       (scrut : Core.InExpr)
       (bndr : Core.InId)
       (ty : Core.InType)
       (alts : list Core.InAlt)
        : Core.OutExpr :=
         let bndr1 := Id.zapIdOccInfo bndr in
         let 'pair env1 bndr2 := addBinder env bndr1 in
         let 'pair cse_done scrut1 := try_for_cse env scrut in
         let 'pair alt_env bndr3 := extendCSEnvWithBinding env1 bndr bndr2 scrut1
                                      cse_done in
         let con_target : Core.OutExpr := lookupSubst alt_env bndr in
         let arg_tys : list Core.OutType := Core.tyConAppArgs (Id.idType bndr3) in
         let cse_alt :=
           fun arg_6__ =>
             match arg_6__ with
             | Core.Mk_Alt (Core.DataAlt con) args rhs =>
                 let 'pair env' args' := addBinders alt_env args in
                 let con_expr := CoreUtils.mkAltExpr (Core.DataAlt con) args' arg_tys in
                 let new_env := extendCSEnv env' con_expr con_target in
                 Core.Mk_Alt (Core.DataAlt con) args' (tryForCSE new_env rhs)
             | Core.Mk_Alt con args rhs =>
                 let 'pair env' args' := addBinders alt_env args in
                 Core.Mk_Alt con args' (tryForCSE env' rhs)
             end in
         let ty' := CoreSubst.substTyUnchecked (csEnvSubst env) ty in
         Core.Case scrut1 bndr3 ty' (combineAlts (GHC.Base.map cse_alt alts)) in
       match arg_0__, arg_1__ with
       | env, Core.Mk_Type t =>
           Core.Mk_Type (CoreSubst.substTyUnchecked (csEnvSubst env) t)
       | env, Core.Mk_Coercion c =>
           Core.Mk_Coercion (CoreSubst.substCo (csEnvSubst env) c)
       | _, Core.Lit lit => Core.Lit lit
       | env, Core.Mk_Var v => lookupSubst env v
       | env, Core.App f a => Core.App (cseExpr env f) (tryForCSE env a)
       | env, Core.Cast e co =>
           Core.Cast (tryForCSE env e) (CoreSubst.substCo (csEnvSubst env) co)
       | env, Core.Lam b e =>
           let 'pair env' b' := addBinder env b in
           Core.Lam b' (cseExpr env' e)
       | env, Core.Let bind e =>
           let 'pair env' bind' := cseBind BasicTypes.NotTopLevel env bind in
           Core.Let bind' (cseExpr env' e)
       | env, Core.Case e bndr ty alts => cseCase env e bndr ty alts
       end
  with cseBind (arg_0__ : BasicTypes.TopLevelFlag) (arg_1__ : CSEnv) (arg_2__
                 : Core.CoreBind) : (CSEnv * Core.CoreBind)%type
    := let try_for_cse (env : CSEnv) (expr : Core.InExpr)
        : (bool * Core.OutExpr)%type :=
         let expr' := cseExpr env expr in
         let expr'' := expr' in
         let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
         match lookupCSEnv env expr'' with
         | Some e => pair true e
         | _ => pair false expr'
         end in
       let tryForCSE (env : CSEnv) (expr : Core.InExpr) : Core.OutExpr :=
         Data.Tuple.snd (try_for_cse env expr) in
       let cse_bind (arg_0__ : BasicTypes.TopLevelFlag)
       (arg_1__ arg_2__ : CSEnv)
       (arg_3__ : (Core.InId * Core.InExpr)%type)
       (arg_4__ : Core.OutId)
        : (CSEnv * (Core.OutId * Core.OutExpr)%type)%type :=
         match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
         | toplevel, env_rhs, env_body, pair in_id in_rhs, out_id =>
             let 'pair cse_done out_rhs := try_for_cse env_rhs in_rhs in
             let 'pair env_body' out_id' := extendCSEnvWithBinding env_body in_id out_id
                                              out_rhs cse_done in
             let out_id'' :=
               if cse_done : bool
               then Id.zapStableUnfolding (delayInlining toplevel out_id') else
               out_id' in
             if andb (BasicTypes.isTopLevel toplevel) (CoreUtils.exprIsTickedString
                      in_rhs) : bool
             then pair env_body' (pair out_id' in_rhs) else
             match Id.idJoinPointHood out_id with
             | Outputable.JoinPoint arity =>
                 NestedRecursionHelpers.collectNBinders_k arity in_rhs (fun params in_body =>
                                                             let 'pair env' params' := addBinders env_rhs params in
                                                             let out_body := tryForCSE env' in_body in
                                                             pair env_body (pair out_id (Core.mkLams params' out_body)))
             | _ => pair env_body' (pair out_id'' out_rhs)
             end
         end in
       match arg_0__, arg_1__, arg_2__ with
       | toplevel, env, Core.NonRec b e =>
           let 'pair env1 b1 := addBinder env b in
           let 'pair env2 (pair b2 e2) := cse_bind toplevel env env1 (pair b e) b1 in
           pair env2 (Core.NonRec b2 e2)
       | toplevel, env, Core.Rec (cons (pair in_id rhs) nil) =>
           let 'pair env1 (Data.Functor.Identity.Mk_Identity out_id) := (@addRecBinders
                                                                           Data.Functor.Identity.Identity
                                                                           Data.Functor.Identity.Functor__Identity
                                                                           Data.Functor.Identity.Foldable__Identity
                                                                           cse_identity_traversable env
                                                                           (Data.Functor.Identity.Mk_Identity in_id)) in
           let rhs' := cseExpr env1 rhs in
           let rhs'' := rhs' in
           let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
           let id_expr' := Core.varToCoreExpr out_id in
           let zapped_id := Id.zapIdUsageInfo out_id in
           if noCSE in_id : bool
           then pair env1 (Core.Rec (cons (pair out_id rhs') nil)) else
           match lookupCSRecEnv env out_id rhs'' with
           | Some previous =>
               let out_id' := delayInlining toplevel out_id in
               let previous' := previous in
               pair (extendCSSubst env1 in_id previous') (Core.NonRec out_id' previous')
           | _ =>
               pair (extendCSRecEnv env1 out_id rhs'' id_expr') (Core.Rec (cons (pair zapped_id
                                                                                      rhs') nil))
           end
       | _, _, _ =>
           match arg_0__, arg_1__, arg_2__ with
           | toplevel, env, Core.Rec pairs =>
               let do_one :=
                 fun arg_3__ arg_4__ =>
                   match arg_3__, arg_4__ with
                   | env, pair pr b1 => cse_bind toplevel env env pr b1
                   end in
               let 'pair env1 bndrs1 := addRecBinders env (GHC.Base.map Data.Tuple.fst
                                                           pairs) in
               let 'pair env2 pairs' := NestedRecursionHelpers.zipMapAccumL do_one env1 pairs
                                                                            bndrs1 in
               pair env2 (Core.Rec pairs')
           | _, _, _ => GHC.Err.patternFailure
           end
       end for cseExpr.

#[global] Definition try_for_cse
   : CSEnv -> Core.InExpr -> (bool * Core.OutExpr)%type :=
  fun env expr =>
    let expr' := cseExpr env expr in
    let expr'' := expr' in
    let ticks := (@nil GHC.Types.Tickish.CoreTickish) in
    match lookupCSEnv env expr'' with
    | Some e => pair true e
    | _ => pair false expr'
    end.

#[global] Definition tryForCSE : CSEnv -> Core.InExpr -> Core.OutExpr :=
  fun env expr => Data.Tuple.snd (try_for_cse env expr).

#[global] Definition cse_bind
   : BasicTypes.TopLevelFlag ->
     CSEnv ->
     CSEnv ->
     (Core.InId * Core.InExpr)%type ->
     Core.OutId -> (CSEnv * (Core.OutId * Core.OutExpr)%type)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | toplevel, env_rhs, env_body, pair in_id in_rhs, out_id =>
        let 'pair cse_done out_rhs := try_for_cse env_rhs in_rhs in
        let 'pair env_body' out_id' := extendCSEnvWithBinding env_body in_id out_id
                                         out_rhs cse_done in
        let out_id'' :=
          if cse_done : bool
          then Id.zapStableUnfolding (delayInlining toplevel out_id') else
          out_id' in
        if andb (BasicTypes.isTopLevel toplevel) (CoreUtils.exprIsTickedString
                 in_rhs) : bool
        then pair env_body' (pair out_id' in_rhs) else
        match Id.idJoinPointHood out_id with
        | Outputable.JoinPoint arity =>
            NestedRecursionHelpers.collectNBinders_k arity in_rhs (fun params in_body =>
                                                        let 'pair env' params' := addBinders env_rhs params in
                                                        let out_body := tryForCSE env' in_body in
                                                        pair env_body (pair out_id (Core.mkLams params' out_body)))
        | _ => pair env_body' (pair out_id'' out_rhs)
        end
    end.

#[global] Definition cseOneExpr : Core.InExpr -> Core.OutExpr :=
  fun e =>
    let env :=
      let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := emptyCSEnv in
      CS (Core.mkEmptySubst (Core.mkInScopeSet (CoreFVs.exprFreeVars e))) cs_map_1__
         cs_rec_map_2__ in
    cseExpr env e.

#[global] Definition cseCase
   : CSEnv ->
     Core.InExpr -> Core.InId -> Core.InType -> list Core.InAlt -> Core.OutExpr :=
  fun env scrut bndr ty alts =>
    let bndr1 := Id.zapIdOccInfo bndr in
    let 'pair env1 bndr2 := addBinder env bndr1 in
    let 'pair cse_done scrut1 := try_for_cse env scrut in
    let 'pair alt_env bndr3 := extendCSEnvWithBinding env1 bndr bndr2 scrut1
                                 cse_done in
    let con_target : Core.OutExpr := lookupSubst alt_env bndr in
    let arg_tys : list Core.OutType := Core.tyConAppArgs (Id.idType bndr3) in
    let cse_alt :=
      fun arg_6__ =>
        match arg_6__ with
        | Core.Mk_Alt (Core.DataAlt con) args rhs =>
            let 'pair env' args' := addBinders alt_env args in
            let con_expr := CoreUtils.mkAltExpr (Core.DataAlt con) args' arg_tys in
            let new_env := extendCSEnv env' con_expr con_target in
            Core.Mk_Alt (Core.DataAlt con) args' (tryForCSE new_env rhs)
        | Core.Mk_Alt con args rhs =>
            let 'pair env' args' := addBinders alt_env args in
            Core.Mk_Alt con args' (tryForCSE env' rhs)
        end in
    let ty' := CoreSubst.substTyUnchecked (csEnvSubst env) ty in
    Core.Case scrut1 bndr3 ty' (combineAlts (GHC.Base.map cse_alt alts)).

Lemma cse_identity_mapAccumL {s a b} (step : s -> a -> prod s b) st x :
  (@Data.Traversable.mapAccumL Data.Functor.Identity.Identity s a b
   Data.Functor.Identity.Functor__Identity Data.Functor.Identity.Foldable__Identity
   cse_identity_traversable step st (Data.Functor.Identity.Mk_Identity x)) =
  (let 'pair st' y := step st x in
   pair st' (Data.Functor.Identity.Mk_Identity y)).
Proof.
  cbv. destruct (step st x). reflexivity.
Qed.

(* External variables:
     None Some andb bool cons false list negb nil op_ze__ op_zt__ option pair prod
     true BasicTypes.NotTopLevel BasicTypes.TopLevel BasicTypes.TopLevelFlag
     BasicTypes.activateAfterInitial BasicTypes.inlinePragmaSpec
     BasicTypes.isAlwaysActive BasicTypes.isTopLevel BasicTypes.noUserInlineSpec
     Core.App Core.Case Core.Cast Core.CoreAlt Core.CoreBind Core.CoreExpr
     Core.CoreProgram Core.DEFAULT Core.DataAlt Core.Id Core.InAlt Core.InExpr
     Core.InId Core.InType Core.InVar Core.Lam Core.Let Core.Lit Core.Mk_Alt
     Core.Mk_Coercion Core.Mk_Type Core.Mk_Var Core.NonRec Core.OutAlt Core.OutExpr
     Core.OutId Core.OutType Core.Rec Core.Subst Core.Var Core.emptySubst Core.isId
     Core.isStableUserUnfolding Core.mkEmptySubst Core.mkInScopeSet Core.mkLams
     Core.tyConAppArgs Core.varToCoreExpr CoreFVs.exprFreeVars CoreSubst.extendSubst
     CoreSubst.lookupIdSubst CoreSubst.substBndr CoreSubst.substBndrs
     CoreSubst.substCo CoreSubst.substRecBndrs CoreSubst.substTyUnchecked
     CoreUtils.exprIsTickedString CoreUtils.mkAltExpr Data.Foldable.null
     Data.Functor.Identity.Foldable__Identity Data.Functor.Identity.Functor__Identity
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Identity.runIdentity Data.Traversable.Traversable
     Data.Traversable.Traversable__Dict_Build Data.Traversable.mapAccumL
     Data.Tuple.fst Data.Tuple.snd GHC.Base.Applicative GHC.Base.fmap GHC.Base.map
     GHC.Core.Map.Expr.CoreMap GHC.Core.Map.Expr.emptyCoreMap
     GHC.Core.Map.Expr.eqCoreExpr GHC.Core.Map.Expr.extendCoreMap
     GHC.Core.Map.Expr.lookupCoreMap GHC.Err.patternFailure
     GHC.Types.Tickish.CoreTickish Id.idHasRules Id.idInlineActivation
     Id.idInlinePragma Id.idJoinPointHood Id.idType Id.idUnfolding Id.isJoinId
     Id.setInlineActivation Id.zapIdOccInfo Id.zapIdUsageInfo Id.zapStableUnfolding
     NestedRecursionHelpers.collectNBinders_k NestedRecursionHelpers.zipMapAccumL
     Outputable.JoinPoint Panic.assertPpr Panic.someSDoc Util.equalLength
     Util.filterOut
*)
