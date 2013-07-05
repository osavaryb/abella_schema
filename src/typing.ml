(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Term
open Metaterm
open Extensions


(** Untyped terms *)

type pos = Lexing.position * Lexing.position

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm


let get_pos t =
  match t with
    | UCon(p, _, _) -> p
    | ULam(p, _, _, _) -> p
    | UApp(p, _, _) -> p

let change_pos p t =
  match t with
    | UCon(_, id, ty) -> UCon(p, id, ty)
    | ULam(_, id, ty, body) -> ULam(p, id, ty, body)
    | UApp(_, t1, t2) -> UApp(p, t1, t2)


let predefined id pos =
  UCon(pos, id, Term.fresh_tyvar ())

let binop id t1 t2 =
  let pos = (fst (get_pos t1), snd (get_pos t2)) in
  UApp(pos, UApp(pos, predefined id pos, t1), t2)


let uterm_head_name t =
  let rec aux = function
    | UCon(_, id, _) -> id
    | UApp(_, h, _) -> aux h
    | ULam _ -> assert false
  in
    aux t

(** Untyped metaterm *)

type umetaterm =
  | UTrue
  | UFalse
  | UEq of uterm * uterm
  | UAsyncObj of uterm * uterm * restriction
  | USyncObj of uterm * uterm * uterm * restriction
  | UArrow of umetaterm * umetaterm
  | UBinding of binder * (id * ty) list * umetaterm
  | UOr of umetaterm * umetaterm
  | UAnd of umetaterm * umetaterm
  | UPred of uterm * restriction


(** Type substitutions *)

type tysub = (string * ty) list

let rec apply_bind_ty v ty = function
  | Ty(tys, bty) ->
      tyarrow
        (List.map (apply_bind_ty v ty) tys)
        (if v = bty then ty else Ty([], bty))

let apply_sub_ty s ty =
  List.fold_left (fun ty (v,vty) -> apply_bind_ty v vty ty) ty s

let apply_sub_tyctx s tyctx =
  List.map (fun (id, ty) -> (id, apply_sub_ty s ty)) tyctx

let ids_to_fresh_tyctx ids =
  List.map (fun id -> (id, fresh_tyvar ())) ids

let tyctx_to_ctx tyctx =
  List.map (fun (id, ty) -> (id, const id ty)) tyctx

let tyctx_to_nominal_ctx tyctx =
  List.map (fun (id, ty) -> (id, nominal_var id ty)) tyctx


(** Tables / Signatures *)

type ktable = string list
type pty = Poly of string list * ty
type ctable = (string * pty) list
type sign = ktable * ctable

(** Kinds *)

let add_types (ktable, ctable) ids =
  List.iter
    (fun id -> if is_capital_name id then
       failwith ("Types may not begin with a capital letter: " ^ id))
    ids ;
  (ids @ ktable, ctable)

let lookup_type (ktable, _) id =
  List.mem id ktable

(** Constants *)

let kind_check sign (Poly(ids, ty)) =
  let rec aux = function
    | Ty(tys, bty) ->
        if List.mem bty ids || lookup_type sign bty then
          List.iter aux tys
        else
          failwith ("Unknown type: " ^ bty)
  in
    aux ty

let check_const (ktable, ctable) (id, pty) =
  begin try
    let pty' = List.assoc id ctable in
      if pty <> pty' then
        failwith ("Constant " ^ id ^ " has inconsistent type declarations")
  with
    | Not_found -> ()
  end ;

  if is_capital_name id then
    failwith ("Constants may not begin with a capital letter: " ^ id) ;

  kind_check (ktable, ctable) pty

let add_poly_consts (ktable, ctable) idptys =
  List.iter (check_const (ktable, ctable)) idptys ;
  (ktable, idptys @ ctable)

let add_consts sign idtys =
  let idptys = List.map (fun (id, ty) -> (id, Poly([], ty))) idtys in
    add_poly_consts sign idptys

let freshen_ty (Poly(ids, ty)) =
  let sub = ids_to_fresh_tyctx ids in
    apply_sub_ty sub ty

let lookup_const (_, ctable) id =
  try
    freshen_ty (List.assoc id ctable)
  with
    | Not_found -> failwith ("Unknown constant: " ^ id)

(* SCHEMA *)
let rec split_n_from_list n l =
begin match (n,l) with
| (n, h::tl) ->  
    let (f,t) = split_n_from_list (n-1) tl in
     (h::f, t)
| (0, []) -> ([],[])
|  _ -> failwith "in split_n_from_list, coudln't remove n element" 
end


let rec type_vars_in tm ty sign lbound = 
begin match observe tm with 
| Var v -> let vn = Term.(v.name) in
         begin try 
	   let ety = lookup_const !sign vn in
	   if (ty_to_string ty) <> (ty_to_string ety) then
	     failwith ("in type_vars_in, constant "^(term_to_string tm)^" has type "^(ty_to_string ety)^" instead of expected type "^(ty_to_string ty)^". \n")
	   else
	     []
         with _ -> 
	   if List.mem_assoc vn lbound then [] else [(Term.(v.name), ty) ]
	 end
| App (th, tt) ->
    begin try 
      let Ty(tys,bty)  = lookup_const !sign (term_to_string th) in
      let n = List.length tt in
      if n <= (List.length tys) then
	let (tys',_) = split_n_from_list n tys in
	let idtysl = List.map (fun (tm,ty) -> type_vars_in tm ty sign lbound) (List.combine tt tys') in
	List.flatten idtysl
      else
      failwith ("in type_vars_in, term "^(term_to_string tm)^" has a function applied to too many arguments")
    with _ -> failwith ("in type_vars_in, can't type "^(term_to_string tm)^"%s. \n") end
| Lam (idtys, t ) -> 
       let Ty(tys,bty) = ty in
       let n = List.length idtys  in
       if n >= (List.length tys) then
	 let (_,tys') = split_n_from_list n tys in
	 type_vars_in t (Ty(tys', bty)) sign (List.append idtys lbound)
       else
	 failwith ("in type_vars_in, "^(term_to_string tm)^" doesn't fit type "^(ty_to_string ty)^". \n" )
| DB i  -> []
|  _ -> failwith ("in type_vars_in, unhandled "^(term_to_string tm)^". \n")
end

(*
let rec get_ty_from_tml id tml tyl sign = 
begin match (tml,tyl) with
| (App(th,tt)::tl,(tyh::tytl)) ->
    begin try 
      let id3 = (term_to_string th) in
      let pty = (lookup_const !sign id3) in
      let Ty(tys,bty) =  pty in
      get_ty_from_tml id (List.map observe tt) tys sign
    with
    | Not_found -> get_ty_from_tml id tl tytl sign
    end 
| (Var v)::tl, tyh::tytl ->
    if (v.name = id) then tyh else get_ty_from_tml id tl tytl sign 
|  _ -> raise Not_found
end
*)



(* end SCHEMA *)

(** Pervasive signature *)

let pervasive_sign =
  (["o"; "olist"; "prop"],
   [("pi",     Poly(["A"], tyarrow [tyarrow [tybase "A"] oty] oty)) ;
    ("=>",     Poly([],    tyarrow [oty; oty] oty)) ;
    ("member", Poly([],    tyarrow [oty; olistty] propty)) ;
    ("::",     Poly([],    tyarrow [oty; olistty] olistty)) ;
    ("nil",    Poly([],    olistty))])

let sign_to_tys sign =
  List.filter_map
    (function (_, Poly([], ty)) -> Some ty | _ -> None)
    (snd sign)

let pervasive_sr =
  List.fold_left Subordination.update Subordination.empty
    (sign_to_tys pervasive_sign)

(** Typing for terms *)

type expected = ty
type actual = ty
(* A constraint contains the position of the 'actual' type *)
type constraint_type = CFun | CArg
type constraint_info = pos * constraint_type
type constraints = (expected * actual * constraint_info) list
exception TypeInferenceFailure of constraint_info * expected * actual

let infer_type_and_constraints ~sign tyctx t =
  let eqns = ref [] in
  let add_constraint expected actual pos =
    eqns := (expected, actual, pos) :: !eqns
  in

  let rec aux tyctx t =
    match t with
      | UCon(p, id, ty) ->
          let ty' =
            begin try
              List.assoc id tyctx
            with
              | Not_found -> lookup_const sign id
            end
          in
            add_constraint ty ty' (p, CArg) ;
            ty
      | ULam(_, id, ty, t) ->
          tyarrow [ty] (aux ((id, ty) :: tyctx) t)
      | UApp(_, t1, t2) ->
          let ty1 = aux tyctx t1 in
          let ty2 = aux tyctx t2 in
          let (aty, rty) =
            match ty1 with
              | Ty([], _) ->
                  let aty = fresh_tyvar () in
                  let rty = fresh_tyvar () in
                    add_constraint (tyarrow [aty] rty) ty1 (get_pos t1, CFun) ;
                    (aty, rty)
              | Ty(aty::atys, bty) ->
                  (aty, Ty(atys, bty))
          in
            add_constraint aty ty2 (get_pos t2, CArg) ;
            rty
  in

  let ty = aux tyctx t in
    (ty, List.rev !eqns)


let constraints_to_string eqns =
  let aux (ty1, ty2, _) =
    (ty_to_string ty1) ^ " = " ^ (ty_to_string ty2)
  in
    String.concat "\n" (List.map aux eqns)

let occurs v ty =
  let rec aux = function
    | Ty(tys, bty) when bty = v -> true
    | Ty(tys, _) -> List.exists aux tys
  in
    aux ty

let rec contains_tyvar = function
  | Ty(tys, bty) ->
      is_tyvar bty || List.exists contains_tyvar tys

let tid_ensure_fully_inferred (id, ty) =
  if contains_tyvar ty then
    failwith ("Type not fully determined for " ^ id)

let term_ensure_fully_inferred t =
  let rec aux t =
    match observe (hnorm t) with
      | Var v -> tid_ensure_fully_inferred (v.name, v.ty)
      | DB i -> ()
      | App(h, args) -> aux h ; List.iter aux args
      | Lam(tys, body) -> aux body
      | _ -> assert false
  in
    aux t

let metaterm_ensure_fully_inferred t =
  let rec aux t =
    match t with
      | True | False -> ()
      | And(a, b) | Or(a, b) | Arrow(a, b) -> aux a; aux b
      | Binding(_, tids, body) ->
          List.iter tid_ensure_fully_inferred tids ;
          aux body
      | Eq(a, b) ->
          term_ensure_fully_inferred a ;
          term_ensure_fully_inferred b
      | Obj(Async obj, _) ->
          let ctx,term = Async.get obj in
          Context.iter term_ensure_fully_inferred ctx ;
          term_ensure_fully_inferred term
      | Obj(Sync obj, _) ->
          let ctx,focus,term = Sync.get obj in
          Context.iter term_ensure_fully_inferred ctx ;
          term_ensure_fully_inferred focus;
          term_ensure_fully_inferred term;
      | Pred(p, _) ->
          term_ensure_fully_inferred p
  in
    aux t

let apply_bind_constraints v ty eqns =
  List.map (fun (x,y) -> (apply_bind_ty v ty x, apply_bind_ty v ty y)) eqns

let apply_bind_sub v ty sub =
  List.map (fun (x,y) -> (x, apply_bind_ty v ty y)) sub

let unify_constraints eqns =
  let add_sub v vty s =
      (v, vty) :: (apply_bind_sub v vty s)
  in

  (* Unify a single constraint and call fail on failure *)
  let rec aux s (ty1, ty2) fail =
    let ty1 = apply_sub_ty s ty1 in
    let ty2 = apply_sub_ty s ty2 in
      match ty1, ty2 with
        | _, _ when ty1 = ty2 -> s
        | Ty([], bty1), _ when is_tyvar bty1 ->
            if occurs bty1 ty2 then
              fail s
            else
              add_sub bty1 ty2 s
        | _, Ty([], bty2) when is_tyvar bty2 ->
            if occurs bty2 ty1 then
              fail s
            else
              add_sub bty2 ty1 s
        | Ty(ty1::tys1, bty1), Ty(ty2::tys2, bty2) ->
            let s = aux s (ty1, ty2) fail in
              aux s (Ty(tys1, bty1), Ty(tys2, bty2)) fail
        | ty1, ty2 -> fail s
  in

  let unify_single_constraint s (ty1, ty2, p) =
    aux s (ty1, ty2)
      (fun s -> raise (TypeInferenceFailure(p, apply_sub_ty s ty1,
                                            apply_sub_ty s ty2)))
  in

    List.fold_left unify_single_constraint [] eqns

let uterms_extract_if test ts =
  let rec aux t =
    match t with
      | UCon(_, id, _) -> if test id then [id] else []
      | ULam(_, id, _, t) -> List.remove id (aux t)
      | UApp(_, t1, t2) -> (aux t1) @ (aux t2)
  in
    List.unique (List.flatten_map aux ts)

let uterm_nominals_to_tyctx t =
  ids_to_fresh_tyctx (uterms_extract_if is_nominal_name [t])


let get_nth_id n tm =
  begin match observe (hnorm tm) with
  | App ( t , ts ) -> 
      let t = 
      begin match n with
      |	0 -> t
      |	_ -> (List.nth ts (n-1))
      end in
       t
  | _ -> if n = 0 then tm else failwith "Unexpected tm in get_nth_id"
  end

let rec mem_pos s l = begin match l with
| h::t -> if h = s then 1 else 
              (mem_pos s t)+1
| [] -> failwith ("in mem_pos, "^s^" not found in list")
end

let rec string_count n s = begin match n with
|  0 -> []
|  n -> List.append (string_count (n-1) s) [s^(string_of_int n)]
end


let listSplit3 l = 
List.fold_right (fun (a,bl,cl) (ca, cb, cc) -> (a::ca,bl::cb, cl::cc)) l ([],[],[])

(* remove repeated strings from list, keeping only the last occ. *)
let rec rem_rep idl = begin match idl with
|  id::idl' -> 
    if (List.mem id idl') then idl' else id::(rem_rep idl')
|  [] -> []
end

let rec rem_rep_pairs idfool = begin match idfool with
| (id,foo)::idl' -> 
    if (List.mem_assoc id idl') then idl' else ((id,foo)::idl')
|  [] -> []
end


let get_head_id tm =
  term_to_string (get_nth_id 0 tm)
(*  begin match observe (hnorm tm) with
  | App ( t , _ ) -> 
      (begin match observe (hnorm t) with
      |  Var {name = op} -> op
      |   _ -> failwith "..."
      end)
  | _ -> failwith "Not a pred"
  end *)

let uterm_to_term sub t =
  let rec aux t =
    match t with
      | UCon(_, id, ty) -> const id (apply_sub_ty sub ty)
      | ULam(_, id, ty, t) -> abstract id (apply_sub_ty sub ty) (aux t)
      | UApp(_, t1, t2) -> app (aux t1) [aux t2]
  in
    aux t

let rec rename_ids_in_idtys sub idtys = 
begin match idtys with
|  (idh,tyh)::idtys' -> let sidtys' = rename_ids_in_idtys sub idtys' in  if
    (List.mem_assoc idh sub) then (List.assoc idh sub, tyh)::sidtys' else (idh,tyh)::sidtys'
|  [] -> []
end

let rec rename_ids_in_uterm sub ut = 
  match ut with
      | UCon(p, id', ty) -> if (List.mem_assoc id' sub) then UCon(p, (List.assoc id' sub), ty) else ut
      | ULam(p, id', ty, t) -> 
	  let (ids1,ids2) = List.split sub in
	  let bus = (List.combine ids2 ids1) in
	  if (List.mem_assoc id' bus) then 
	    let nid = List.assoc id' bus in
	    ULam(p,nid, ty, (rename_ids_in_uterm ((id',nid)::sub) t))
	  else
	    ULam(p,id', ty, (rename_ids_in_uterm ((id',id')::sub) t))
      | UApp(p, t1, t2) -> UApp(p, (rename_ids_in_uterm sub t1), (rename_ids_in_uterm sub t2))

let uterm_to_string t =
  term_to_string (uterm_to_term [] t)

let term_ensure_subordination sr t =
  let rec aux tyctx t =
    match observe (hnorm t) with
      | Var v -> Subordination.ensure sr v.ty
      | DB i -> ()
      | App(h, ts) -> aux tyctx h ; List.iter (aux tyctx) ts
      | Lam(idtys, b) ->
          Subordination.ensure sr (tc tyctx t) ;
          aux (List.rev_app idtys tyctx) b
      | _ -> assert false
  in
    aux [] t

let iter_ty f ty =
  let rec aux = function
    | Ty(tys, bty) -> f bty; List.iter aux tys
  in
    aux ty

let check_spec_logic_type ty =
  iter_ty
    (fun bty ->
       if bty = "prop" then
         failwith "Cannot mention type prop in the specification logic" ;
       if bty = "olist" then
         failwith "Cannot mention type olist in the specification logic")
    ty

let check_spec_logic_quantification_type ty =
  check_spec_logic_type ty ;
  iter_ty
    (fun bty  ->
        if bty = "o" then
          failwith "Cannot quantify over type o in the specification logic")
    ty

let check_pi_quantification ts =
  ignore
    (map_vars
       (fun v ->
          if v.name = "pi" then
            match v.ty with
              | Ty([Ty([tau], _)], _) ->
                  check_spec_logic_quantification_type tau
              | _ -> assert false)
       ts)

let type_uterm ?expected_ty ~sr ~sign ~ctx t =
  let nominal_tyctx = uterm_nominals_to_tyctx t in
  let tyctx =
    (List.map (fun (id, t) -> (id, tc [] t)) ctx)
      @ nominal_tyctx
  in
  let (ty, eqns) = infer_type_and_constraints ~sign tyctx t in
  let eqns =
    match expected_ty with
    | None -> eqns
    | Some exp_ty -> (exp_ty, ty, (get_pos t, CArg)) :: eqns
  in
  let sub = unify_constraints eqns in
  let ctx = ctx @ (tyctx_to_nominal_ctx (apply_sub_tyctx sub nominal_tyctx)) in
  let result = replace_term_vars ctx (uterm_to_term sub t) in
    term_ensure_fully_inferred result ;
    term_ensure_subordination sr result ;
    result

let rec has_capital_head t =
  match t with
    | UCon(_, v, _) -> is_capital_name v
    | UApp(_, h, _) -> has_capital_head h
    | _ -> false


let replace_underscores head body =
  let names = uterms_extract_if is_capital_name (head::body) in
  let used = ref (List.map (fun x -> (x, ())) names) in
  let rec aux t =
    match t with
      | UCon(p, id, ty) when id = "_" ->
          let id' = fresh_name "X" !used in
            used := (id', ()) :: !used ;
            UCon(p, id', ty)
      | UCon _ -> t
      | ULam(p, id, ty, t) ->
          used := (id, ()) :: !used ;
          ULam(p, id, ty, aux t)
      | UApp(p, t1, t2) ->
          let t1' = aux t1 in
          let t2' = aux t2 in
            UApp(p, t1', t2')
  in
    match List.map aux (head::body) with
      | h::b -> (h, b)
      | [] -> assert false

let type_uclause ~sr ~sign (head, body) =
  if has_capital_head head then
    failwith "Clause has flexible head" ;
  let head, body = replace_underscores head body in
  let cids = uterms_extract_if is_capital_name (head::body) in
  let get_imp_form head body =
    (let impfy imp f = (binop "=>" f imp) in
    List.fold_left impfy head (List.rev body))
  in
  let imp_form = get_imp_form head body in
  let get_pi_form ids body =
    (let pify id pi =
      let pos = get_pos pi in
      let abs = ULam (pos, id, Term.fresh_tyvar (), pi) in
      UApp (pos, predefined "pi" pos, abs)
    in
    List.fold_right pify ids body)
  in
  let pi_form = get_pi_form cids imp_form in
  let result = type_uterm ~sr ~sign ~ctx:[] pi_form in
  let _,cls = replace_pi_with_const result in
  let _ = check_pi_quantification [cls] in
  result

(*
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns =
    List.fold_left (fun acc p ->
                      let (pty, peqns) = infer_type_and_constraints ~sign tyctx p in
                        acc @ peqns @ [(oty, pty, (get_pos p, CArg))])
      [] (head::body)
  in
  let sub = unify_constraints eqns in
  let ctx = tyctx_to_ctx (apply_sub_tyctx sub tyctx) in
  let convert p = replace_term_vars ctx (uterm_to_term sub p) in
  let (rhead, rbody) = (convert head, List.map convert body) in
    List.iter term_ensure_fully_inferred (rhead::rbody) ;
    List.iter (term_ensure_subordination sr) (rhead::rbody) ;
    check_pi_quantification (rhead::rbody) ;
    (rhead, rbody)
*)


(** Typing for metaterms *)

let infer_constraints ~sign ~tyctx t =
  let rec aux tyctx t =
    match t with
      | UTrue | UFalse -> []
      | UEq(a, b) ->
          let (aty, aeqns) = infer_type_and_constraints ~sign tyctx a in
          let (bty, beqns) = infer_type_and_constraints ~sign tyctx b in
            aeqns @ beqns @ [(aty, bty, (get_pos b, CArg))]
      | UAsyncObj(l, g, _) ->
          let (lty, leqns) = infer_type_and_constraints ~sign tyctx l in
          let (gty, geqns) = infer_type_and_constraints ~sign tyctx g in
            leqns @ geqns @ [(olistty, lty, (get_pos l, CArg));
                             (oty, gty, (get_pos g, CArg))]
      | USyncObj(l, f, g, _) ->
          let (lty, leqns) = infer_type_and_constraints ~sign tyctx l in
          let (fty, feqns) = infer_type_and_constraints ~sign tyctx f in
          let (gty, geqns) = infer_type_and_constraints ~sign tyctx g in
            leqns @ feqns @ geqns @
          [(olistty, lty, (get_pos l, CArg));
           (oty, fty, (get_pos f, CArg));
           (oty, gty, (get_pos g, CArg))]
      | UArrow(a, b) | UOr(a, b) | UAnd(a, b) ->
          (aux tyctx a) @ (aux tyctx b)
      | UBinding(_, tids, body) ->
          aux (List.rev_app tids tyctx) body
      | UPred(p, _) ->
          let (pty, peqns) = infer_type_and_constraints ~sign tyctx p in
            peqns @ [(propty, pty, (get_pos p, CArg))]
  in
    aux tyctx t

let umetaterm_extract_if test t =
  let rec aux t =
    match t with
      | UTrue | UFalse -> []
      | UEq(a, b) ->
          uterms_extract_if test [a; b]
      | UPred(p, _) ->
          uterms_extract_if test [p]
      | UAsyncObj(l, g, _) ->
          uterms_extract_if test [l; g]
      | USyncObj(l, f, g, _) ->
          uterms_extract_if test [l;f;g]
      | UArrow(a, b) | UOr(a, b) | UAnd(a, b) ->
          (aux a) @ (aux b)
      | UBinding(_, tids, body) ->
          List.remove_all (fun id -> List.mem_assoc id tids) (aux body)
  in
    List.unique (aux t)

let umetaterm_nominals_to_tyctx t =
  ids_to_fresh_tyctx (umetaterm_extract_if is_nominal_name t)

let umetaterm_to_metaterm sub t =
  let rec aux t =
    match t with
      | UTrue -> True
      | UFalse -> False
      | UEq(a, b) -> Eq(uterm_to_term sub a, uterm_to_term sub b)
      | UAsyncObj(l, g, r) ->
          Obj(Async (Async.obj (Context.normalize [uterm_to_term sub l])
                (uterm_to_term sub g)), r)
      | USyncObj(l, f, g, r) ->
          Obj(Sync (Sync.obj (Context.normalize [uterm_to_term sub l])
                (uterm_to_term sub f) (uterm_to_term sub g)), r)
      | UArrow(a, b) -> Arrow(aux a, aux b)
      | UBinding(binder, tids, body) ->
          Binding(binder,
                  List.map_snd (apply_sub_ty sub) tids,
                  aux body)
      | UOr(a, b) -> Or(aux a, aux b)
      | UAnd(a, b) -> And(aux a, aux b)
      | UPred(p, r) -> Pred(uterm_to_term sub p, r)
  in
    aux t

let umetaterm_to_string t =
  metaterm_to_string (umetaterm_to_metaterm [] t)

let umetaterm_to_formatted_string t =
  metaterm_to_formatted_string (umetaterm_to_metaterm [] t)

let check_meta_logic_quantification_type ty =
  iter_ty
    (fun bty ->
       if bty = "prop" then
         failwith "Cannot quantify over type prop")
    ty

let check_meta_quantification t =
  let rec aux t =
    match t with
      | True | False | Eq _ | Obj _ | Pred _ -> ()
      | And(a, b) | Or(a, b) | Arrow(a, b) -> aux a; aux b
      | Binding(_, tids, body) ->
          List.iter
            check_meta_logic_quantification_type
            (List.map snd tids) ;
          aux body
  in
    aux t

let sync_to_async obj =
  { Async.context = obj.Sync.focus :: obj.Sync.context ;
    Async.term  = obj.Sync.term }

let metaterm_ensure_subordination sr t =
  let rec aux t =
    match t with
      | True | False -> ()
      | Eq(a, b) ->
          term_ensure_subordination sr a ;
          term_ensure_subordination sr b
      | Obj(Async obj, _) ->
          aux (async_to_member obj)
      (* what about the sync object ? I have no idea.
         -- Yuting *)
      | Obj(Sync obj, _) ->
          aux (async_to_member (sync_to_async obj))

        (* failwith "Un implemented: subordination of sync objects" *)
      | Arrow(a, b) | Or(a, b) | And(a, b) ->
          aux a ;
          aux b
      | Binding(_, tids, body) ->
          List.iter (Subordination.ensure sr) (List.map snd tids) ;
          aux body
      | Pred(p, _) ->
          term_ensure_subordination sr p
  in
    aux t

let type_umetaterm ~sr ~sign ?(ctx=[]) t =
  let nominal_tyctx = umetaterm_nominals_to_tyctx t in
  let tyctx =
    (List.map (fun (id, t) -> (id, tc [] t)) ctx)
      @ nominal_tyctx
  in
  let eqns = infer_constraints ~sign ~tyctx t in
  let sub = unify_constraints eqns in
  let ctx = ctx @ (tyctx_to_nominal_ctx (apply_sub_tyctx sub nominal_tyctx))
  in
  let result = replace_metaterm_vars ctx (umetaterm_to_metaterm sub t) in
    metaterm_ensure_fully_inferred result ;
    metaterm_ensure_subordination sr result ;
    check_meta_quantification result ;
    result


let type_udef ~sr ~sign (head, body) =
  let cids = umetaterm_extract_if is_capital_name head in
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns1 = infer_constraints ~sign ~tyctx head in
  let eqns2 = infer_constraints ~sign ~tyctx body in
  let sub = unify_constraints (eqns1 @ eqns2) in
  let ctx = tyctx_to_ctx (apply_sub_tyctx sub tyctx) in
  let (rhead, rbody) =
    (replace_metaterm_vars ctx (umetaterm_to_metaterm sub head),
     replace_metaterm_vars ctx (umetaterm_to_metaterm sub body))
  in
    metaterm_ensure_fully_inferred rhead ;
    metaterm_ensure_fully_inferred rbody ;
    metaterm_ensure_subordination sr rhead ;
    metaterm_ensure_subordination sr rbody ;
    check_meta_quantification rbody ;
    (rhead, rbody)

let type_udefs ~sr ~sign udefs =
  List.map (type_udef ~sr ~sign) udefs

(** Utilities *)

let rec has_capital_head t =
  match t with
    | UCon(_, id, _) -> is_capital_name id
    | ULam _ -> false
    | UApp(_, t, _) -> has_capital_head t
