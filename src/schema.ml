(****************************************************************************)
(* Schema Extension                                                         *)
(* Copyright (C) 2013 Savary Chaudhuri                                      *)
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
open Typing
open Abella_types
open Printf
open Prover

(* Global schema environment *)
let schemaExt = ref false 

type blocks = (id * ((id * ty) list * (id * ty) list * uterm)) list
let blocks : blocks ref = ref []

type schemas = (id * (int * ((id list)*(id list)*(((id list)*(id list)*id)) list) list)) list
let schemas : schemas ref = ref []




(* Schema toolbox *)
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



(* Schema hammer *)
(* SCHEMA *)

(* verify that each variable appearing in the substitution is only bound to a single term *)
let rec isPSub' sub c =
begin match sub with
| (pid,tm)::sub' -> 
    if (List.mem_assoc pid c) then 
      begin if term_to_string (List.assoc pid c) = (term_to_string tm)
      then isPSub' sub' c
      else false end
    else
      (isPSub' sub' ((pid,tm)::c))
| [] -> true
end

let rec isPSub sub = isPSub' sub []





let rec fvInTm tm = 
begin match observe tm with
|  Var v ->  [ Term.(v.name)]
|  App(th,tt) -> 
    let fvh = fvInTm th in
    let fvl = List.map fvInTm tt in
     rem_rep (List.append fvh (List.flatten fvl))
| Lam (idtys, tm') -> 
    let fv = fvInTm tm' in
    let (ids,tys) = List.split idtys in
    List.filter (fun id -> not (List.mem id ids)) fv
| DB _ -> []
|  _ -> failwith (sprintf "unexpected '%s' in fvInTm" (term_to_string tm))
end

(* TODO: return (b,sig,fv) where fv are the new free variables introduced by the sub and sig is (id,tm) list *)
(* verify if term "tm" matches pattern "ptn", returns "(b,sig)" where "b" is the answer, and "sig" a pattern substitution for which tm = (sig) ptn  
  eids is a list of exists-bound variables in ptn *)
let rec patternMatch tm ptn eids = 
  let (_,ctable) = !sign in
 begin match observe (hnorm tm), observe (hnorm ptn) with
 | Var v, Var pv -> 
       begin match (List.mem_assoc (term_to_string tm) ctable, List.mem_assoc (term_to_string ptn) ctable) with
      | true, true -> if (term_to_string tm) = (term_to_string ptn) then (true,[], []) else (false,[], []) (* both are the same constant *)
      | false, false -> (true, [(Term.(pv.name),tm)], [Term.(v.name)] )
      |	 _ , _ -> (false, [], [])
       end
 |  App(th,tt), App(pth, ptt) ->
     let (bh, subh, fvh) = patternMatch th pth eids in
     if bh then 
       let rl = List.map (fun (ctm,cptn) -> patternMatch ctm cptn eids) (List.combine tt ptt) in
       let (bl, subl, fvl) = listSplit3 rl in
       begin if (List.fold_left (fun bt ct -> bt && ct) true bl) then
	 let sub = List.append subh (List.flatten subl) in
	 let fv = rem_rep (List.append fvh (List.flatten fvl)) in
	 (* substitution *)
	 begin if isPSub sub then (true, sub,fv) else (false, [], []) end
       else (false, [], [])
       end
     else 
       (false, [], [])
 | App(th,tt), Var pv ->
   (* check if v is exists bound, then true, else [nabla bound or constant] false *)
   (* TODO: should also check that App is not A n1 n2... *)
      if (List.mem_assoc Term.(pv.name) eids) then (true, [(Term.(pv.name), tm)], fvInTm tm) else (false,[], [])
 | Lam(idtys,tm'), Lam(pidtys,ptn') ->  
      patternMatch tm' ptn' eids
 | DB i, DB j ->  if (i = j) then (true, [], []) else (false ,[], [])
 |  _ , _ -> (false, [], [])
 end


(* returns a list of (bool * (id * id) list)  with, for each pattern in bls, if t could match the pattern, and if it is the case, a substitution s.t. the term = @sub pat *)
let rec instOfPats t bls = 
List.map (fun (idtys1,idtys2,utm) ->  patternMatch t (uterm_to_term [] utm) idtys1 ) bls


let rec seqIdTerm id t nl = 
   begin match observe t with
   | App (th,tt) -> 
     let (nl',th') = seqIdTerm id th nl in
     let (nl'',tt') = (List.fold_right ( fun t (nl,tl) -> 
                                     let (nl',t') = seqIdTerm id t nl in
                                        (nl', t'::tl)) tt (nl',[])) in
    (nl'', app th' tt')
   | Var v -> 
 begin if Term.(v.tag = Nominal) then
        (nl,Term.(var Constant "" max_int (Ty([],"err"))))
   else
     let i = (List.hd nl)+1 in
     let vn = id^(string_of_int i) in
     (i::nl, var v.tag vn v.ts v.ty) end
   | _ -> failwith (sprintf "unexpected %s in seqIdTerm" (term_to_string t))
   end



let makeDummyVars nl = 
     let i = (List.hd nl)+1 in
     let v1n = "A"^(string_of_int i) in
     let v2n = "B"^(string_of_int i) in
      (i::nl, Term.(var Constant v1n max_int (Ty([],"err"))), Term.(var Constant v2n max_int (Ty([],"err"))))

(* make two terms with new variables Ai...Ai+n,Bi...Bi+1 leaving constants and "X" untouched *)
let rec uniteTerms t1 t2 nl v = 
   let (_,ctable) = !sign in
   begin match observe (hnorm t1),observe (hnorm t2) with
   | App (th1,tt1),App(th2,tt2) ->  
   begin if List.mem_assoc (term_to_string th1) ctable || List.mem_assoc (term_to_string th2) ctable then 
   let (nl,th1',th2') = uniteTerms th1 th2 nl v in
   let (nl,tt1',tt2') = (List.fold_right (fun (t1,t2) (nl, t1l,t2l) ->  
                             let (nl',t1',t2') =  uniteTerms t1 t2 nl v in
                                 (nl', t1'::t1l,t2'::t2l))
            (List.combine tt1 tt2) (nl,[],[])) in
   (nl, (app  th1' tt1'), (app th2' tt2'))
   else 
    makeDummyVars nl
   end 
   | Var v1 ,App(th2,tt2) -> 
   begin if List.mem_assoc (term_to_string th2) ctable then
   failwith (sprintf "Can't unify %s with eigenvariable %s in uniteTerms" (term_to_string t2) (Term.(v1.name))) 
   else 
    makeDummyVars nl
   end
   | App (th1,tt1), Var v2 -> 
   begin if List.mem_assoc (term_to_string th1) ctable then
   failwith (sprintf "Can't unify %s with eigenvariable %s in uniteTerms" (Term.(v2.name)) (term_to_string t1) ) 
   else 
    makeDummyVars nl
   end
   | Var v1, Var v2 ->
   begin if (term_to_string t1 = v) || List.mem_assoc Term.(v1.name) ctable then 
     (nl,t1,t2)
   else
 begin if Term.(v1.tag = Nominal) then
        (nl,Term.(var Constant "" max_int (Ty([],"err"))), Term.(var Constant "" max_int (Ty([],"err")))) else
     let i = (List.hd nl)+1 in
     let v1n = "A"^(string_of_int i) in
     let v2n = "B"^(string_of_int i) in
      (i::nl, Term.(var v1.tag v1n v1.ts v1.ty), Term.(var v2.tag v2n v2.ts v2.ty)) 
end
 end
   | Lam (idtys1, tm1'), Lam (idtys2,tm2') -> (* this is only correct if bound variables are represented with DB *)
      let (nl, tu1', tu2') =  uniteTerms tm1' tm2' nl v in
      (nl, lambda idtys1 tu1',lambda idtys2 tu2')
   | DB i, DB j -> if (i = j) then (nl, t1, t2) else failwith "Can't unify terms, bound variables are different"
   | _ , _ ->  
 failwith (sprintf "unexpected %s and %s in uniteTerms" (term_to_string t1) (term_to_string t2)) 
(* safe fail    makeDummyVars nl *)
   end

let rec replaceithby ng id tl =
begin match tl,ng with
   | t::tl',0 -> 
      Term.(var Constant id max_int (Ty([],"err")))::tl'
   | t::tl',_ -> t::(replaceithby (ng-1) id tl')
   | [],_ -> []
end
   

(* two terms to build the uniqueness theorem, position of the ground variable *)
let makeUniqueTerms t1 t2 ng v = 
   begin match observe t1, observe t2 with
   |App(th1,tt1),App(th2,tt2) -> 
   let (nl , t1, t2) = uniteTerms (app th1 (replaceithby (ng-1) v tt1)) (app th1 (replaceithby (ng-1) v tt2)) [0] v in
   ((List.tl (List.rev nl)), t1,t2)
   | _ , _ -> failwith (sprintf "unexpected %s and %s in makeUniqueTerms" (term_to_string t1) (term_to_string t2))
   end

let rec pairwiseEqual' t1l t2l =
  begin match t1l with
  |  t1::t1r ->
      begin match t2l with
      |	t2::t2r ->
	  (* printf "Pairwise equal: %s =? %s \n %!" (term_to_string t1) (term_to_string t2);*)
	  let eql = pairwiseEqual' t1r t2r in
	  if (term_to_string t2) = (term_to_string t1) then
	    1::eql
                                       else
	    0::eql
      |	[] -> failwith "unexpected in pairwiseEqual'"
      end
  |  [] ->  []
end


let pairwiseEqual t1 t2 = 
begin match t1 with
| App (t1h,t1l) ->
    begin match t2 with
    | App (t2h,t2l) -> if (term_to_string t1h) = (term_to_string t2h) then
	   pairwiseEqual' t1l t2l
	  else
	failwith "pairwiseEqual: dem terms can't be unified"
    | _ -> failwith "unexpected in pairwiseEqual"
    end
| _ -> failwith "unexpected in pairwiseEqual"
end

let rec pairwiseEqual2 t1 t2 = 
  let (_,ctable) = !sign in
  begin match (observe (hnorm t1), observe (hnorm t2)) with
  | Var v1, Var v2 -> 
      let v1n = Term.(v1.name) in
      let v2n = Term.(v2.name) in
      if v1n = v2n   then
        if (List.mem_assoc v1n ctable) then
	   []
	else
	   [v1n]
      else 
	[]
  | App (t1h,t1l), App(t2h,t2l) -> 
      begin try 
      let varll = List.map (fun (t1,t2) -> pairwiseEqual2 t1 t2) (List.combine (t1h::t1l) (t2h::t2l)) in
      let varl = List.flatten varll in
       rem_rep varl
      with Invalid_argument e -> [] end
  | Lam(idtys1, t1') , Lam(idtys2, t2') ->
      pairwiseEqual2 t1' t2'
 |  _ , _ ->  []
  end



(* Make one fresh definition for each pairs of exists, nabla bound variable *)
(*exists bound variables, nabla bound variables, id paired with their type *)
let rec makeFreshGeneric' tys1 ty2  =
  begin match tys1 with
  | ty1::tys1p ->
      let ty1str = (ty_to_string ty1) in
      let ty2str = (ty_to_string ty2) in
      let freshname = "fresh_"^ty2str^"_in_"^ty1str in
      if H.mem defs_table freshname then 
	makeFreshGeneric' tys1p ty2
      else 
      let freshstr = "Define "^freshname^" : "^ty2str^" -> "^ty1str^" -> prop by \n nabla n, "^freshname^" n X. \n" in
      let restOf = makeFreshGeneric' tys1p ty2  in
      freshstr^restOf
  | [] -> ""
  end


(* assumes there is no repetition in tys1,tys2 *)
let rec makeFreshGeneric tys1 tys2 =
  begin match tys2 with
  | ty2::tys2p -> 
      let curFresh = makeFreshGeneric' tys1 ty2 in
      let restOf = makeFreshGeneric tys1 tys2p in
       curFresh^restOf
  | [] -> ""


  end
(* assume there is no repetition in tys *)
let rec makeNameGeneric tys = 
begin match tys with
| ty::tys' ->
    let tystr = ty_to_string ty in
    let namename = tystr^"_name" in
    begin if H.mem defs_table namename then
      makeNameGeneric tys' 
    else
      let curName = "Define "^namename^" : "^tystr^" -> prop by \n nabla x, "^namename^" x.\n" in
      let restOf = makeNameGeneric tys' in
      curName^restOf
    end
| [] -> ""
end


(* Make one prune lemma for each nabla bound variable *)
(* nabla bound variables, id paired with their type *)
(* assume there is no repetition in tys *)
let rec makePruneGeneric tys =
  begin match tys with
  | ty::tysp -> 
      let tystr = ty_to_string ty in
      let prnname = "member_prune_"^tystr in
      if List.mem_assoc prnname !lemmas  then 
        makePruneGeneric tysp 
      else
	let prnstr = "Theorem "^prnname^" : forall G E, nabla (n:"^tystr^"),member (E n) G -> (exists E', E = x\\E').\n" in
	let prnprf = "induction on 1. intros. case H1. search. apply IH to H2. search.\n" in
	let restOf =  makePruneGeneric tysp in 
	prnstr^prnprf^restOf
  |  [] ->  ""
end

let rec makeBlockGeneric tys1 tys2 =
  let tys1 = rem_rep tys1 in
  let tys2 = rem_rep tys2 in
  let freshDefs = if tys1 = [] then makeNameGeneric tys2 else makeFreshGeneric tys1 tys2 in
  let pruneDefs = makePruneGeneric tys2 in
   freshDefs^pruneDefs

let add_block name block =
 blocks := (name, block)::!blocks

let get_block name =
 try List.assoc name !blocks 
 with Not_found -> failwith (sprintf "Block %s undefined." name)


(* get block and substitute variables names in it *)
let get_block_sub (idsa,idsb,bid) =
 let (idtys1,idtys2,utm) = get_block bid in
 begin if (List.length idtys1 <> List.length idsa)||(List.length idtys2 <> List.length idsb) then
    failwith (sprintf "Wrong number of arguments passed to block %s" bid) 
 else
   let (ids1,tys1) = List.split idtys1 in
   let (ids2,tys2) = List.split idtys2 in
   let utm' = rename_ids_in_uterm (List.append (List.combine ids1 idsa) (List.combine ids2 idsb)) utm in
   ((List.combine idsa tys1),(List.combine idsb tys2), utm')
 end 


let add_schema name schema =
 (schemaExt := true; schemas := (name, schema)::!schemas)

let get_schema name =
 try List.assoc name !schemas 
 with Not_found -> failwith (sprintf "Block %s undefined." name)


let rec one_fresh (id1,ty1) idtys2 = 
  begin match idtys2 with
 | (id2,ty2)::idtys2' ->
     let fresh = " fresh_"^(ty_to_string ty2)^"_in_"^(ty_to_string ty1)^" "^id2^" "^id1^" " in 
     let rst = one_fresh (id1,ty1) idtys2' in
     fresh::rst
 | [] -> []
  end

let rec all_fresh idtys1 idtys2 = 
  begin match idtys1 with
  | idty1::idtys1' -> 
      List.append (one_fresh idty1 idtys2) (all_fresh idtys1' idtys2)
  | [] -> []
end

let rec all_name idtys =
begin match idtys with
| (id,ty)::idtys' -> ((ty_to_string ty)^"_name"^" "^id)::(all_name idtys')
| [] -> []
end


(* t1 = ctx G1 ... GN *)
(* t2 = member E Gi *)
(* verifies that ctx is a defined schema *)
(* output (ctx, i, E) *)
let member_of_ith t1 t2 =
  begin match observe t1, observe t2 with
  | App (t1h,t1l), App(t2h,t2l) -> if ((term_to_string t2h) = "member") then
      let t1l' = List.map get_head_id t1l in 
(*      let t1l' = List.map term_to_string t1l in *)
      let gi = get_head_id (List.hd (List.tl t2l)) in 
(*      let gi = term_to_string (List.hd (List.tl t2l)) in *)
      let schName = term_to_string t1h in
      if (List.mem_assoc schName !schemas) then () else failwith ("Schema: "^schName^" is not the name of a defined schema");
       ( schName ,(mem_pos gi t1l'), List.hd t2l)
  else failwith "Schema: hypothesis should be of the form 'member E G'. "
  | _ -> failwith "Shema: hypothesis should be of the given form."
  end




let make_sync_clause i ((a,b,l),(it,sub, _)) = 
  let substr = List.map (fun (id,tm) -> (id, (term_to_string tm))) sub in
  begin match it with
  | true ->
      let ( j ,cl,idtys1,idtys2, eit,nit ) = 
	List.fold_left (fun (j,cstr,idty1,idty2, eit , nit ) -> fun c -> 
	  let ( c, d ,cbl) = get_block_sub c in
	  if (j = i) then
	    (j+1,cstr, idty1, idty2, rename_ids_in_idtys substr c, rename_ids_in_idtys substr d)
	  else 
	    let s = sprintf "member (%s) G%d" (uterm_to_string (rename_ids_in_uterm substr cbl)) j in
	    let c' = List.filter (fun (id,ty) -> not (List.mem_assoc id sub)) c in

	    let d' = List.filter (fun (id,ty) -> not (List.mem_assoc id sub)) d in (* actually none of these should match...should test *)
	    (j+1,s::cstr, (List.append c' idty1),(List.append d' idty2), eit, nit)) (1,[],[],[], [], []) l in
      let idtysa = rem_rep_pairs idtys1 in
      let idtysb = rem_rep_pairs idtys2 in
      let (ida',tya) = List.split idtysa in
      let (idb',tyb) = List.split idtysb in
      let freshl = all_fresh idtysa (List.append nit idtysb)  (* all_fresh (List.append idtysa eit) (List.append idtysb nit)  *) in  (* doesn't work if e.g. B -> foo A *)
      let ab = List.append ida' idb' in
      if ab = [] then "("^(String.concat " /\\ " (List.append cl freshl))^")" else
      sprintf "(exists %s, %s)" (String.concat " " ab) (String.concat " /\\ " (List.append cl freshl))
  | false -> ""
  end


(* TODO: make processing of clauses a helper function instead of an anon one *)
(* ids: (a,b, (c,d,e) list) list *)
(* ground on the ith projection of the context *)
(* fresh on a b *)
(* for every (c,d,e) other than the ith, member l(c,d,e) Gjth *)
(* for ith (c,d,e), E = l(c,d,e) *)
let make_sync_stmt i id arr ids ads tm = 
  let clstrl = List.map  (make_sync_clause i) (List.combine ids ads) in
  List.iteri (printf "%d: Make_sync_clause  %s \n") clstrl; flush stdout;
  let clstrl = List.filter (fun s -> not (s = "")) clstrl in
    let ctxgl =  string_count arr "G" in
    let ctxg = String.concat " " ctxgl in
    sprintf "forall %s, %s -> member (%s) G%d -> %s. \n" ctxg (id^" "^ctxg) (term_to_string tm) i (String.concat " \\/ \n" clstrl)




let make_sync_prf ads = 
let clstrl = List.map (fun (b,_,_) -> if b then "H4inv: case H2inv. search. apply IHinv to H3inv H4inv. search." else "H4inv: case H2inv. apply IHinv to H3inv H4inv. search.") ads in
 "IHinv: induction on 1. intros H1inv H2inv. H3inv: case H1inv. H4inv: case H2inv.\n"^(String.concat "\n" clstrl)


(* ids: (a,b, (c,d,e) list) list *)
(* ground on the ith projection of the context *)
(* fresh on a b *)
(* for every (c,d,e) other than the ith, member l(c,d,e) Gjth *)
(* for ith (c,d,e), E = l(c,d,e) *)
let make_inv_stmt i id arr ids  =
    let clstrl = List.map (fun (a,b,l) ->
                       let (j,cl,idty1,idty2) = 
			 List.fold_left (fun (j,cstr,idty1,idty2) -> fun c -> 
			   let ( c, d ,cbl) = get_block_sub c in
	   let s = begin if j = i then
			      sprintf "E = (%s)" (uterm_to_string cbl) 
			   else
			     sprintf "member (%s) G%d" (uterm_to_string cbl) j
			   end in
			   (j+1,s::cstr,List.append idty1 c,List.append idty2 d)) (1,[],[],[]) l in
		       let idtya = List.map (fun id -> (id, List.assoc id idty1)) a in
		       let idtyb = List.map (fun id -> (id, List.assoc id idty2)) b in
		       let freshl = if a = [] then all_name idtyb else all_fresh idtya idtyb in
		       let ab = List.append a b in
		       if ab = [] then "("^(String.concat " /\\ " (List.append cl freshl))^")" else
		       sprintf "(exists %s, %s)" (String.concat " " (List.append a b)) (String.concat " /\\ " (List.append cl freshl))) ids in
    let ctxgl =  string_count arr "G" in
    let ctxg = String.concat " " ctxgl in
    sprintf "forall E %s, %s -> member E G%d -> %s. \n" ctxg (id^" "^ctxg) i (String.concat " \\/ \n" clstrl)


let make_inv_prf ids =
  let i = List.length ids in
  let bsl = if i < 2 then " search. \n" else " case H5inv."^(str_repeat i " search.")^" \n" in
  "IHinv: induction on 1. intros H1inv H2inv. H3inv : case H1inv. case H2inv."^(str_repeat i (" H4inv : case H2inv. search. H5inv: apply IHinv to H3inv H4inv."^bsl))


let rec safeUniqueGround mts ads cvar =
begin match (mts, ads) with
| (cmts::mts', (false,_,_)::ads') -> 
    let (b,rel) = (safeUniqueGround mts' ads' cvar) in
     (b, rel)
| ((idtys1,idtys2,ut)::mts', (true,sads,_)::ads') -> 
    let (idl,tml) = List.split sads in
    let tmstrl = List.map term_to_string tml in
    let sads' = List.combine tmstrl idl  in
    begin if List.mem_assoc cvar sads' then
      let blid = List.assoc cvar sads' in
        if List.mem_assoc blid idtys2 then
	   let (b,rel) = (safeUniqueGround mts' ads' cvar) in
	    (b, blid::rel)
	else
	  let _ = (printf "ground fails(1) on %s, %s assoc with %s . \n" (uterm_to_string ut) cvar blid) in (false, [])
    else
      let _ = (printf "ground fails(2) on %s, no assoc for %s . \n" (uterm_to_string ut) cvar) in (false, [])
    end
| ([],[]) -> (true, [])
|  _ -> failwith "Schema: Unexpected in safeUniqueGround"
end

let rec safeUniqueGrounds mts ads varl = 
begin match varl with
| cvar::varl' -> 
    let (b,rel)  = safeUniqueGround mts ads cvar in
    if b then (cvar, rel) else safeUniqueGrounds mts ads varl'
| [] -> failwith "Schema: Can't ground unique theorem for given assumption"
end


let rec safe_uni_ground eql bls ads n = 
  begin match eql with
  | 1::eqlr -> if (List.fold_left 
		     (fun a ((idtys1,idtys2,ut),matches) -> 
		       begin match a with
		       | true -> 
			   (* check if the block could add the assumption *)
			   if matches then
			     let cid = term_to_string (get_nth_id n (uterm_to_term [] ut)) in
			     let (id2,_) = List.split idtys2 in
			     List.mem cid id2
			   else true
		       | false -> false
		       end) 
		     true (List.combine bls ads))
      then n else safe_uni_ground eqlr bls ads (n+1) 
  | _::eqlr -> safe_uni_ground eqlr bls ads (n+1)
  | [] -> failwith "Can't ground unique theorem for given assumption"
  end


   




(* schemaname, nabla ground, canonical block, number of exists bound variables as a list, arriety of the schema, block being uniqued *)
let make_uni_stmt id tm1 tm2 nl arr gi gv =
   let idsA = List.map (fun i -> "A"^(string_of_int i)) nl in
   let idsB = List.map (fun i -> "B"^(string_of_int i)) nl in
  let eqstrl = List.map (fun (a,b) -> a^" = "^b) (List.combine idsA idsB) in
    let ctxgl =  string_count arr "G" in
    let ctxg = String.concat " " ctxgl in
  "forall "^ctxg^" "^(String.concat " " (List.append (gv::idsA) idsB))^" , "^id^" "^ctxg^" -> member ( "^(term_to_string tm1)^") G"^(string_of_int gi) ^" -> member ("^(term_to_string tm2)^") G"^(string_of_int gi) ^" -> "^(String.concat " /\\ " eqstrl)^" ." 



(* schemaname, block names, blocks, block_include *)
 let make_uni_prf id mts ads = 
  let h1 =   "IHuni: induction on 1. intros H1uni H2uni H3uni. H4uni: case H1uni. case H2uni.\n" in
  let h2l = List.map (fun ((idtys1,idtys2,utm),b) -> 
   if b then
     let (id2,ty2) = List.hd idtys2 in 
  "H5uni: case H2uni. H6uni: case H3uni. search. apply member_prune_"^(ty_to_string ty2)^" to H6uni.\n"^"H6uni: case H3uni. apply member_prune_"^(ty_to_string ty2)^" to H5uni. apply IHuni to H4uni H5uni H6uni. search."
  else  "H5uni:case H2uni. H6uni: case H3uni. apply IHuni to H4uni H5uni H6uni. search."
) (List.combine mts ads) in
  h1^(String.concat "" h2l)

 


