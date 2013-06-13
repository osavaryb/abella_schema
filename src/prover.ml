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
open Typing
open Metaterm
open Format
open Tactics
open Abella_types
open Extensions

module H = Hashtbl

type lemmas = (id * metaterm) list
let lemmas : lemmas ref = ref []

(* SCHEMA *)
type blocks = (id * ((id * ty) list * (id * ty) list * uterm)) list
let blocks : blocks ref = ref []

type schemas = (id * (id list)) list
let schemas : schemas ref = ref []

type subgoal = unit -> unit
let subgoals : subgoal list ref = ref []

type hyp = {
  id : id ;
  term : metaterm ;
  mutable abbrev : string option ;
}

type sequent = {
  mutable vars : (id * term) list ;
  mutable hyps : hyp list ;
  mutable goal : metaterm ;
  mutable count : int ;
  mutable name : string ;
  mutable next_subgoal_id : int ;
}

let sequent = {
  vars = [] ;
  hyps = [] ;
  goal = termobj (const "placeholder" propty) ;
  count = 0 ;
  name = "" ;
  next_subgoal_id = 1 ;
}

let sign = ref pervasive_sign
let sr = ref pervasive_sr

let add_global_types tys =
  sign := add_types !sign tys

let locally_add_global_consts cs =
  let local_sr = List.fold_left Subordination.update !sr (List.map snd cs)
  and local_sign = add_consts !sign cs
  in (local_sr, local_sign)

let commit_global_consts local_sr local_sign =
  sr := local_sr ;
  sign := local_sign

let add_global_consts cs =
  sr := List.fold_left Subordination.update !sr (List.map snd cs) ;
  sign := add_consts !sign cs

let close_types ids =
  begin match List.minus ids (fst !sign) with
    | [] -> ()
    | xs -> failwith ("Unknown type(s): " ^ (String.concat ", " xs))
  end ;
  begin match List.intersect ["o"; "olist"; "prop"] ids with
    | [] -> ()
    | xs -> failwith ("Cannot close " ^ (String.concat ", " xs))
  end ;
  sr := Subordination.close !sr ids

let add_subgoals ?(mainline) new_subgoals =
  let extend_name i =
    if sequent.name = "" then
      sequent.name <- string_of_int i
    else
      sequent.name <- sequent.name ^ "." ^ (string_of_int i)
  in
  let rec annotate i gs =
    match gs with
      | [] -> []
      | g::rest ->
          (fun () -> g (); extend_name i; sequent.next_subgoal_id <- 1) ::
            annotate (i+1) rest
  in
  let n = List.length new_subgoals in
  let annotated_subgoals =
    match mainline with
      | None ->
          if n > 1 then
            annotate sequent.next_subgoal_id new_subgoals
          else
            new_subgoals
      | Some mainline ->
          let new_mainline () =
            mainline () ;
            sequent.next_subgoal_id <- sequent.next_subgoal_id + n
          in
            annotate sequent.next_subgoal_id new_subgoals @ [new_mainline]
  in
    subgoals := annotated_subgoals @ !subgoals

(* The vars = sequent.vars is superfluous, but forces the copy *)
let copy_sequent () =
  {sequent with vars = sequent.vars}

let set_sequent other =
  sequent.vars <- other.vars ;
  sequent.hyps <- other.hyps ;
  sequent.goal <- other.goal ;
  sequent.count <- other.count ;
  sequent.name <- other.name ;
  sequent.next_subgoal_id <- other.next_subgoal_id

let fresh_hyp_name base =
  if base = "" then begin
    sequent.count <- sequent.count + 1 ;
    "H" ^ (string_of_int sequent.count)
  end else
    fresh_name base (List.map (fun h -> (h.id, ())) sequent.hyps)

let normalize_sequent () =
  sequent.goal <- normalize sequent.goal ;
  sequent.hyps <-
    sequent.hyps |> List.map (fun h -> { h with term = normalize h.term })

(* Clauses *)

let clauses : clauses ref = ref []

let add_clauses new_clauses =
  clauses := !clauses @ new_clauses



let parse_defs str =
  type_udefs ~sr:!sr ~sign:!sign (Parser.defs Lexer.token (Lexing.from_string str))

let defs_table : defs_table = H.create 10
let () = H.add defs_table "member"
  (Inductive,
   ["member"],
   parse_defs "member A (A :: L) ; member A (B :: L) := member A L.")

let add_defs ids ty defs =
  List.iter
    (fun id -> if H.mem defs_table id then
       failwith (id ^ " has already been defined"))
    ids ;
  List.iter
    (fun id -> H.add defs_table id (ty, ids, defs))
    ids


(* Undo support *)

type undo_stack = (sequent * subgoal list * Term.bind_state) list
let undo_stack : undo_stack ref = ref []

let save_undo_state () =
  undo_stack := (copy_sequent (), !subgoals, Term.get_bind_state ())::
    !undo_stack

let undo () =
  match !undo_stack with
    | (saved_sequent, saved_subgoals, bind_state)::rest ->
        set_sequent saved_sequent ;
        subgoals := saved_subgoals ;
        Term.set_bind_state bind_state ;
        undo_stack := rest
    | [] -> failwith "Nothing left to undo"


(* Proof state manipulation utilities *)

let reset_prover =
  let original_state = get_bind_state () in
  let original_sequent = copy_sequent () in
    fun () ->
      set_bind_state original_state ;
      set_sequent original_sequent ;
      subgoals := [] ;
      undo_stack := []

let full_reset_prover =
  let original_clauses = !clauses in
  let original_defs_table = H.copy defs_table in
    fun () ->
      reset_prover () ;
      clauses := original_clauses ;
      H.assign defs_table original_defs_table

let add_hyp ?name term =
  let name = fresh_hyp_name begin
    match name with
      | None -> ""
      | Some name -> name
  end in
  sequent.hyps <- List.append sequent.hyps
    [{ id = name ; term = term ; abbrev = None }]

let remove_hyp name =
  sequent.hyps <- List.remove_all (fun h -> h.id = name) sequent.hyps

let replace_hyp name t =
  let rec aux hyplist =
    match hyplist with
      | [] -> []
      | hyp::rest when hyp.id = name -> {hyp with term = t} :: rest
      | hyp::rest -> hyp :: (aux rest)
  in
    sequent.hyps <- aux sequent.hyps

let add_var v =
  sequent.vars <- List.append sequent.vars [v]

let add_if_new_var (name, v) =
  if not (List.mem_assoc name sequent.vars) then
    add_var (name, v)

let add_lemma name lemma =
  lemmas := (name, lemma)::!lemmas

let get_hyp name =
  let hyp = List.find (fun h -> h.id = name) sequent.hyps in
    hyp.term

let get_lemma name =
  List.assoc name !lemmas

(* SCHEMA *)



(* Cases: hd1 <~> hd2 <~ hd3 & args1 args2 are pairwise uni to args3 *)
(* returns true if tm could the described pattern ptm, false otherwise *)
let rec instOfPat tm eids ptm ctable =
   begin match observe tm, observe ptm  with
   | Var _, Var _ -> 
       begin match (List.mem_assoc (term_to_string tm) ctable, List.mem_assoc (term_to_string ptm) ctable) with
      | true, true -> if (term_to_string tm) = (term_to_string ptm) then true else false
      | false, false -> true
      | _ , _ -> false
      end
   | App(th,tt), App(pth,ptt) ->  begin try (instOfPat th eids pth ctable) && (List.fold_left (fun cur (tm',ptm') -> cur && (instOfPat tm' eids ptm' ctable)) true (List.combine tt ptt))
                                  with
                                   | e -> false
                                  end
   | App(th,tt), Var v -> 
   (* check if v is exists bound, then true, else [nabla bound] false *)
      if (List.mem_assoc Term.(v.name) eids) then true else false
(*            if List.mem_assoc Term.(v.name) ctable then false else true *)
   | Var v, App(pth,ptt) -> false
 (*            if List.mem_assoc Term.(v.name) ctable then false else true *)
   | Lam (idtys,tm'), _ -> failwith "Lambda case of tm unimplemented in instOfPats"
   | _ , _ -> failwith "unexpected in instOfPats (2)"
   end

(* returns a bitmap of booleans indicating, for each pattern in bls, if t1 and t2 could both match it *)
let rec instOfPats t bls sign =
let (_,ctable) = sign in
begin match bls with
| (idtys1,idtys2,utm)::bls' -> (instOfPat t idtys1 (uterm_to_term [] utm) ctable)::(instOfPats t bls' sign)
| [] -> []
end

(*
  let pstr = (get_head_id (get_nth_id 1 t1)) in
  List.map (fun (idtys1,idtys2,utm) ->  
    begin match observe (uterm_to_term [] utm) with 
    |  App(th,tt) -> 
	if  (pstr = (term_to_string th)) then 1 else 0
    |	 _ ->  0
    end) bls

*)

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
let rec uniteTerms t1 t2 nl = 
   let (_,ctable) = !sign in
   begin match observe t1,observe t2 with
   | App (th1,tt1),App(th2,tt2) ->  
   begin if List.mem_assoc (term_to_string th1) ctable || List.mem_assoc (term_to_string th2) ctable then 
   let (nl,th1',th2') = uniteTerms th1 th2 nl in
   let (nl,tt1',tt2') = (List.fold_right (fun (t1,t2) (nl, t1l,t2l) ->  
                             let (nl',t1',t2') =  uniteTerms t1 t2 nl in
                                 (nl', t1'::t1l,t2'::t2l))
            (List.combine tt1 tt2) (nl,[],[])) in
   (nl, (app  th1' tt1'), (app th2' tt2'))
   else 
    makeDummyVars nl
   end 
   | Var v1 ,App(th2,tt2) -> 
   begin if List.mem_assoc (term_to_string th2) ctable then
   failwith (sprintf "Can't unify %s with eigenvariable %s in uniteTerms" (term_to_string t2) (Term.(v1.name))) 
(*    let (nl1, t1) = seqIdTerm "A" t2 nl in
   let (nl2, t2) = seqIdTerm "B" t2 nl in 
   (nl2,t1,t2) *)
   else 
    makeDummyVars nl
   end
   | App (th1,tt1), Var v2 -> 
   begin if List.mem_assoc (term_to_string th1) ctable then
   failwith (sprintf "Can't unify %s with eigenvariable %s in uniteTerms" (Term.(v2.name)) (term_to_string t1) ) 
(*   let (nl1, t1) = seqIdTerm "A" t1 nl in
   let (nl2, t2) = seqIdTerm "B" t1 nl in 
   (nl2,t1,t2)*)
   else 
    makeDummyVars nl
   end
   | Var v1, Var v2 ->
   begin if (term_to_string t1 = "X") || List.mem_assoc Term.(v1.name) ctable then 
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
let makeUniqueTerms t1 t2 ng = 
   begin match observe t1, observe t2 with
   |App(th1,tt1),App(th2,tt2) -> 
   let (nl , t1, t2) = uniteTerms (app th1 (replaceithby (ng-1) "X" tt1)) (app th1 (replaceithby (ng-1) "X" tt2)) [0] in
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
    let curName = "Define "^namename^" : "^tystr^" -> prop by \n nabla x, "^namename^" x.\n" in
    let restOf = makeNameGeneric tys' in
    curName^restOf
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

(* I could remove the repeated types in tys1 and tys2 *)
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

let add_schema name schema =
 schemas := (name, schema)::!schemas

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
| (id,ty)::idtys' -> ((ty_to_string ty)^"_var"^" "^id)::(all_name idtys')
| [] -> []
end

let make_inv_stmt id ids = 
  	    let mts = List.map get_block ids in
	    let invstrl = List.map (fun (idtys1,idtys2,utm) -> 
	      let (id1s,ty1s) = List.split idtys1 in
	      let (id2s,ty2s) = List.split idtys2 in
	      let freshl = all_fresh idtys1 idtys2 in
	      if (List.append id1s id2s) = [] then "(E = "^(uterm_to_string utm)^")" else " (exists "^(String.concat " " id1s)^" "^(String.concat " " id2s)^", E = "^(uterm_to_string utm)^" /\\ "^(String.concat "/\\" freshl)^") ") mts in
	    "forall E G, \n "^id^" G -> member E G ->"^(String.concat "\\/ \n" invstrl)^". \n"

let make_inv_prf ids =
  "IHinv: induction on 1. intros H1inv H2inv. H3inv : case H1inv. case H2inv."^(str_repeat (List.length ids) "H4inv : case H2inv. search. apply IHinv to H3inv H4inv. search. \n")


let rec safe_uni_ground eql bls n = 
  begin match eql with
  | 1::eqlr -> if (List.fold_left 
		     (fun a (idtys1,idtys2,ut) -> 
		       begin match a with
		       | true -> 
			   let cid = term_to_string (get_nth_id n (uterm_to_term [] ut)) in
			   let (id2,_) = List.split idtys2 in
			   List.mem cid id2
		       | false -> false
		       end) 
		     true bls)
  then n else safe_uni_ground eqlr bls (n+1)
  | _::eqlr -> safe_uni_ground eqlr bls (n+1)
  | [] -> failwith "Can't ground unique theorem for given assumption"
  end




(* schemaname, nabla ground, canonical block *)
let make_uni_stmt' id tm1 tm2 nl =
   let idsA = List.map (fun i -> "A"^(string_of_int i)) nl in
   let idsB = List.map (fun i -> "B"^(string_of_int i)) nl in
  let eqstrl = List.map (fun (a,b) -> a^" = "^b) (List.combine idsA idsB) in
  "forall G X "^(String.concat " " (List.append idsA idsB))^" , "^id^" G -> member ( "^(term_to_string tm1)^") G -> member ("^(term_to_string tm2)^") G -> "^(String.concat " /\\ " eqstrl)^" ." 


let make_uni_stmt id n (idtys1,idtys2,utm) =
  let ac = ref 0 in
  let bc = ref 0 in
  let idground = term_to_string (get_nth_id n (uterm_to_term [] utm)) in
  let idGround = String.capitalize idground in
  let idtys2' = List.remove_assoc idground idtys2 in
  let (id2s,_) = List.split idtys2' in
  let (id1s,_) = List.split idtys1 in
  let idaA = List.map (fun id -> ac := !ac+1; (id, "A"^(string_of_int !ac))) (List.append id1s id2s) in
  let idaB = List.map (fun id -> bc := !bc+1; (id, "B"^(string_of_int !bc))) (List.append id1s id2s) in
  let tmAstr = uterm_to_string (rename_ids_in_uterm ((idground,idGround)::idaA) utm) in
  let tmBstr = uterm_to_string (rename_ids_in_uterm ((idground,idGround)::idaB) utm) in
  let (_,idsA) = List.split idaA in
  let (_,idsB) = List.split idaB in
  let eqstrl = List.map (fun (a,b) -> a^" = "^b) (List.combine idsA idsB) in
  "forall G "^idGround^" "^(String.concat " " (List.append idsA idsB))^" , "^id^" G -> member ( "^tmAstr^") G -> member ("^tmBstr^") G -> "^(String.concat " /\\ " eqstrl)^" ." 


(* schemaname, block names, blocks, block_include *)
 let make_uni_prf id mts ads = 
  let h1 =   "IHuni: induction on 1. intros H1uni H2uni H3uni. H4uni: case H1uni. case H2uni.\n" in
  let h2l = List.map (fun ((idtys1,idtys2,utm),b) -> 
    let (id2,ty2) = List.hd idtys2 in 
   if b then
  "H5uni: case H2uni. H6uni: case H3uni. search. apply member_prune_"^(ty_to_string ty2)^" to H6uni.\n"^"H6uni: case H3uni. apply member_prune_"^(ty_to_string ty2)^" to H5uni. apply IHuni to H4uni H5uni H6uni. search."
  else  "H5uni:case H2uni. H6uni: case H3uni. apply IHuni to H4uni H5uni H6uni. search."
) (List.combine mts ads) in
  h1^(String.concat "" h2l)

(* END OF SCHEMA *)

let get_hyp_or_lemma name =
  try
    get_hyp name
  with
      Not_found -> get_lemma name

let next_subgoal () =
  match !subgoals with
    | [] -> failwith "Proof completed."
    | set_subgoal::rest ->
        set_subgoal () ;
        normalize_sequent () ;
        subgoals := rest


(* Pretty print *)

let vars_to_string () =
  match sequent.vars with
    | [] -> ""
    | _ -> "Variables: " ^ (String.concat ", " (List.map fst sequent.vars))

let format_vars fmt =
  let rec aux fmt xs =
    match xs with
      | x::y::ys -> fprintf fmt "%s,@ " (fst x) ; aux fmt (y::ys)
      | [x] -> fprintf fmt "%s" (fst x)
      | [] -> assert false
  in
    if sequent.vars = [] then
      fprintf fmt "@\n"
    else
      fprintf fmt "  Variables: @[%a@]@\n" aux sequent.vars

let format_hyp fmt hyp =
  fprintf fmt "%s : " hyp.id ;
  begin match hyp.abbrev with
    | None -> format_metaterm fmt hyp.term
    | Some s -> fprintf fmt "%s" s
  end;
  pp_force_newline fmt ()

let format_hyps fmt =
  List.iter (format_hyp fmt) sequent.hyps

let format_count_subgoals fmt n =
  match n with
    | 0 -> ()
    | 1 -> fprintf fmt "1 other subgoal.@\n@\n"
    | n -> fprintf fmt "%d other subgoals.@\n@\n" n

let format_display_subgoals fmt n =
  save_undo_state () ;
  let count = ref 0 in
    List.iter (fun set_state ->
                 set_state () ;
                 if String.count sequent.name '.' > n then
                   fprintf fmt "@[<1>Subgoal %s%sis:@\n%a@]@\n@\n"
                     sequent.name
                     (if sequent.name = "" then "" else " ")
                     format_metaterm (normalize sequent.goal)
                 else
                   incr count)
      !subgoals ;
    format_count_subgoals fmt !count ;
    undo ()

let subgoal_depth = ref 1000

let format_other_subgoals fmt =
  format_display_subgoals fmt (String.count sequent.name '.' - !subgoal_depth)

let format_sequent fmt =
  pp_open_box fmt 2 ;
  format_vars fmt ;
  format_hyps fmt ;
  fprintf fmt "============================@\n" ;
  fprintf fmt " %a" format_metaterm sequent.goal ;
  pp_close_box fmt ()

let format_display fmt =
  pp_open_box fmt 0 ;
  if sequent.name = "" then
    fprintf fmt "@\n"
  else
    fprintf fmt "Subgoal %s:@\n@\n" sequent.name;
  format_sequent fmt ;
  fprintf fmt "@\n@\n" ;
  format_other_subgoals fmt ;
  pp_close_box fmt () ;
  pp_print_flush fmt ()

let display out =
  format_display (formatter_of_out_channel out)

let get_display () =
  let b = Buffer.create 100 in
    format_display (formatter_of_buffer b) ;
    Buffer.contents b


(* Object level instantiation *)

let inst ?name h ws =
  let ht = get_hyp h in
    match ht with
      | Obj _ ->
          let rec aux ws ht = match ws with
            | [] -> add_hyp ?name ht
            | (n, t) :: ws ->
                let ht = begin try
                  let ntids = metaterm_nominal_tids ht in
                  let nty = List.assoc n ntids in
                  let ctx = sequent.vars @
                    (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
                  in
                  let t = type_uterm ~expected_ty:nty ~sr:!sr ~sign:!sign ~ctx t in
                  object_inst ht n t
                with
                  | Not_found ->
                      failwith "Vacuous instantiation"
                end in
                  aux ws ht
          in
            aux ws ht
      | _ -> failwith
          "Instantiation can only be used on hypotheses of the form {...}"


(* Object level cut *)

let cut ?name h arg =
  let h = get_hyp h in
  let arg = get_hyp arg in
    match h, arg with
      | Obj(obj_h, _), Obj(obj_arg, _) ->
          add_hyp ?name (object_cut obj_h obj_arg)
      | _ -> failwith "Cut can only be used on hypotheses of the form {...}"


(* Search *)

let has_inductive_hyps hyp =
  let rec aux term =
    match term with
      | Binding(Forall, _, body) -> aux body
      | Binding(Nabla, _, body) -> aux body
      | Arrow(Obj(_, Smaller i), _) -> true
      | Arrow(Pred(_, Smaller i), _) -> true
      | Arrow(left, right) -> aux right
      | _ -> false
  in
    aux hyp.term

let remove_inductive_hypotheses hyps =
  List.remove_all has_inductive_hyps hyps

let has_coinductive_result hyp =
  let rec aux term nested =
    match term with
      | Binding(Forall, _, body) -> aux body true
      | Binding(Nabla, _, body) -> aux body true
      | Arrow(left, right) -> aux right true
      | Pred(_, CoSmaller _) -> nested
      | Pred(_, CoEqual _) -> nested
      | _ -> false
  in
    aux hyp.term false

let remove_coinductive_hypotheses hyps =
  List.remove_all has_coinductive_result hyps

let defs_table_to_list () =
  H.fold (fun _ (_, mutual, dcs) acc -> (mutual, dcs) :: acc) defs_table []

let search_depth = ref 5

let search_goal_witness ?depth goal =
  let hyps = sequent.hyps
    |> remove_inductive_hypotheses
    |> remove_coinductive_hypotheses
    |> List.map (fun h -> (h.id, h.term))
  in
  let depth = Option.default !search_depth depth in
  let search_depth n =
    Tactics.search
      ~depth:n
      ~hyps
      ~clauses:!clauses
      ~alldefs:(defs_table_to_list ())
      goal
  in
    List.find_some search_depth (List.range 1 depth)

let search_goal goal =
  Option.is_some (search_goal_witness goal)

let search ?(limit=None) ?(interactive=true) ?(witness=ignore) () =
  let search_result = match limit with
    | None -> search_goal_witness sequent.goal
    | Some depth -> search_goal_witness ~depth sequent.goal
  in
    match search_result with
      | None -> if not interactive then failwith "Search failed"
      | Some w -> witness w ; next_subgoal ()

(* Search cut *)

let search_cut ?name h =
  match get_hyp h with
    | Obj(obj, _) ->
        add_hyp ?name (Obj(search_cut ~search_goal obj, Irrelevant))
    | _ ->
        failwith "Cut can only be used on hypotheses of the form {... |- ...}"


(* Case analysis *)

(* Lifting during case analysis may cause some variables to be bound to
   themselves. We need to update sequent.vars to reflect this. *)
let update_self_bound_vars () =
  sequent.vars <-
    sequent.vars |> List.map
        (fun (id, term) ->
           match term_head_var term with
             | Some v when term_to_name v = id ->
                 (id, v)
             | _ -> (id, term))

let case_to_subgoal ?name case =
  let saved_sequent = copy_sequent () in
    fun () ->
      set_sequent saved_sequent ;
      List.iter add_if_new_var case.new_vars ;
      List.iter (add_hyp ?name) case.new_hyps ;
      Term.set_bind_state case.bind_state ;
      update_self_bound_vars ()

let get_defs term =
  match term with
    | Pred(p, _) ->
        begin try
          let (_, mutual, defs) = H.find defs_table (term_head_name p) in
            (mutual, defs)
        with Not_found ->
          failwith "Cannot perform case-analysis on undefined atom"
        end
    | _ -> ([], [])

let case ?name ?(keep=false) str =
  let term = get_hyp str in
  let global_support =
    (List.flatten_map metaterm_support
       (List.map (fun h -> h.term) sequent.hyps)) @
      (metaterm_support sequent.goal)
  in
  let (mutual, defs) = get_defs term in
  let cases =
    Tactics.case ~used:sequent.vars ~sr:!sr ~clauses:!clauses
      ~mutual ~defs ~global_support term
  in
    if not keep then remove_hyp str ;
    add_subgoals (List.map (case_to_subgoal ?name) cases) ;
    next_subgoal ()



(* Assert *)

let goal_to_subgoal g =
  let saved_sequent = copy_sequent () in
  let bind_state = Term.get_bind_state () in
    fun () ->
      set_sequent saved_sequent ;
      Term.set_bind_state bind_state ;
      sequent.goal <- g


let delay_mainline ?name new_hyp detour_goal =
  if search_goal detour_goal then
    add_hyp ?name new_hyp
  else
    let mainline =
      case_to_subgoal ?name
        { bind_state = get_bind_state () ;
          new_vars = [] ;
          new_hyps = [new_hyp] }
    in
    let detour = goal_to_subgoal detour_goal in
      (* Using add_subgoals to take care of annotations *)
      add_subgoals ~mainline [detour] ;
      next_subgoal ()

let assert_hyp ?name term =
  let term = type_umetaterm ~sr:!sr ~sign:!sign ~ctx:sequent.vars term in
    delay_mainline ?name term term


(* Apply *)

let get_some_hyp name =
  if name = "_" then
    None
  else
    Some (get_hyp name)

let ensure_no_logic_variable terms =
  let logic_vars = List.flatten_map (metaterm_vars_alist Logic) terms in
  if logic_vars <> [] then
    failwith "Found logic variable at toplevel"

let ensure_no_restrictions term =
  let rec aux t nested =
    match t with
      | Binding(Forall, _, body) -> aux body true
      | Binding(Nabla, _, body) -> aux body true
      | Arrow(left, right) -> aux left true; aux right true
      | Obj(_, Smaller i) | Obj(_, Equal i)
      | Pred(_, Smaller i) | Pred(_, Equal i) ->
          if nested then invalid_metaterm_arg term
      | Pred(_, CoSmaller i) | Pred(_, CoEqual i) ->
          invalid_metaterm_arg term
      | _ -> ()
  in
    aux term false

let toplevel_bindings stmt =
  let rec aux = function
    | Binding(Forall, tids, t) -> tids @ (aux t)
    | Binding(Nabla, tids, t) -> tids @ (aux t)
    | _ -> []
  in
    aux stmt

let type_apply_withs stmt ws =
  let bindings = toplevel_bindings stmt in
    List.map
      (fun (id, t) ->
         try
           let ty = List.assoc id bindings in
             (id, type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign ~ctx:sequent.vars t)
         with
           | Not_found -> failwith ("Unknown variable " ^ id ^ "."))
      ws

let partition_obligations obligations =
  Either.partition_eithers
    (List.map
       (fun g -> match search_goal_witness g with
          | None -> Either.Left g
          | Some w -> Either.Right (g, w))
       obligations)




let apply ?name ?(term_witness=ignore) h args ws =
  let stmt = get_hyp_or_lemma h in
  let args = List.map get_some_hyp args in
  let () = List.iter (Option.map_default ensure_no_restrictions ()) args in
  let ws = type_apply_withs stmt ws in
  let result, obligations = Tactics.apply_with stmt args ws in
  let remaining_obligations, term_witnesses =
    partition_obligations obligations
  in
  let () = ensure_no_logic_variable (result :: remaining_obligations) in
  let () = List.iter term_witness term_witnesses in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
  let resulting_case = recursive_metaterm_case ~used:sequent.vars ~sr:!sr result in
    begin match resulting_case with
      | None -> add_subgoals obligation_subgoals
      | Some case ->
          let resulting_subgoal =
            let restore = goal_to_subgoal sequent.goal in
              fun () ->
                restore () ;
                List.iter add_if_new_var case.stateless_new_vars ;
                List.iter (add_hyp ?name) case.stateless_new_hyps
          in
            add_subgoals ~mainline:resulting_subgoal obligation_subgoals
    end ;
    next_subgoal ()

(* Bachchain *)

let type_backchain_withs stmt ws =
  let bindings = toplevel_bindings stmt in
  let nctx = List.map term_to_pair (metaterm_support sequent.goal) in
    List.map
      (fun (id, t) ->
         try
           let ty = List.assoc id bindings in
             (id, type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign ~ctx:(nctx @ sequent.vars) t)
         with
           | Not_found -> failwith ("Unknown variable " ^ id ^ "."))
      ws

let backchain ?(term_witness=ignore) h ws =
  let stmt = get_hyp_or_lemma h in
  let ws = type_backchain_withs stmt ws in
  let obligations = Tactics.backchain_with stmt ws sequent.goal in
  let remaining_obligations, term_witnesses =
    partition_obligations obligations
  in
  let () = ensure_no_logic_variable remaining_obligations in
  let () = List.iter term_witness term_witnesses in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
    add_subgoals obligation_subgoals ;
    next_subgoal ()

(* Induction *)

let get_restriction r =
  match r with
    | Smaller n -> n
    | CoSmaller n -> n
    | Equal n -> n
    | CoEqual n -> n
    | Irrelevant -> 0

let get_max_restriction t =
  let rec aux t =
    match t with
      | True | False | Eq _ -> 0
      | Obj(_, r) -> get_restriction r
      | Arrow(a, b) -> max (aux a) (aux b)
      | Binding(_, _, body) -> aux body
      | Or(a, b) -> max (aux a) (aux b)
      | And(a, b) -> max (aux a) (aux b)
      | Pred(_, r) -> get_restriction r
  in
    aux t

let next_restriction () =
  1 + (sequent.hyps |> List.map (fun h -> h.term) |>
           List.map get_max_restriction |> List.max)

let rec nth_product n term =
  match term with
    | Binding(Forall, _, body) -> nth_product n body
    | Binding(Nabla, _, body) -> nth_product n body
    | Arrow(left, right) ->
        if n = 1 then
          left
        else
          nth_product (n-1) right
    | _ -> failwith "Can only induct on predicates and judgments"

let ensure_is_inductive term =
  match term with
    | Obj _ -> ()
    | Pred(p, _) ->
        let pname = term_head_name p in
          begin try
            match H.find defs_table pname with
              | Inductive, _, _ -> ()
              | CoInductive, _, _ -> failwith
                  (sprintf "Cannot induct on %s since it has\
                          \ been coinductively defined" pname)
          with Not_found ->
            failwith (sprintf "Cannot induct on %s since it has\
                             \ not been defined" pname)
          end
    | _ -> failwith "Can only induct on predicates and judgments"

let add_ih h =
  add_hyp ~name:(fresh_hyp_name "IH") h

let induction ?name ind_args =
  if has_coinductive_restriction sequent.goal then
    failwith "Induction within coinduction is not allowed" ;
  List.iter
    (fun (arg, goal) -> ensure_is_inductive (nth_product arg goal))
    (List.combine ind_args (and_to_list sequent.goal)) ;
  let res_num = next_restriction () in
    let (ihs, new_goal) = Tactics.induction ind_args res_num sequent.goal in
    let name = match name with
      | None -> fresh_hyp_name "IH"
      | Some name -> name
    in
      List.iter (add_hyp ~name) ihs ;
      sequent.goal <- new_goal


(* CoInduction *)

let rec conclusion term =
  match term with
    | Binding(Forall, _, body) -> conclusion body
    | Binding(Nabla, _, body) -> conclusion body
    | Arrow(left, right) -> conclusion right
    | Pred(p, _) -> p
    | _ -> failwith "Cannot coinduct on a goal of this form"

let ensure_is_coinductive p =
  let pname = term_head_name p in
    try
      match H.find defs_table pname with
        | CoInductive, _, _ -> ()
        | Inductive, _, _ -> failwith
            (sprintf "Cannot coinduct on %s since it has\
                    \ been inductively defined" pname)
    with Not_found ->
      failwith (sprintf "Cannot coinduct on %s since it has\
                       \ not been defined" pname)

let coinduction ?name () =
  ensure_is_coinductive (conclusion sequent.goal) ;
  if has_inductive_restriction sequent.goal then
    failwith "Coinduction within induction is not allowed" ;
  let res_num = next_restriction () in
  let (ch, new_goal) = Tactics.coinduction res_num sequent.goal in
  let name = match name with
    | None -> fresh_hyp_name "CH"
    | Some name -> name
  in
    add_hyp ~name ch ;
    sequent.goal <- new_goal



(* Object logic monotone *)

let monotone h t =
  let ht = get_hyp h in
    match ht with
      | Obj(Async obj, r) ->
          let obj_context, obj_term = Async.get obj in
          let ntids = metaterm_nominal_tids ht in
          let ctx = sequent.vars @
            (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
          in
          let t = type_uterm ~expected_ty:olistty ~sr:!sr ~sign:!sign ~ctx t in
          let new_obj = Async.obj (Context.normalize [t]) obj_term in
            delay_mainline
              (Obj(Async new_obj, r))
              (Binding(Forall, [("X", oty)],
                       Arrow(member (Term.const "X" oty)
                               (Context.context_to_term obj_context),
                             member (Term.const "X" oty)
                               t))) ;
      | _ -> failwith
          "Monotone can only be used on hypotheses of the form {...}"


(* Theorem *)

let theorem thm =
  sequent.goal <- thm


(* Introduction of forall variables *)

let intros hs =
  let rec aux hs term =
    match term with
      | Binding(Forall, bindings, body) ->
          let support = metaterm_support body in
          let (alist, vars) =
            fresh_raised_alist ~sr:!sr ~tag:Eigen ~used:sequent.vars
              ~support bindings
          in
            List.iter add_var (List.map term_to_pair vars) ;
              aux hs (replace_metaterm_vars alist body)
      | Binding(Nabla, bindings, body) ->
          let (ids, tys) = List.split bindings in
            aux hs (replace_metaterm_vars
                      (List.combine ids (fresh_nominals tys body))
                      body)
      | Arrow(left, right) -> begin
          let (name, hs) = match hs with
            | [] -> (None, [])
            | "_" :: hs -> (None, hs)
            | h :: hs -> (Some h, hs)
          in
          add_hyp ?name (normalize left) ;
          aux hs right
        end
      | _ -> term
  in
    sequent.goal <- aux hs sequent.goal

(* Split *)

let split ?name propogate_result =
  let rec accum_goals conjs prev =
    match conjs with
      | [] -> []
      | g::rest ->
          let saved = goal_to_subgoal g in
          let subgoal () =
            saved () ;
            if propogate_result then
              List.iter (add_hyp ?name) (List.rev prev)
          in
            subgoal :: (accum_goals rest (g :: prev))
  in
  let conjs = and_to_list sequent.goal in
    if List.length conjs = 1 then failwith "Needless use of split" ;
    add_subgoals (accum_goals (and_to_list sequent.goal) []) ;
    next_subgoal ()

(* Split theorem *)

let decompose_forall_nabla t =
  match t with
    | Binding(Forall, foralls, Binding(Nabla, nablas, body)) ->
        (foralls, nablas, body)
    | Binding(Forall, foralls, body) ->
        (foralls, [], body)
    | Binding(Nabla, nablas, body) ->
        ([], nablas, body)
    | _ ->
        ([], [], t)

let rec multiarrow arrows body =
  let rec aux = function
    | h::hs -> Arrow(h, aux hs)
    | [] -> body
  in
    aux arrows

let ensure_no_renaming vars terms =
  let conflicts =
    List.intersect
      vars
      (List.map fst (all_tids (List.flatten_map collect_terms terms)))
  in
    if conflicts <> [] then
      failwith "Variable renaming required"

let split_theorem thm =
  let foralls, nablas, body = decompose_forall_nabla thm in
  let arrows, conj = decompose_arrow body in
  let nabla_consts = List.map (fun (x, ty) -> const x ty) nablas in
  let lift t =
    let iforalls, inablas, ibody = decompose_forall_nabla t in
      (* Raise iforalls over nablas *)
    let alist, iforall_vars =
      fresh_raised_alist ~used:[] ~sr:!sr ~tag:Constant
        ~support:nabla_consts iforalls
    in
    let iforalls = List.map (fun x -> (term_to_name x, tc [] x)) iforall_vars in
    let ibody = replace_metaterm_vars alist ibody in
      ensure_no_renaming (List.map fst (iforalls @ inablas)) arrows ;
      forall (foralls @ iforalls)
        (nabla (nablas @ inablas)
           (multiarrow arrows ibody))
  in
    List.map lift (and_to_list conj)

let create_split_theorems name names =
  let thms = split_theorem (get_lemma name) in
  let rec loop = function
    | n::ns, t::ts, count ->
        (n, t) :: (loop (ns, ts, count+1))
    | [], t::ts, count ->
        (name ^ (string_of_int count), t) :: (loop ([], ts, count+1))
    | _ -> []
  in
    if List.length thms = 1 then
      failwith "Cannot split this type of theorem" ;
    loop (names, thms, 1)

(* Left and right side of disjunction *)

let left () =
  match sequent.goal with
    | Or(left, _) -> sequent.goal <- left
    | _ -> ()

let right () =
  match sequent.goal with
    | Or(_, right) -> sequent.goal <- right
    | _ -> ()


(* Unfold *)

let unfold () =
  let mdefs = get_defs sequent.goal in
  let goal = unfold ~mdefs sequent.goal in
  let goals = and_to_list goal in
    add_subgoals (List.map goal_to_subgoal goals) ;
    next_subgoal ()

(* Exists *)

let exists t =
  match sequent.goal with
    | Binding(Metaterm.Exists, (id, ty)::tids, body) ->
        let ntids = metaterm_nominal_tids body in
        let ctx = sequent.vars @
          (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
        in
        let t = type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign ~ctx t in
        let goal = exists tids (replace_metaterm_vars [(id, t)] body) in
          sequent.goal <- goal
    | _ -> ()

(* Skip *)

let skip () =
  next_subgoal ()

(* Clear *)

let clear hs =
  List.iter remove_hyp hs

(* Abbrev *)

let abbrev id str =
  List.iter (fun h -> if h.id = id then h.abbrev <- Some str) sequent.hyps

let unabbrev ids =
  List.iter (fun h -> if List.mem h.id ids then h.abbrev <- None) sequent.hyps

(* Rename *)

let rename hfr hto =
  try begin
    ignore (get_hyp_or_lemma hto) ;
    failwith (sprintf "%S already refers to a hypothesis or lemma" hto)
  end with Not_found ->
    let hyps = List.map begin
      fun h ->
        if h.id = hfr then
          { h with id = hto }
        else h
    end sequent.hyps in
    sequent.hyps <- hyps

(* Permute *)

let permute_nominals ids form =
  if not (List.is_unique ids) then failwith "Not a permutation" ;
  let term =
    match form with
      | None -> sequent.goal
      | Some h -> get_hyp h
  in
  let support_alist =
    List.map (fun t -> (term_to_name t, t)) (metaterm_support term)
  in
  let perm =
    List.map
      (fun id ->
         try
           List.assoc id support_alist
         with Not_found -> nominal_var id (tybase ""))
      ids
  in
  let result = Tactics.permute_nominals perm term in
    match form with
      | None -> sequent.goal <- result
      | Some hyp -> replace_hyp hyp result

(* Object level cut with explicit cut formula*)

let cut_from ?name h arg term =
  let term = type_uterm ~sr:!sr ~sign:!sign ~ctx:sequent.vars term in
  let h = get_hyp h in
  let arg = get_hyp arg in
    match h, arg with
      | Obj(obj_h1, _),Obj(obj_h2, _) ->
          add_hyp ?name (object_cut_from obj_h1 obj_h2 term)
      | _,_ -> failwith "Cut can only be used on hypotheses of the form {...}"
