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
open Prover
open Abella_types
open Typing
open Extensions
open Printf
open Debug
open Accumulate
open Schema

let can_read_specification = ref true

let interactive = ref true
let out = ref stdout
let compile_out = ref None

let switch_to_interactive = ref false
let lexbuf = ref (Lexing.from_channel stdin)

let annotate = ref false
let count = ref 0

let witnesses = ref false

exception AbortProof

(* Input *)

let perform_switch_to_interactive () =
  assert !switch_to_interactive ;
  switch_to_interactive := false ;
  lexbuf := Lexing.from_channel stdin ;
  interactive := true ;
  out := stdout ;
  fprintf !out "Switching to interactive mode.\n%!"

let interactive_or_exit () =
  if not !interactive then
    if !switch_to_interactive then
      perform_switch_to_interactive ()
    else
      exit 1


let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
    if file = "" then
      ""
    else
      sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

let type_inference_error (pos, ct) exp act =
  eprintf "Typing error%s.\n%!" (position_range pos) ;
  match ct with
    | CArg ->
        eprintf "Expression has type %s but is used here with type %s\n%!"
          (ty_to_string act) (ty_to_string exp)
    | CFun ->
        eprintf "Expression is applied to too many arguments\n%!"

let teyjus_only_keywords =
  ["closed"; "exportdef"; "import"; "infix"; "infixl"; "infixr"; "local";
   "localkind"; "postfix"; "posfixl"; "prefix"; "prefixr"; "typeabbrev";
   "use_sig"; "useonly"; "sigma"]

let warn_on_teyjus_only_keywords (ktable, ctable) =
  let tokens = List.unique (ktable @ List.map fst ctable) in
  let used_keywords = List.intersect tokens teyjus_only_keywords in
    if used_keywords <> [] then
      fprintf !out
        "Warning: The following tokens are keywords in Teyjus: %s\n%!"
        (String.concat ", " used_keywords)

let update_subordination_sign sr sign =
  List.fold_left Subordination.update sr (sign_to_tys sign)

let read_specification name =
  clear_specification_cache () ;
  fprintf !out "Reading specification %S%s\n%!" name
    (if !load_path <> "." then
       sprintf " (from %S)" !load_path
     else "") ;
  let read_sign = get_sign name in
  let () = warn_on_teyjus_only_keywords read_sign in
  let sign' = merge_signs [!sign; read_sign] in
  let sr' = update_subordination_sign !sr read_sign in
  let clauses' = get_clauses ~sr:sr' name in
    (* Any exceptions must have been thrown by now - do actual assignments *)
    sr := sr' ;
    sign := sign' ;
    add_clauses clauses'

(* Checks *)

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwith "Cannot use restrictions: *, @ or +"

let untyped_ensure_no_restrictions term =
  ensure_no_restrictions (umetaterm_to_metaterm [] term)

let warn_stratify names term =
  let rec aux nested term =
    match term with
      | Pred(p, _) when nested && List.mem (term_head_name p) names -> true
      | Arrow(left, right) -> aux true left || aux nested right
      | Binding(_, _, body) -> aux nested body
      | Or(left, right) -> aux nested left || aux nested right
      | And(left, right) -> aux nested left || aux nested right
      | _ -> false
  in
    if aux false term then
      fprintf !out "Warning: Definition might not be stratified\n%!"

let check_theorem thm =
  ensure_no_restrictions thm

let ensure_not_capital name =
  if is_capital_name name then
    failwith (sprintf "Defined predicates may not begin with \
                       a capital letter.")

let ensure_name_contained id ids =
  if not (List.mem id ids) then
    failwith ("Found stray clause for " ^ id)

let ensure_wellformed_head t =
  match t with
    | Pred _ -> ()
    | Binding(Nabla, _, Pred _) -> ()
    | _ -> failwith
        (sprintf "Bad head in definition: %s" (metaterm_to_string t))

let check_defs names defs =
  List.iter ensure_not_capital names ;
  List.iter
    (fun (head, body) ->
       ensure_wellformed_head head ;
       ensure_name_contained (def_head_name head) names ;
       ensure_no_restrictions head ;
       ensure_no_restrictions body ;
       warn_stratify names body)
    defs

let check_noredef ids =
  let (_, ctable) = !sign in
    List.iter (
      fun id -> if List.mem id (List.map fst ctable) then
        failwith (sprintf "%s is already defined" id)
    ) ids

(* Compilation and importing *)

let comp_spec_sign = ref ([], [])
let comp_spec_clauses = ref []
let comp_content = ref []

let marshal citem =
  match !compile_out with
    | Some cout -> Marshal.to_channel cout citem []
    | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    comp_spec_sign := !sign ;
    comp_spec_clauses := !clauses
  end

let compile citem =
  ensure_finalized_specification () ;
  comp_content := citem :: !comp_content

let predicates (ktable, ctable) =
  List.map fst (List.find_all (fun (_, Poly(_, Ty(_, ty))) -> ty = "o") ctable)

let write_compilation () =
  marshal !comp_spec_sign ;
  marshal !comp_spec_clauses ;
  marshal (predicates !sign) ;
  marshal (List.rev !comp_content)

let clause_eq c1 c2 = eq c1 c2

let clauses_to_predicates clauses =
  let clause_heads =
    List.map (fun c -> let (_,h,_) = clausify c in h) clauses in
  List.unique (List.map term_head_name clause_heads)

let ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates =
  let (ktable, ctable) = !sign in
  let (imp_ktable, imp_ctable) = imp_spec_sign in

  (* 1. Imported ktable must be a subset of ktable *)
  let missing_types = List.minus imp_ktable ktable in
  let () = if missing_types <> [] then
    failwith (sprintf "Imported file makes reference to unknown types: %s"
                (String.concat ", " missing_types))
  in

  (* 2. Imported ctable must be a subset of ctable *)
  let missing_consts = List.minus imp_ctable ctable in
  let () = if missing_consts <> [] then
    failwith (sprintf "Imported file makes reference to unknown constants: %s"
                (String.concat ", " (List.map fst missing_consts)))
  in

  (* 3. Imported clauses must be a subset of clauses *)
  let missing_clauses =
    List.minus ~cmp:clause_eq imp_spec_clauses !clauses
  in
  let () = if missing_clauses <> [] then
    failwith (sprintf "Imported file makes reference to unknown clauses for: %s"
                (String.concat ", " (clauses_to_predicates missing_clauses)))
  in

  (* 4. Clauses for imported predicates must be subset of imported clauses *)
  let extended_clauses =
    List.minus ~cmp:clause_eq
      (List.find_all
         (fun clause ->
           let (_,clause_head,_) = clausify clause in
           List.mem (term_head_name clause_head) imp_predicates)
         !clauses)
      imp_spec_clauses
  in
  let () = if extended_clauses <> [] then
    failwith (sprintf "Cannot import file since clauses have been extended for: %s"
                (String.concat ", " (clauses_to_predicates extended_clauses)))
  in

    ()


let imported = ref []

let import filename =
  let rec aux filename =
    if not (List.mem filename !imported) then begin
      imported := filename :: !imported ;
      let file = open_in_bin (filename ^ ".thc") in
      let imp_spec_sign = (Marshal.from_channel file : sign) in
      let imp_spec_clauses = (Marshal.from_channel file : clauses) in
      let imp_predicates = (Marshal.from_channel file : string list) in
      let imp_content = (Marshal.from_channel file : compiled list) in
        ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates ;
        List.iter
          (function
             | CTheorem(name, thm) ->
                 add_lemma name thm ;
             | CDefine(idtys, defs) ->
                 let ids = List.map fst idtys in
                   check_noredef ids;
                   check_defs ids defs ;
                   add_global_consts idtys ;
                   add_defs ids Inductive defs ;
             | CCoDefine(idtys, defs) ->
                 let ids = List.map fst idtys in
                   check_noredef ids;
                   check_defs ids defs ;
                   add_global_consts idtys ;
                   add_defs ids CoInductive defs
             | CImport(filename) ->
                 aux filename
             | CKind(ids) ->
                 check_noredef ids;
                 add_global_types ids
             | CType(ids, ty) ->
                 check_noredef ids;
                 add_global_consts (List.map (fun id -> (id, ty)) ids)
             | CClose(ty_subords) ->
                 List.iter
                   (fun (ty, prev) ->
                      let curr = Subordination.subordinates !sr ty in
                        match List.minus curr prev with
                          | [] -> ()
                          | xs ->
                              failwith
                                (Printf.sprintf
                                   "Cannot close %s since it is now subordinate to %s"
                                   ty (String.concat ", " xs)))
                   ty_subords ;
                 close_types (List.map fst ty_subords))
          imp_content
    end
  in
    if List.mem filename !imported then
      fprintf !out "Ignoring import: %s has already been imported.\n%!" filename
    else begin
      fprintf !out "Importing from %s\n%!" filename ;
      aux filename
    end


(* Proof processing *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv, q)) with
    | Binding(Metaterm.Exists, fv, q) ->
        let ctx = fresh_alist ~tag:Logic ~used:[] fv in
        let q = replace_metaterm_vars ctx q in
        let _ = Tactics.search
          ~depth:max_int
          ~hyps:[]
          ~clauses:!clauses
          ~alldefs:(defs_table_to_list ())
          ~sc:(fun w ->
                 fprintf !out "Found solution:\n" ;
                 List.iter
                   (fun (n, v) ->
                      fprintf !out "%s = %s\n" n (term_to_string v))
                   ctx ;
                 fprintf !out "\n%!")
          q
        in
          fprintf !out "No more solutions.\n%!"
    | _ -> assert false

let set k v =
  match k, v with
    | "subgoals", Int d when d >= 0 -> subgoal_depth := d
    | "subgoals", Str "on" -> subgoal_depth := 1000
    | "subgoals", Str "off" -> subgoal_depth := 0
    | "subgoals", _ ->
        failwith ("Unknown value '" ^ (set_value_to_string v) ^
                    "' for key 'subgoals'." ^
                    " Expected 'on', 'off', or non-negative integer.")

    | "debug", Str "on" -> debug_level := 1
    | "debug", Str "off" -> debug_level := 0
    | "debug", _ ->
        failwith ("Unknown value '" ^ (set_value_to_string v) ^
                    "' for key 'debug'." ^
                    " Expected 'on' or 'off'.")

    | "search_depth", Int d when d >= 0 -> search_depth := d
    | "search_depth", _ ->
        failwith ("Unknown value '" ^ (set_value_to_string v) ^
                    "' for key 'search_depth'." ^
                    " Expected non-negative integer.")

    | "witnesses", Str "on" -> witnesses := true
    | "witnesses", Str "off" -> witnesses := false
    | "witnesses", _ ->
        failwith ("Unknown value '" ^ (set_value_to_string v) ^
                    "' for key 'witnesses'." ^
                    " Expected 'on' or 'off'.")

    | "load_path", QStr s -> load_path := s

    | _, _ -> failwith ("Unknown key '" ^ k ^ "'.")

let print_theorem name thm =
  fprintf !out "\nTheorem %s : \n%s.\n%!"
    name (metaterm_to_formatted_string thm)

let show name =
  print_theorem name (get_lemma name)

let witness w =
  if !witnesses then
    fprintf !out "Witness: %s\n%!" (Tactics.witness_to_string w)

let term_witness (t, w) =
  if !witnesses then
    fprintf !out "Witness: %s : %s\n%!"
      (Tactics.witness_to_string w)
      (metaterm_to_string t)

let rec process_proof name =
  let suppress_display = ref false in
  let finished = ref false in
    try while not !finished do try
      if !annotate then begin
        fprintf !out "</pre>\n%!" ;
        incr count ;
        fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
        fprintf !out "<pre>\n%!"
      end ;
      if not !suppress_display then
        display !out
      else
        suppress_display := false ;
      fprintf !out "%s < %!" name ;
      let input = Parser.command Lexer.token !lexbuf in
        if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            fprintf !out "%s%s.%s\n%!" pre (command_to_string input) post
        end ;
        save_undo_state () ;
      begin match input with
      | Induction(args, hn) -> induction ?name:hn args
      | CoInduction hn -> coinduction ?name:hn ()
   | Apply(h, args, ws, hn) -> 
  let (h,args) = if not !(Schema.schemaExt) then (h,args) else begin match h with 
   | "inversion" ->
(* inv.1 *) 
       begin match (get_hyp (List.hd args), get_hyp (List.hd (List.tl args))) with
       | Pred ( t, r), Pred (t1, _ ) ->
	   let (schName, gi, _) = member_of_ith t t1 in
(* inv.2 *)let hypName = "Hinv"^schName^(string_of_int gi) in
	   begin try
	     let _ = get_hyp hypName in
	     (hypName, args)
	   with  _ -> 
	     let (arr, bids) = get_schema schName in
(* inv.3 *)  let invThmStr = make_inv_stmt gi schName arr bids  in
	     let invPrfStr = make_inv_prf (List.length bids) in
	     let aStr = hypName^": assert "^invThmStr^invPrfStr in
	     recursePPOn aStr;
	     (hypName, args)
	   end
       | _,_ -> failwith "unexpected in inversion" 
       end
  | "sync" -> 
(* syn.1 *)
   begin match (get_hyp (List.hd args), get_hyp (List.hd (List.tl args))) with
   | Pred ( t, _), Pred (t1, _ ) ->
   let (schName,gi,st) = member_of_ith t t1 in
   let (arr, bids) = get_schema schName in
(* syn.2 *)
   let githbids = List.map (fun (a,b,c) -> (a,b, List.nth c (gi-1))) bids in 
   let bnames = List.map (fun (a,b,(c,d,e)) -> (c,d,e)) githbids in
   let mts = List.map get_block_sub bnames in
   let ads = instOfPats st mts in
(* syn.3 *)
   let adsHashl = List.map (fun (b,_) -> if b then "1" else "0") ads in
   let hypName = "Hsync"^schName^(string_of_int gi)^(String.concat "" adsHashl) in
   begin try
     let _ = get_hyp hypName in
     (hypName, args)
   with  _ -> 
(* syn.4 *)
   let vvts = List.filter (fun (cmts, (b,_)) -> b) (List.combine mts ads) in
   if vvts = [] then failwith (sprintf "Schema: in sync, no clauses of %s can introduce a formula of the form %s. \n" schName (term_to_string st));
   let (pmts,pads) = List.split vvts in
   let tlup = List.map (fun (eb,nb,ut) -> 
		    let abt = List.map (fun (name,typ) -> (name,Term.(var Logic name (max_int-1) typ))) (List.append eb nb) in
		    type_uterm ~sr:!sr ~sign:!sign ~ctx:abt ut) pmts in
   List.iter (Unify.left_unify (List.hd tlup)) (List.tl tlup);
   let ads = instOfPats (List.hd tlup) mts in
(* syn.5 *)
   let syncThmStr = make_sync_stmt gi schName arr bids ads (List.hd tlup) in
   let syncPrfStr = make_sync_prf ads in 
   let aStr = hypName^" : assert "^syncThmStr^syncPrfStr in
   recursePPOn  aStr; (hypName, args) end
   | _ , _ -> failwith " unexpected in sync" end 
  |  "unique" ->
(* uni.1 *)      let (h0,h1,h2) = ( try (get_hyp (List.nth args 0), 
					 get_hyp (List.nth args 1),
					 get_hyp (List.nth args 2))
with _ -> failwith "Schema: 3 arguments expected for 'unique' tactical" ) in
             begin match (h0,h1,h2) with
	     | Pred(t,_),Pred(t1,_),Pred(t2,_) ->
	 let (schName , gi ,te1) = (member_of_ith t t1) in
	 let (schName', gi',te2) = (member_of_ith t t2) in
	 (if  (gi <> gi' || schName <> schName') then failwith "Schema: membership hypothesis should come from the same projection of the context in 'unique' tactical" else ());
		  let (arr,bids) = get_schema schName in
		  let bids = List.map (fun (a,b,c) -> (a,b, List.nth c (gi-1))) bids in
		  let bnames = List.map (fun (a,b,(c,d,e)) -> (c,d,e)) bids in
		  let mts = List.map get_block_sub bnames in

(* uni.2 *)       let varl = pairwiseEqual te1 te2 in

(* uni.3 *)       Unify.left_unify te1 te2; 

(* uni.4 *)       let ads = instOfPats te1 mts in
(* uni.5 *)       let (groundVar, rel) = safeUniqueGrounds mts ads varl in
(* uni.6 *)       let adsHashl = List.map (fun (b,_) -> if b then "1" else "0") ads in
                  let hypName = "Huni"^schName^(string_of_int gi)^(List.hd rel)^(String.concat "" adsHashl) in
         	  begin try
                     let _ = get_hyp hypName in
		     (hypName, args)
                  with  _ -> 
(* uni.7 *)       let vvts = List.filter (fun (cmts, (b,_)) -> b) (List.combine mts ads) in
                  let (pmts,pads) = List.split vvts in


		  let utlup = List.map (fun ((eb,nb,ut),oldid) -> 
		    let gvSwap = ((groundVar,oldid)::[(oldid,groundVar)]) in
		    ((rename_ids_in_idtys gvSwap (List.append eb nb)), (rename_ids_in_uterm gvSwap ut))) (List.combine pmts rel) in
		  let tlup = List.map (fun (ab,ut) -> 
		    let abt = List.map (fun (name,typ) -> (name,Term.(var Logic name (max_int-1) typ))) ab in
		    type_uterm ~sr:!sr ~sign:!sign ~ctx:abt ut) utlup in
		  List.iter (Unify.left_unify (List.hd tlup)) (List.tl tlup);
(* uni.8 *)      let (nl,tu1,tu2) = uniteTerms (List.hd tlup) (List.hd tlup) 0 groundVar in
		  let (bads,_) = List.split ads in
		  let uniThmStr = make_uni_stmt schName tu1 tu2 nl arr gi groundVar in
                  let uniPrfStr = make_uni_prf schName mts bads in
		  let aStr = hypName^" : assert "^uniThmStr^uniPrfStr in
		  recursePPOn aStr; (hypName,args) end
	     | _ -> failwith "Schema: arguments in the wrong form for 'unique' tactical"
	     end
  |  "projas" -> 
(* pro.1 *)  
(*        ((if List.length hl < 3 then failwith "Schema: Not enough argument for projas"); *)
	let schNameD = List.hd (List.tl args) in
	let schDs = List.tl (List.tl args) in
	(begin match (get_hyp (List.hd args)) with 
	| Pred (t,_) -> 
	    (begin match observe t with
	    | App(schNameT,schGsTl) ->
	       let schNameO = term_to_string schNameT in
	       let schOs = List.map get_head_id schGsTl in
	       (if (List.mem_assoc schNameO Prover.(!schemas)) then
		 if (List.mem_assoc schNameD Prover.(!schemas)) then
		   ()
		 else failwith ("Schema: "^schNameD^" is not a declared schema.")
	       else failwith ("Schema: "^schNameO^" is not a declared schema."));
	       let (arrD,bidsD) = get_schema schNameD in
	       let (arrO,bidsO) = get_schema schNameO in
	       (if (List.length schOs) = arrO then 
		 if (List.length schDs) = arrD then 
		   ()
		 else failwith (sprintf "Schema: %d arguments expected for schema %s." arrD schNameD)
	       else failwith (sprintf "Schema: %d arguments expected for schema %s." arrO schNameO));
(* pro.2 *)    let odPerm = List.map (fun id -> 
                                    try 
				      string_of_int (mem_pos id schDs)
				    with _ -> "0") schOs in
	       let hypName = "Hpro"^schNameO^(String.concat "" odPerm)^schNameD in
	       begin try 
		 let _ = get_hyp hypName in
		 (hypName, [List.hd args])
	       with _ ->
(* pro.3 *)    let (_,_,blsO) = split3 bidsO in
               let btmsO = type_clauses blsO in
	       let clConsO = proClConst schOs btmsO in
               let (_,_,blsD) = split3 bidsD in
               let btmsD = type_clauses blsD in
                checkProMatches clConsO schDs btmsD;   
(* pro.4 *)    let projThmStr =  make_proj_stmt schNameO schOs schNameD schDs in
	       let projPrfStr =  make_proj_prf (List.length bidsO) in
	       let aStr =  hypName^" : assert "^projThmStr^projPrfStr in
	       recursePPOn aStr; (hypName, [List.hd args])
	       end
	    | _ -> failwith "Schema: Unexpected in projas (1)" 
	    end)
	| _ -> failwith "Schema: Unexpected in projas (2)"
	end)
  |   _ ->
      (h,args)
  end in
     apply ?name:hn h args ws ~term_witness;
      | Backchain(h, ws) -> backchain h ws ~term_witness
      | Cut(h, arg, hn) -> cut ?name:hn h arg
          | CutFrom(h, arg, t, hn) -> cut_from ?name:hn h arg t
          | SearchCut(h, hn) -> search_cut ?name:hn h
          | Inst(h, ws, hn) -> inst ?name:hn h ws
          | Case(str, keep, hn) -> case ?name:hn ~keep str
          | Assert(t, hn) ->
              untyped_ensure_no_restrictions t ;
              assert_hyp ?name:hn t
          | Exists(t) -> exists t
          | Monotone(h, t) -> monotone h t
          | Clear(hs) -> clear hs
          | Abbrev(h, s) -> abbrev h s
          | Unabbrev(hs) -> unabbrev hs
          | Rename(hfr, hto) -> rename hfr hto
          | Search(limit) ->
              search ~limit ~interactive:!interactive ~witness ()
          | Permute(ids, h) -> permute_nominals ids h
          | Split -> split false
          | SplitStar -> split true
          | Left -> left ()
          | Right -> right ()
          | Unfold -> unfold ()
          | Intros hs -> intros hs
          | Skip -> skip ()
          | Abort -> raise AbortProof
          | Undo -> undo () ; undo () (* undo recent save, and previous save *)
          | Common(Set(k, v)) -> set k v
          | Common(Show(n)) ->
              undo () ; (* Do not save an undo point here *)
              show n ;
              fprintf !out "\n%!" ;
              suppress_display := true
          | Common(Quit) -> raise End_of_file
      end ;
        if !interactive then flush stdout ;
    with
      | Failure "lexing: empty token" ->
          exit (if !interactive then 0 else 1)
      | Failure "Proof completed." ->
          fprintf !out "Proof completed.\n%!" ;
          reset_prover () ;
          finished := true
      | Failure s ->
          eprintf "Error: %s\n%!" s ;
          interactive_or_exit ()
      | End_of_file ->
          if !switch_to_interactive then
            perform_switch_to_interactive ()
          else begin
            fprintf !out "Proof NOT completed.\n%!" ;
            failwith "eof"
          end
      | AbortProof ->
          fprintf !out "Proof aborted.\n%!" ;
          reset_prover () ;
          raise AbortProof
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
          Lexing.flush_input !lexbuf ;
          interactive_or_exit () ;
      | TypeInferenceFailure(ci, exp, act) ->
          type_inference_error ci exp act ;
          interactive_or_exit ()
      | e ->
          eprintf "Error: %s\n%!" (Printexc.to_string e) ;
          interactive_or_exit ()
    done with
      | Failure "eof" -> ()
(* schema ext *)
and recursePPOn ?quiet:(q=true) aStr = 
  if aStr = "" then () else 
  if not q then printf "/* %s */" aStr;
   let holdout = ref !out in
   let holdbuf = ref !lexbuf in
   lexbuf := Lexing.from_string aStr;
   if q then out := open_out "/dev/null";
   begin try 
   process_proof "";
   out := !holdout;
   lexbuf := !holdbuf;
   ()
   with AbortProof ->
     out := !holdout; lexbuf := !holdbuf; failwith  (sprintf "error while recursePPOn %s" aStr)
   |  e -> out := !holdout; lexbuf := !holdbuf; printf "Error while recursePPOn %s \n" aStr; raise e  end


let rec process () =
  try while true do try
    if !annotate then begin
      incr count ;
      fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
      fprintf !out "<pre class=\"code\">\n%!"
    end ;
    fprintf !out "Abella < %!" ;
    let input = Parser.top_command Lexer.token !lexbuf in
      if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in 
	    fprintf !out "%s%s.%s\n%!" pre (top_command_to_string input) post 
      end ;
      begin match input with
        | Theorem(name, thm) ->
            let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
              check_theorem thm ;
              theorem thm ;
              begin try
                process_proof name ;
                compile (CTheorem(name, thm)) ;
                add_lemma name thm ;
              with AbortProof -> () end
        | SSplit(name, names) ->
            let thms = create_split_theorems name names in
              List.iter
                (fun (n, t) ->
                   print_theorem n t ;
                   add_lemma n t ;
                   compile (CTheorem(n, t)))
                thms ;
        | Define(idtys, udefs) ->
            let ids = List.map fst idtys in
              check_noredef ids;
              let (local_sr, local_sign) = locally_add_global_consts idtys in
              let defs = type_udefs ~sr:local_sr ~sign:local_sign udefs in
                check_defs ids defs ;
                commit_global_consts local_sr local_sign ;
                compile (CDefine(idtys, defs)) ;
                add_defs ids Inductive defs
        | Block (id,(ids1,ids2,ut)) ->  
               check_noredef [id];
	    let idtys = type_vars_in (uterm_to_term [] ut) (Ty( [], "o")) sign in
	    let idtys = rem_rep_pairs idtys in
	    let tys1 = List.map (fun id -> List.assoc id idtys) ids1 in
	    let tys2 = List.map (fun id -> List.assoc id idtys) ids2 in
	    let proofStr = makeBlockGeneric tys1 tys2 in
	    add_block id (List.combine ids1 tys1,List.combine ids2 tys2,ut);
	      recursePOn proofStr
	| Schema (id,bids) -> 
    (* check that the name is fresh, *)
            check_noredef [id];
(* that for each block, the applied variables are bound from the proper quantifier, *)
	    let _ = List.map (fun (a,b,l) -> 
	      (List.map (fun (c,d,e) -> if (List.fold_left (fun r -> fun var -> r && List.mem var a) true c)  && (List.fold_left (fun r -> fun var -> r && List.mem var b) true d)  then () else failwith (sprintf "Free variable(s) in the declaration of %s" id)) l)) bids in
(* that the arriety of the schema is the same for every clause (save the result), *)
	    let arr = (fun (a,b,l) -> List.length l) (List.hd bids) in
	    let _ = List.map (fun (a,b,l) -> if arr = (List.length l) then () else failwith (sprintf "All clauses should have the same arrity (%d) in the declaration of %s" arr id)) bids in
	    (*and that  nabla bound variables are used at most once in every block. *)
	    let _ = List.map (fun (a,b,l) ->
	      (List.map (fun (c,d,e) -> if List.is_unique d then () else failwith (sprintf "Nabla bound variable should be used linearly in the declaration of %s" id)) l)) bids in
	    add_schema id (arr, bids);
	    let schTy = (str_repeat arr " olist ->")^" prop" in
	    let blids = List.map (fun (a,b,l) -> l) bids in 
	    let clstrl = List.map (fun e ->
		 List.fold_left (fun (i,defl,defr) -> fun  (idtys1 ,idtys2 , utm) -> (i+1,defl^" (("^(uterm_to_string utm)^") :: G"^(string_of_int i)^")", defr^" G"^(string_of_int i))) (1, id, id) (List.map get_block_sub e)) blids in
	    let cdef = begin match List.length blids with
	    |  0 -> "Define "^id^":"^schTy^" by \n"^id^(str_repeat arr " nil")^"."
	    |  _ -> "Define "^id^":"^schTy^" by \n"^id^(str_repeat arr " nil")^";\n"^(String.concat ";\n" (List.map (fun ((_,b,_),(_,d,e)) -> 
	      if b = [] then 
	      sprintf "%s := %s "  d e
		else 
	      sprintf "nabla %s , %s := %s" (String.concat " " b) d e) (List.combine bids clstrl)))^"." end in
	    recursePOn cdef
        | CoDefine(idtys, udefs) ->
            let ids = List.map fst idtys in
              check_noredef ids;
              let (local_sr, local_sign) = locally_add_global_consts idtys in
              let defs = type_udefs ~sr:local_sr ~sign:local_sign udefs in
                check_defs ids defs ;
                commit_global_consts local_sr local_sign ;
                compile (CCoDefine(idtys, defs)) ;
                add_defs ids CoInductive defs
        | TopCommon(Set(k, v)) ->
            set k v
        | TopCommon(Show(n)) ->
            show n
        | TopCommon(Quit) ->
            raise End_of_file
        | Import(filename) ->
            compile (CImport filename) ;
            import filename ;
        | Specification(filename) ->
            if !can_read_specification then begin
              read_specification filename ;
              ensure_finalized_specification ()
            end else
              failwith ("Specification can only be read " ^
                          "at the begining of a development.")
        | Query(q) -> query q
        | Kind(ids) ->
            check_noredef ids;
            add_global_types ids ;
            compile (CKind ids)
        | Type(ids, ty) ->
            check_noredef ids;
            add_global_consts (List.map (fun id -> (id, ty)) ids) ;
            compile (CType(ids, ty))
        | Close(ids) ->
            close_types ids ;
            compile
              (CClose(List.map
                        (fun id -> (id, Subordination.subordinates !sr id))
                        ids)) ;
      end ;
      if !interactive then flush stdout ;
      if !annotate then fprintf !out "</pre>%!" ;
      fprintf !out "\n%!" ;
  with
    | Failure "lexing: empty token" ->
        eprintf "Unknown symbol" ;
        exit (if !interactive then 0 else 1)
    | Failure s ->
        eprintf "Error: %s\n%!" s ;
        interactive_or_exit ()
    | End_of_file ->
        if !switch_to_interactive then
          perform_switch_to_interactive ()
        else begin
	  fprintf !out "Goodbye.\n%!" ;
          ensure_finalized_specification () ;
          write_compilation () ;
          if !annotate then fprintf !out "</pre>\n%!" ;
	  failwith "eof"
         (*  exit 0 *)
        end
    | Parsing.Parse_error ->
        eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
        Lexing.flush_input !lexbuf ;
        interactive_or_exit ()
    | TypeInferenceFailure(ci, exp, act) ->
        type_inference_error ci exp act ;
        interactive_or_exit ()
    | e ->
        eprintf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        interactive_or_exit ()
  done with
  | Failure "eof" -> ()
and recursePOn ?quiet:(q=true) aStr = 
  if aStr = "" then () else 
  if not q then printf "/* %s */" aStr;
   let holdout = ref !out in
   let holdbuf = ref !lexbuf in
   lexbuf := Lexing.from_string aStr;
   if q then out := open_out "/dev/null";
   begin try 
   process ();
   out := !holdout;
   lexbuf := !holdbuf;
   ()
   with   e -> out := !holdout; lexbuf := !holdbuf; printf "Error while recursePOn %s \n" aStr; raise e  end 


(* Command line and startup *)

let welcome_msg = sprintf "Welcome to Abella %s\n" Version.version

let usage_message = "abella [options] <theorem-file>"

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out := Some (open_out_bin filename)

let makefile = ref false

let options =
  Arg.align
    [
      ("-i", Arg.Set switch_to_interactive,
       " Switch to interactive mode after reading inputs") ;
      ("-o", Arg.String set_output,
       "<file-name> Output to file") ;
      ("-c", Arg.String set_compile_out,
       "<file-name> Compile definitions and theorems in an importable format") ;
      ("-a", Arg.Set annotate, " Annotate mode") ;
      ("-M", Arg.Set makefile, " Output dependencies in Makefile format")
    ]

let input_files = ref []

let set_input () =
  match !input_files with
    | [] -> ()
    | [filename] ->
        interactive := false ;
        lexbuf := lexbuf_from_file filename
    | fs ->
        eprintf "Error: Multiple files specified as input: %s\n%!"
          (String.concat ", " fs) ;
        exit 1

let add_input filename =
  input_files := !input_files @ [filename]

let _ =
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle (fun _ -> failwith "Interrupted (use ctrl-D to quit)")) ;

  Arg.parse options add_input usage_message ;

  if not !Sys.interactive then
    if !makefile then begin
      List.iter Depend.print_deps !input_files ;
    end else begin
      set_input () ;
      fprintf !out "%s%!" welcome_msg ;
      process ()
    end
;;
