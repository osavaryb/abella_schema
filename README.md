(04/07/2013) 
* doing some test to fix unique, will probably modify the generation so that we unify all matched patterns before generating the statement, as described before. 
> fvInTm is just select_var_refs with f = \x.true, should use it(and List.unique) in patternMatch.
> rem_rep is List.unique
* TODO: move all new code in a different module


(03/07/2013) meetup
TODO
1) unique
2) rewrite bred
3) term redev
4) proj&inj


MEETING
10th regular meeting
12th code walk
17 meetup with dale


REPORT
1 or 2 pages (computer science generalist) summary of research - bilan
RAPT report 

(03/07/2013)
* working on breduce.thm now, to test quantifiers in contexts.
 > inversion works
 > sync works
 > unique need some work, pairwiseEqual assumed a constant followed by vars
? I always use prune ctxvars, might need to deal with nominal deps.
(02/07/2013)
* TODO: revisit how to type the block head, maybe storing term instead of uterm. 
  > Deprecated get_ty_from_tml, using type_vars_in which take a term, its expected type, the ctx signature and a list of locally bound variables, and returns a list of free variables appearing in the term together with their type. 
> Block and schema definition with quantifier now works, will test the tacticals tomorrow.


(01/07/2013)
> Sync works -> proof is quite like unique, if not matched, can skip the head case, o.w. apply I.H. and search.
* TODO: find a way to type and add the new variables from patternMatch in the list of "fresh" variables in make_sync_stmt.
* TODO: Should use Right.unify instead of uniteTerms for sync&unique, on the matched patterns, to make the most general terms matching all the pattern matched by the hypothesis.
* TODO: handle general term in "Block", maybe type them right away and store term instead of uterm.
(26/06/2013) 
* For sync & uniq, if not cases ... , return false. (think about discrim )
* think about getting induction principles from type from sig in abella ($tm &c) (read bpientka's coverage paper)
? Seems like all the tacticals are following the pattern of 1) observing the hypothesis given 2) selecting the statement from a finite set of statement that could've been generated at the schema definition. 
?? See if unique can be expressed as such, using a unified pattern from all matching patterns instead of a unified pattern of the two hypotehesis
 


(25/06/2013) bis
 Unique is done, but there's a bit of a circularity between "safe_uni_ground" and "instOfPats". At the moment "safe_uni_ground" might say "false" for a position even if the assumption couldn't be introduiced by the block, however "n" is needed for makeUniqueTerms with his used in instOfPats...Will have to untangle this at some point - make instOfPat [pattern matching] primitive.

Now onto sync; e.g. 
schema ctx := exists B, nabla n m, (ofb (B;n),ofi, ofb (B;m));
              exists B C,          ( ofb' (B,C;), ofi, ofi);

ctx G1 G2 G3 -> member (of X B) G1 -> exists M, member i G2 /\ member (of M B) G3
ctx G1 G2 G3 -> member i G2 -> (exists X M B, member (of X B) G1 /\ member (of M B) G3) \/
                              member i G1 /\ member i G3
ctx G1 G2 G3 -> member (of X B) G3 -> exists N, member (of M B) G1 /\ member i G2

1) member_of_ith 
2) inst_of_path to see which clauses could've matched the hyp
3) construct the disjunction of the clauses that could've matched, each of a conjunction of the other member (need to deal with which variable to rename/quantify over here)
4) proof looks like unique

(25/06/2013)
 Inversion is done, might want to add typing information in the binding lists of schemas.
  - ask kaustuv why the case H5inv search search instead of search directly on ctx'.
 > Updated unit with multiple tests on inversion
 > Will now look into sync (very similar to inversion) and unique(same proof as before, just need)


(24/06/2013) Schema generation done, start 25th with make_in_stmt, may inline ground_inv_at after
 to ignore the other fields) [25/06 note: Wontfix. ground_in_at renamed member_of_ith, used in uni as well]

(20/06/2013) Meeting with Kaustuv:

- We found out compounding schema as was planned in the previous notes is not directly possible, as we want blocks to be able to share variables, and at the moment quantifiers appears at the level of blocks. We plan on modifying the block/schema syntax as such:
====================================================================
 Block c1(X1,...,Xp ; n1,...,nq) = ∃ X1 ... Xp ∇ n1 ... nq . [...]
 Block c2(X ; n,m) = ∃ X ∇ n m . [...]

 Schema C = ∃ Y1 ...  Yp, ∇ n, c1 (Y1,...,Yp ; n);
            ∃ Y,  ∇ n m,       c2 (Y; m , n).

 Schema CC = ∃ Y,  ∇ n m,    ( c2(Y; n,m) , c2 (Y; m , n))
====================================================================
Important: need to check, when using a block in the schema, that nabla bound variables in the blocks are bound separately at the schema level (e.g. can't do c2(Y;m,m))




(19/06/2013) 
Design of schema relations (n-ary schema definition)
Schemas as , for some number n, list of [tuples of length n] of block names
   Schema A = (a_1,...,z_1);...;(a_m,...,z_m).
Defining the context
  Define A: olist -> ... -> olist -> prop by
   A nil;
   ctx ([a_1]::L^1) ... ([z_1]::L^n):= ctx L^1 /\ ... /\ ctx L^n;
                      ...
 ctx ([a_m]::L^1) ... ([z_m]::L^n):= ctx L^1 /\ ... /\ ctx L^n;
The following lemma can then be generated:

1) Inversion (membership)
 -> add some sync info (i.e. not only refine E from member E G, but show member form from D)

2) Uniqueness 


3) Sync(uniform) lemma, if A \G ... \D and member ([a_1]) \G then member [z_1] \D
   (or [z_m] for every clause m which could be matched by [a_1])

   
   sync (ctxgd \G \D) (member E \G) ->  member E' \D
 




4) Projections lemmas from A to any context including, at least, for some e, e_1;...;e_m
   proj 1 "ctxg" (ctxgd \G \D) -> ctxg \G
   proj 2 "ctxd" (ctxgd \G \D) -> ctxd \D
   proj (2,1) "ctxdg" (ctxgd \G \D) -> (ctxdg \D \G)

5) Injection lemmas,

   inj 1 (ctxg \G) -> \exists D. (ctxgd \G \D)


(18/06/2013 bis)
Meeting with Kaustuv

1) path examples
2) schema relations
   A = b_1|b_2|b_3
   B = c_1 | c_2
   R (A~B)? = (b_1,c_1) | (b_2,c_1)| (b_3,c_2)
 bring projection R \Gamma \Delta -> A \Gamma


(18/06/2013)
Description of the different procedures

Block  |
--------
> Check that the name of the block is not in use
> (Check that the head of the block is a declared constant)
> Get the type of the head constant, and use it to type the list of variables
> Check that the whole block is of type "o"
> Save the list of exists bound variables, the list of nabla bound variables and the body of the block as a utm in "Prover.blocks" associated with the block name
> Make generic lemmas:
  - if no exists bound variable
    o for each type of nabla bound variable 'a, define "'a_name" as "nabla n, 'a_name n."
    o for each pair of nabla bound variable 'a and exists bound 'b, define "fresh_'a_in_'b" as "\nabla n, fresh_'a_in'b n X."
  -
> Process recursively generic lemmas, supressing the output.

Schema |
--------
> Check that the name of schema isn't already used in a definition
>* Check that the blocks were previously defined
> Add the schema name and the list of block names in "Prover.schemas"
> Build and process the context definition from the blocks

Inversion |
-----------
Receives something of form "ctx L" and "member E L", and outputs the form of E
> Get the schema name as the head of hyp1
> check that inversion for that schema wasn't already define, o.w. use the prefious definition
> make and process the inversion statement and the inversion proof from the list of blocks (more details to come)

Unique |
--------
Receives something of form "ctx L" "member E1[X_1..X_n] L" "member E2[X_1..X_n] L"
> Get the schema name as the head of hyp1
> check that inversion for that schema wasn't already define, o.w. use the prefious definition
> observe E1 and E2 from hyp2 and hyp3
 - Create E which matches both E1 and E2
 - Create a bitmap of which block from schema matches E
 - See if, for the variables [X_1,..,X_n] equal and at the same position in E1 and E2, one of them is nabla bound on every blocks which matches E. That variable "grounds" the uniqueness lemma
 - Generate the uniqueness lemma and proof ground at that variables (more details to come)
> process the uniqueness statement and proof

(06/06/2013)
-I need to change the "canonical" term I use to make uni statement. At the moment I used a matching block, but this could be too general for what I'm trying to prove. I need to make a term using the two hypothesis, e.g. "of X A" and "of X (foo B)" would result in "of X (foo A1)" and use this instead of the canonical block


(31/05/2013)

TODO:
0) update structure to handle 1+ nabla and 1+ exists 
    - DONE for parser, Block in abella, generation of generic lemmas/def, still store only the head of nabla/exists.
1) support 1+ nabla variables.
  - generate 1 prune, fresh for each pairs (nabla, exists), if no exists, generate name instead.
  - for uniqueness, verify which variables are the same, then verify if one of them is nabla bound, if so, generate uniqueness centred around that one, resulting in the other variables being equal.
===============================================================

(28/05/2013)
Started looking at proof generation. 

Inversion is easy, each block is the same no matter what the other blocks are

Uniqueness has a number of cases of the case H1 dependent on the number of blocks. 
If the term added by the block is the one being compared, then it can be either front or part of the rest,so it looks something like
   case H2
      -h case H3. 
      	        -h search.
		-t prune
      -t case H3.
       	       -h prune 
	       -t IH 

 o.w. it's part of the tail and we just use I.H.
    case H2. case H3. IH

Note for uniqueness: nabla bound variable has to appear in the term if we want this propertie to hold. e.g. block uhoh: exists P. nabla x. path P P won't have a uniqueness lemma.

===========================================================
QUESTION:
Best way to add defn,theorem,proof?
    - reimplement the theorem portion of process
    - push parsed syntax to input
    - as a new tempfile on input_file, pre-lex.

IDEA:
Generic naming of schema by the blocks
Tactic to generate projections of a schema towards another.
  break ctx_oftmpath 2 3 as ctx_tmpath


ADDED SO FAR:
Lexer, Parser, Pretty-Printer for block with 1 exists, 1 nabla, 1 field.
Lexer, Parser, PP for schema with a list of simple block.
Function add_block, get_block in prover.ml to accumulate blocks at defn and get them at schema declaration.


WIP:
working on processing of block in abella.ml

TODO:
working on processing of block in schema.ml

DESC:
Definition should only be carried out at Schema, 
Block should 
-) Get the pred's signature to type id1, id2 (lookup_const sign "of")
-) create the prune theorem if not already done for the type of the nabla bound variable(id2)
-) store the raw block with add_block
(* pseudo: 1) find the var in tt which is nabla bound
           2) match it with its type from pty
	   3) generate pruning lemma theorem for that type
	   3) update nabla, exists bounds with typing information *)


Schema should
-) Create the context definition, one constructor for each of its block plus the nil one
-) Spawm and prove the various theorems about regular contexts.



Meeting:
-Btw, if not Ty([], A) for nabla then throw error
-For prune...

-Once we have dat lemma in (add_schema_lemma), when get to 
apply hyp_name to...
add "schema_lemma" to hypname













