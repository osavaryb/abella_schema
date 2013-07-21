/****************************************************************************/
/* Copyright (C) 2007-2009 Gacek                                            */
/*                                                                          */
/* This file is part of Abella.                                             */
/*                                                                          */
/* Abella is free software: you can redistribute it and/or modify           */
/* it under the terms of the GNU General Public License as published by     */
/* the Free Software Foundation, either version 3 of the License, or        */
/* (at your option) any later version.                                      */
/*                                                                          */
/* Abella is distributed in the hope that it will be useful,                */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of           */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            */
/* GNU General Public License for more details.                             */
/*                                                                          */
/* You should have received a copy of the GNU General Public License        */
/* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          */
/****************************************************************************/

%{

  open Typing

  module Types = Schema_types

  let pos i =
    if i = 0 then
      (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
    else
      (Parsing.rhs_start_pos i, Parsing.rhs_end_pos i)

  let predefined id =
    UCon(pos 0, id, Term.fresh_tyvar ())

  let binop id t1 t2 =
    UApp(pos 0, UApp(pos 0, predefined id, t1), t2)

  let nested_app head args =
    List.fold_left
      (fun h a -> UApp((fst (get_pos h), snd (get_pos a)), h, a))
      head args

%}

%token IMP COMMA DOT BSLASH LPAREN RPAREN TURN CONS EQ TRUE FALSE DEFEQ BANG
%token SCHEMA INVERSION PROJECTION SYNC UNIQUE
%token IND INST APPLY CASE FROM SEARCH TO ON WITH INTROS CUT ASSERT CLAUSEEQ SCHPRO
%token SKIP UNDO ABORT COIND LEFT RIGHT MONOTONE IMPORT BY
%token SPLIT SPLITSTAR UNFOLD KEEP CLEAR SPECIFICATION SEMICOLON
%token THEOREM DEFINE PLUS CODEFINE SET ABBREV UNABBREV QUERY SHOW 
%token PERMUTE BACKCHAIN QUIT UNDERSCORE AS SSPLIT RENAME
%token COLON RARROW FORALL NABLA EXISTS STAR AT HASH OR AND 
%token LBRACE RBRACE LBRACK RBRACK
%token KIND TYPE KKIND TTYPE SIG MODULE ACCUMSIG ACCUM END CLOSE

%token <int> NUM
%token <string> STRINGID QSTRING
%token EOF

/* Lower */

%nonassoc COMMA
%right RARROW
%left OR
%left AND

%nonassoc BSLASH
%right IMP
%nonassoc EQ

%right CONS

/* Higher */


%start term metaterm top_command command
%type <Typing.uterm> term
%type <Typing.umetaterm> metaterm
%type <Schema_types.top_command> top_command
%type <Schema_types.command> command

%%

hyp:
  | STRINGID                             { $1 }
  | UNDERSCORE                           { "_" }

id:
  | STRINGID                             { $1 }
  | IND                                  { "induction" }
  | INST                                 { "inst" }
  | APPLY                                { "apply" }
  | BACKCHAIN                            { "backchain" }
  | CASE                                 { "case" }
  | SEARCH                               { "search" }
  | TO                                   { "to" }
  | ON                                   { "on" }
  | BY                                   { "by" }
  | AS                                   { "as" }
  | WITH                                 { "with" }
  | INTROS                               { "intros" }
  | CUT                                  { "cut" }
  | FROM                                 { "from" }
  | ASSERT                               { "assert" }
  | SKIP                                 { "skip" }
  | UNDO                                 { "undo" }
  | ABORT                                { "abort" }
  | COIND                                { "coinduction" }
  | LEFT                                 { "left" }
  | RIGHT                                { "right" }
  | MONOTONE                             { "monotone" }
  | SPLIT                                { "split" }
  | UNFOLD                               { "unfold" }
  | KEEP                                 { "keep" }
  | CLEAR                                { "clear" }
  | ABBREV                               { "abbrev" }
  | UNABBREV                             { "unabbrev" }
  | RENAME                               { "rename" }
  | PERMUTE                              { "permute" }
  | THEOREM                              { "Theorem" }
  | IMPORT                               { "Import" }
  | SPECIFICATION                        { "Specification" }
  | DEFINE                               { "Define" }
  | CODEFINE                             { "CoDefine" }
  | SET                                  { "Set" }
  | SHOW                                 { "Show" }
  | QUIT                                 { "Quit" }
  | QUERY                                { "Query" }
  | SSPLIT                               { "Split" }
  | CLOSE                                { "Close" }
  | TTYPE                                { "Type" }
  | KKIND                                { "Kind" }
  | SCHEMA                               { "Schema" }
  | PROJECTION                           { "projas" }
  | UNIQUE                               { "unique" }
  | SYNC                                 { "sync"}
  | INVERSION                            { "inversion"}

/* Annotated ID */
aid:
  | id                                   { ($1, Term.fresh_tyvar ()) }
  | id COLON ty                          { ($1, $3) }

/* Parenthesized annotated ID */
paid:
  | id                                   { ($1, Term.fresh_tyvar ()) }
  | LPAREN id COLON ty RPAREN            { ($2, $4) }
  | UNDERSCORE                           { ("_", Term.fresh_tyvar ()) }
  | LPAREN UNDERSCORE COLON ty RPAREN    { ("_", $4) }

contexted_term:
  | context TURN term                    { ($1, $3) }
  | term                                 { (predefined "nil", $1) }

focused_term:
  | context COMMA LBRACK term RBRACK TURN term { ($1, $4, $7) }
  | LBRACK term RBRACK TURN term               { (predefined "nil", $2, $5) }

context:
  | context COMMA term                   { binop "::" $3 $1 }
  | term                                 { if has_capital_head $1 then
                                             $1
                                           else
                                             binop "::" $1
                                               (predefined "nil") }

term:
  | term IMP term                        { binop "=>" $1 $3 }
  | term CONS term                       { binop "::" $1 $3 }
  | aid BSLASH term                      { let (id, ty) = $1 in
                                             ULam(pos 0, id, ty, $3) }
  | exp exp_list                         { nested_app $1 $2 }
  | exp                                  { $1 }

exp:
  | LPAREN term RPAREN                   { let left = fst (pos 1) in
                                           let right = snd (pos 3) in
                                             change_pos (left, right) $2 }
  | paid                                 { let (id, ty) = $1 in
                                             UCon(pos 0, id, ty) }

exp_list:
  | exp exp_list                         { $1::$2 }
  | exp                                  { [$1] }
  | aid BSLASH term                      { let (id, ty) = $1 in
                                             [ULam(pos 0, id, ty, $3)] }




sclause_list:
  | existsopt nablaopt term_tup                { [($1,$2,$3)] }
  | existsopt nablaopt term_tup SEMICOLON sclause_list  { ($1,$2,$3)::$5}


term_tup:
  | term                                 { [$1] }
  | LPAREN term_list RPAREN              { $2   }

term_list:
  | term                                 { [$1] }
  | term COMMA term_list                 { $1::$3}

id_list:
  | id                                   { [$1] }
  | id COMMA id_list                     { $1::$3}

ty:
  | id                                   { Term.tybase $1 }
  | ty RARROW ty                         { Term.tyarrow [$1] $3 }
  | LPAREN ty RPAREN                     { $2 }

clause:
  | term DOT                             { ($1, []) }
  | term CLAUSEEQ clause_body DOT        { ($1, $3) }

clause_body:
  | term COMMA clause_body               { $1::$3 }
  | LPAREN term COMMA clause_body RPAREN { $2::$4 }
  | term                                 { [$1] }

defs:
  | def SEMICOLON defs                   { $1::$3 }
  | def                                  { [$1] }

def:
  | metaterm                             { ($1, UTrue) }
  | metaterm DEFEQ metaterm              { ($1, $3) }

existsopt:
  | EXISTS utbinding_list COMMA            { $2 }
  |                                      { [] }

nablaopt:
  | NABLA utbinding_list COMMA            { $2 }
  |                                      { [] }

opt_perm:
|  LPAREN perm_ids RPAREN                {Some $2}
|                                        { None}

perm:
  | LPAREN perm_ids RPAREN               { $2 }

perm_ids:
  | id perm_ids                          { $1 :: $2 }
  | id                                   { [$1] }



command:
  | INVERSION hyp_list DOT                    { Schema_types.Inversion($2)}
  | PROJECTION LPAREN perm_ids RPAREN hyp_list DOT    { Schema_types.Projection($3,$5)}
  | UNIQUE hyp_list DOT                       { Schema_types.Unique($2)}
  | SYNC hyp_list DOT                         { Schema_types.Sync($2)}
  | EOF                                       { raise End_of_file }

hhint:
  | STRINGID COLON                       { Some $1 }
  |                                      { None }

hyp_list:
  | hyp hyp_list                         { $1::$2 }
  | hyp                                  { [$1] }

num_list:
  | NUM num_list                         { $1::$2 }
  | NUM                                  { [$1] }

withs:
  | id EQ term COMMA withs               { ($1, $3) :: $5 }
  | id EQ term                           { [($1, $3)] }

metaterm:
  | TRUE                                 { UTrue }
  | FALSE                                { UFalse }
  | term EQ term                         { UEq($1, $3) }
  | binder binding_list COMMA metaterm   { UBinding($1, $2, $4) }
  | metaterm RARROW metaterm             { UArrow($1, $3) }
  | metaterm OR metaterm                 { UOr($1, $3) }
  | metaterm AND metaterm                { UAnd($1, $3) }
  | LPAREN metaterm RPAREN               { $2 }
  | objseq                               { $1 }
  | term restriction                     { UPred($1, $2) }

objseq:
  | LBRACE contexted_term RBRACE restriction
                                         { let l, g = $2 in
                                             UAsyncObj(l, g, $4) }
  | LBRACE focused_term RBRACE restriction
                                         { let l, f, g = $2 in
                                             USyncObj(l, f, g, $4) }

binder:
  | FORALL                               { Metaterm.Forall }
  | EXISTS                               { Metaterm.Exists }
  | NABLA                                { Metaterm.Nabla }

utbinding_list:
  | id utbinding_list                    { $1::$2 }
  | id                                 { [$1] }

binding_list:
  | paid binding_list                    { $1::$2 }
  | paid                                 { [$1] }


restriction:
  |                                      { Metaterm.Irrelevant }
  | stars                                { Metaterm.Smaller $1 }
  | pluses                               { Metaterm.CoSmaller $1 }
  | ats                                  { Metaterm.Equal $1 }
  | hashes                               { Metaterm.CoEqual $1 }

stars:
  | STAR stars                           { 1 + $2 }
  | STAR                                 { 1 }

ats:
  | AT ats                               { 1 + $2 }
  | AT                                   { 1 }

pluses:
  | PLUS pluses                          { 1 + $2 }
  | PLUS                                 { 1 }

hashes:
  | HASH hashes                          { 1 + $2 }
  | HASH                                 { 1 }

id_ty:
  | id COLON ty                          { ($1, $3) }

id_tys:
  | id_ty COMMA id_tys                   { $1::$3 }
  | id_ty                                { [$1] }


top_command:
  | SCHEMA id DEFEQ sclause_list DOT          { Schema_types.SchemaDef($2,$4) }
  | EOF                                       { raise End_of_file }


