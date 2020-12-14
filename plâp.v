Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorString :=
  | error_string : ErrorString
  | str : string -> ErrorString.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.


Coercion num: nat >-> ErrorNat.
Coercion str: string >-> ErrorString.
Coercion boolean: bool >-> ErrorBool.

(*Check ErrorBool.
Check ErrorNat.
Check ErrorString.
Check bool.*)

Inductive NatExp:=
  | apls: NatExp -> NatExp -> NatExp
  | amul: NatExp -> NatExp -> NatExp 
  | asub: NatExp -> NatExp -> NatExp
  | adiv: NatExp -> NatExp -> NatExp 
  | amod: NatExp -> NatExp -> NatExp
  | anum: ErrorNat -> NatExp
  | astr: string -> NatExp.

Inductive StrExp :=
  | strcat : StrExp -> StrExp -> StrExp
  | strupper : StrExp -> StrExp
  | strlower : StrExp -> StrExp
  | strset : StrExp -> StrExp -> StrExp
  | strnum : ErrorString -> StrExp
  | strvar: string -> StrExp.

Inductive BoolExp :=
  | btrue
  | bfalse
  | bequal : NatExp -> NatExp -> BoolExp
  | blessthan : NatExp -> NatExp -> BoolExp
  | bgreaterthan : NatExp -> NatExp -> BoolExp
  | band : BoolExp -> BoolExp -> BoolExp
  | bor : BoolExp -> BoolExp -> BoolExp
  | bnot : BoolExp -> BoolExp
  | bstrcmp : StrExp -> StrExp -> BoolExp
  | bnum: ErrorBool -> BoolExp
  | bstr: string -> BoolExp.

Inductive Stmt :=
  | nat_decl: string -> NatExp -> Stmt 
  | bool_decl: string -> BoolExp -> Stmt 
  | str_decl: string -> StrExp -> Stmt 

  | nat_assign : string -> NatExp -> Stmt
  | bool_assign : string -> BoolExp -> Stmt 
  | str_assign : string -> StrExp -> Stmt 

  | while : BoolExp -> Stmt -> Stmt
  | ifthenelse : BoolExp -> Stmt -> Stmt -> Stmt
  | ifthen : BoolExp -> Stmt -> Stmt
  | sequence : Stmt -> Stmt -> Stmt.



