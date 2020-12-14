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
  | natpls: NatExp -> NatExp -> NatExp
  | natmul: NatExp -> NatExp -> NatExp 
  | natsub: NatExp -> NatExp -> NatExp
  | natdiv: NatExp -> NatExp -> NatExp 
  | natmod: NatExp -> NatExp -> NatExp
  | natnum: ErrorNat -> NatExp
  | natstr: string -> NatExp.


Notation "A !+ B" := (natpls A B)(at level 20, left associativity).
Notation "A !* B" := (natmul A B)(at level 19, left associativity).
Notation "A !- B" := (natsub A B)(at level 20, left associativity).
Notation "A !/ B" := (natdiv A B)(at level 19, left associativity).
Notation "A !% B" := (natmod A B)(at level 19, left associativity).

Inductive StrExp :=
  | strcat : StrExp -> StrExp -> StrExp
  | strupper : StrExp -> StrExp
  | strlower : StrExp -> StrExp
  | strset : StrExp -> StrExp -> StrExp
  | strvar : string -> StrExp.

Notation "S !strcat S'" := (strcat S S')(at level 40).
Notation "!upper S" := (strupper S)(at level 40).
Notation "!lower S" := (strlower S)(at level 40).
Notation "!strset S S'" := (strset S S')(at level 40).

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

Notation "A !< B" := (blessthan A B) (at level 70).
Notation "A !> B" := (bgreaterthan A B) (at level 70).
Notation "!! A" := (bnot A)(at level 71, left associativity).
Notation "A !&& B" := (band A B)(at level 72, left associativity).
Notation "A !|| B" := (bor A B)(at level 73, left associativity).
Notation "A !strcmp B" := (bstrcmp A B)(at level 73, left associativity).

Inductive Stmt :=
  | declare_nat: string -> NatExp -> Stmt 
  | declare_string: string -> StrExp -> Stmt 
  | declare_bool: string -> BoolExp -> Stmt 
 
  | nat_assign : string -> NatExp -> Stmt 
  | str_assign : string -> StrExp -> Stmt 
  | bool_assign : string -> BoolExp -> Stmt

  | while : BoolExp -> Stmt -> Stmt
  | ifthen : BoolExp -> Stmt -> Stmt
  | ifelse : BoolExp -> Stmt -> Stmt -> Stmt
  | sequence : Stmt -> Stmt -> Stmt.

Notation "X !n= A" := (nat_assign X A)(at level 75).
Notation "X !s= A" := (str_assign X A)(at level 75).
Notation "X !b= A" := (bool_assign X A)(at level 75).

Notation "!Nat X ::= A" := (declare_nat X A)(at level 75).
Notation "!Str X ::= A" := (declare_string X A)(at level 75).
Notation "!Bool X ::= A" := (declare_bool X A)(at level 75).

Notation "S1 , S2" := (sequence S1 S2) (at level 80).
Notation "!while ( A ) { S } " := (while A S)(at level 80). 
Notation "!for ( A ; B ; C ) { S }" := (A , while B ( S , C )) (at level 97).


Reserved Notation "A =[ S ]=> N" (at level 90).
Reserved Notation "B ={ S }=> B'" (at level 91).
Reserved Notation "B ={ S }=> B'" (at level 91).
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 90).

Coercion natnum: ErrorNat >-> NatExp.
Coercion natstr: string >-> NatExp. 
Coercion bnum: ErrorBool >-> BoolExp.
Coercion bstr: string >-> BoolExp. 
Coercion strvar: string >-> StrExp.

Definition nat_plsmergi :=
  !Nat "i" ::= 0,
  !Nat "j" ::= 1,
  !Nat "k" ::= 0, 
  "k" !n= "i" !+ "j", 
  "j" !n= "j" !- "i",
  "i" !n= "j" !* "i", 
  "j" !n= 2 !+ 1,
  "j" !n= "i" !/ "j",   "j" !n= "i" !% "j".

Check nat_plsmergi.


Definition bool_plsmergi :=
  
  
  
  
  





