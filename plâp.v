Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorString :=
  | error_string : ErrorString
  | str : string -> ErrorString.

Coercion boolean: bool >-> ErrorBool.
Coercion num: nat >-> ErrorNat.
Coercion str: string >-> ErrorString.

Check ErrorBool.
Check ErrorNat.
Check ErrorString.
Check bool.

Inductive BoolExp :=
  | btrue
  | bfalse
  | bequal : NatExp -> NatExp -> BoolExp
  | blessthan : NatExp -> NatExp -> BoolExp
  | bgreaterthan : NatExp -> NatExp -> BoolExp
  | band : BoolExp -> BoolExp -> BoolExp
  | bor : BoolExp -> BoolExp -> BoolExp
  | bnot : BoolExp -> BoolExp
  | bnum: ErrorBool -> BoolExp
  | bstr: string -> BoolExp.

Inductive NatExp:=
  | apls: NatExp -> NatExp -> NatExp
  | amul: NatExp -> NatExp -> NatExp 
  | asub: NatExp -> NatExp -> NatExp
  | adiv: NatExp -> NatExp -> NatExp 
  | amod: NatExp -> NatExp -> NatExp
  | anum: ErrorNat -> NatExp
  | astr: string -> NatExp.

