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

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
  | error_string : ErrorString
  | str : string -> ErrorString.

Inductive ErrorVector :=
  | error_vector : ErrorVector
  | vctr : vector -> ErrorVector.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion str: string >-> ErrorString.
Coercion vctr : 