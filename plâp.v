Require Import Ascii String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Extraction.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope Z_scope.

Inductive Var :=
|Id : string -> Var.
Coercion Id : string >-> Var.
Scheme Equality for Var.

Inductive ErrorString : Type :=
| error_string : ErrorString
| str : string -> ErrorString.

Inductive ErrorNat : Type :=
| errNr : ErrorNat
| num : Z -> ErrorNat.

Inductive ErrorBool : Type :=
| errBool : ErrorBool
| boolVal : bool -> ErrorBool.

Notation "'str(' S )" := (str S) (at level 0).
Coercion num : Z >-> ErrorNat.
Coercion boolVal : bool >-> ErrorBool.

Inductive StrExp :=
| sconst : ErrorString -> StrExp 
| svar : Var -> StrExp 
| strcat : StrExp -> StrExp -> StrExp 
| toString : Var -> StrExp. 

Definition fun_strConcat (s1 s2: ErrorString) : ErrorString :=
match s1 , s2 with 
  |error_string, _ => error_string
  |_, error_string => error_string
  |str str1, str str2 => str (str1 ++ str2)
end.

Fixpoint Length_help (s : string) : Z :=
  match s with
  | EmptyString => Z0
  | String c s' => 1 + Length_help s'
  end.

Definition fun_strlen (s : ErrorString) : ErrorNat :=
match s with 
| error_string => errNr
| str str1 => num (Length_help str1)
end.

Definition Z_of_bool (b : bool) := if b then 1 else 0.
Definition Z_of_ascii (a : ascii) : Z:=
  match a with
   Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
     Z_of_bool b1 + 2 * (Z_of_bool b2 + 2 * (Z_of_bool b3 + 2 * (Z_of_bool b4 + 2 *
      (Z_of_bool b5 + 2 * (Z_of_bool b6 + 2 * (Z_of_bool b7 + 2 * Z_of_bool b8))))))
  end.

Definition Z_of_0 := Eval compute in Z_of_ascii "0".
Definition Z_of_digit a := 
   let v := Z_of_ascii a - Z_of_0 in
   match v ?= 0 with
     Lt => None | Eq => Some v | 
     Gt => match v ?= 10 with Lt => Some v | _ => None end
   end.
Fixpoint str_to_num (s : string) : option (Z * Z) :=
  match s with
    EmptyString => None
  | String a s' => 
    match Z_of_digit a with
      None => None
    | Some va =>
      match str_to_num s' with
        None => Some (va, 1)
      | Some (vs, n) => Some (va * 10 ^ n + vs, n+1)
      end
    end
  end.
Definition num_to_ErrorNat (n : option(Z*Z)) : ErrorNat :=
match n with
| None => errNr
| Some (nr, _) => num nr
end.
Definition str_toNewNr (s : string) : ErrorNat :=
match s with
| EmptyString => errNr
| String a s' => if (ascii_dec a "-") 
        then (match (num_to_ErrorNat (str_to_num s')) with
              | errNr => errNr
              | num nr => num (0 - nr) end
        ) 
        else (match (num_to_ErrorNat (str_to_num s)) with
              | errNr => errNr
              | num nr => num nr end
        )
end.

Definition digit_to_ascii (n : Z) : ascii :=
match n with
|Z0 => "0"
|1 => "1"
|2 => "2"
|3 => "3"
|4 => "4"
|5 => "5"
|6 => "6"
|7 => "7"
|8 => "8"
|9 => "9"
|_ => ascii_of_nat 1
end.

Fixpoint nr_to_string_aux (time : nat) (n : Z) (acc : string) : string :=
  let acc' := String (digit_to_ascii (n mod 10)) acc in
  match time with
    | 0%nat => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => nr_to_string_aux time' n' acc'
      end
  end.

Definition nr_to_string (n : Z) : string :=
match n with
| Z0 => "0"
| Zpos _ => nr_to_string_aux 15 n ""
| Zneg l => String "-" (nr_to_string_aux 15 (Zpos l) "")
end.

Inductive NatExp:=
| aconst : ErrorNat -> NatExp 
| natvar : Var -> NatExp 
| natpls : NatExp -> NatExp -> NatExp
| natsub : NatExp -> NatExp -> NatExp
| natmul : NatExp -> NatExp -> NatExp
| natdiv : NatExp -> NatExp -> NatExp
| natmod : NatExp -> NatExp -> NatExp
| boolToNr : BoolExp -> NatExp 
| strToNr : StrExp -> NatExp 
| strLen : StrExp -> NatExp 
with BoolExp :=
| bconst : ErrorBool -> BoolExp 
| bvar : Var -> BoolExp 
| bnot : BoolExp -> BoolExp
| band : BoolExp -> BoolExp -> BoolExp
| bor : BoolExp -> BoolExp -> BoolExp
| blessthan : NatExp -> NatExp -> BoolExp
| blessthanEq : NatExp -> NatExp -> BoolExp
| bgreaterthan : NatExp-> NatExp -> BoolExp
| bgreaterthanEq : NatExp -> NatExp -> BoolExp
| bequality : NatExp -> NatExp -> BoolExp
| binequality : NatExp -> NatExp -> BoolExp
| bexclusiveor : BoolExp -> BoolExp -> BoolExp
| toBool : NatExp -> BoolExp. 

Coercion aconst : ErrorNat >-> NatExp.
Coercion bconst : ErrorBool >-> BoolExp.
Coercion sconst : ErrorString >-> StrExp.
Coercion natvar : Var >-> NatExp.
Coercion bvar : Var >-> BoolExp.
Coercion svar : Var >-> StrExp.

Notation "'Concat(' S1 , S2 )" := (strcat S1 S2) (at level 50, left associativity).
Notation "'BoolToNr(' B )" := (boolToNr B) (at level 0).
Notation "'StrToNr(' S )" := (strToNr S) (at level 0).
Notation "'ToBool(' S )" := (toBool S) (at level 0).
Notation "'ToStr(' S )" := (toString S) (at level 0).
Notation "'StrLen(' S )" := (strLen S) (at level 0).

(*Notatii expresii algebrice*)
Notation "A +' B" := (natpls A B)(at level 50, left associativity).
Notation "A -' B" := (natsub A B)(at level 50, left associativity).
Notation "A *' B" := (natmul A B)(at level 48, left associativity).
Notation "A /' B" := (natdiv A B)(at level 48, left associativity).
Notation "A %' B" := (natmod A B)(at level 48, left associativity).

 
(*Notatii expresii booleene*)
Notation "!' A" := (bnot A) (at level 45, right associativity).
Notation "A &&' B" := (band A B) (at level 55, left associativity).
Notation "A ||' B" := (band A B) (at level 56, left associativity).
Notation "A 'xor' B" := (bexclusiveor A B) (at level 56, left associativity).
Notation "A <=' B" := (blessthanEq A B) (at level 52, left associativity).
Notation "A <' B" := (blessthan A B) (at level 52, left associativity).
Notation "A >=' B" := (bgreaterthanEq A B) (at level 52, left associativity).
Notation "A >' B" := (bgreaterthan A B) (at level 52, left associativity).
Notation "A ==' B" := (bequality A B) (at level 53, left associativity).
Notation "A !=' B" := (bequality A B) (at level 53, left associativity).

Inductive Stmt := 
| decl_int : Var -> NatExp -> Stmt 
| decl_bool : Var -> BoolExp -> Stmt 
| decl_string : Var -> StrExp -> Stmt 
| secventa : Stmt -> Stmt -> Stmt 
| skip : Stmt 
| break : Stmt 
| continue : Stmt
| asig_nr : Var -> NatExp -> Stmt 
| asig_bool : Var -> BoolExp -> Stmt
| asig_str : Var -> StrExp -> Stmt
| citeste : Var -> Stmt
| scrie : StrExp -> Stmt
| ifthen : BoolExp -> Stmt -> Stmt 
| ifthenelse : BoolExp -> Stmt -> Stmt -> Stmt
| whileloop : BoolExp -> Stmt -> Stmt
| dowhile : Stmt -> BoolExp -> Stmt
| forloop : Stmt -> BoolExp -> Stmt -> Stmt -> Stmt
| apelfunc : Var -> list Var -> Stmt.


Inductive newType : Type :=
| error : newType 
| nrType : ErrorNat -> newType 
| boolType : ErrorBool -> newType 
| strType : ErrorString -> newType 
| code : Stmt -> newType. 

Coercion nrType : ErrorNat >-> newType.
Coercion boolType : ErrorBool >-> newType.
Coercion strType : ErrorString >-> newType.
Coercion code : Stmt >-> newType.



Notation "'int'' V <-- E" := (decl_int V E) (at level 90, right associativity).
Notation "'bool'' V <-- E" := (decl_bool V E) (at level 90, right associativity).
Notation "'string'' V <-- E" := (decl_string V E) (at level 90, right associativity).
Notation "V :N= E" := (asig_nr V E) (at level 90, right associativity).
Notation "V :B= E" := (asig_bool V E) (at level 90, right associativity).
Notation "V :S= E" := (asig_str V E) (at level 90, right associativity).
Notation "S1 ;; S2" := (secventa S1 S2) (at level 93, right associativity).
Notation "'if'(' B ) 'then'{' S '}end'" := (ifthen B S) (at level 97).
Notation "'if'(' B ) 'then'{' S1 '}else'{' S2 '}end'" := (ifthenelse B S1 S2) (at level 97).
Notation "'while'(' B ) 'do'{' S }" := (whileloop B S) (at level 97).
Notation "'do'{' S '}while(' B )" := (dowhile S B) (at level 97).
Notation "'for'(' I ; B ; A ) 'do'{' S }" := (forloop I B A S) (at level 97).



Notation "'write(' S )" := (scrie S) (at level 92).
Notation "'read(' V )" := (citeste V) (at level 92).


Definition EqForTypes (a b : newType) : bool :=
match a, b with
| error, error => true
| nrType _, nrType _ => true
| boolType _, boolType _ => true
| strType _, strType _ => true
| code _, code _ => true
| _, _ => false
end.

Definition Memory := nat -> newType.
Definition State := Var -> nat.
Inductive MemoryLayer := 
| pair : State -> Memory -> nat -> State -> Memory -> nat -> MemoryLayer.
Notation "<< S , M , N >>-<< GS , GM , GN >>" := (pair S M N GS GM GN) (at level 0).

Definition getVal (m : MemoryLayer) (v : Var) : newType :=
match m with
| pair st mem _ gst gmem _ => if (EqForTypes ( mem (st v) ) error) 
                              then gmem(gst v) else mem(st v)
end.

Definition getLocalMaxPos (m : MemoryLayer) : nat :=
match m with
| pair _ _ max _ _ _  => max
end.

Definition getLocalAdress (m:MemoryLayer) (v : Var) : nat :=
match m with
| pair state _ _ _ _ _ => state v
end.

Definition getAdress (m:MemoryLayer) (v:Var) : nat :=
match m with
| pair st _ _ gst _ _ => if (Nat.eqb (st v) 0%nat) then gst v else st v
end.

Definition updateState (st : State) (v : Var) (n : nat) : State:= 
fun x => if (Var_beq x v) then n else st x.

Definition updateMemory (mem : Memory) (n : nat) (val : newType) : Memory :=
fun n' => if (Nat.eqb n' n) then val else mem n'. 

Definition updateLocal (M : MemoryLayer) (V : Var) (T : newType) (pos : nat) : MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (andb (Nat.eqb pos (getLocalAdress M V) ) (Nat.eqb pos 0) ) then
       <<st, mem, max>>-<<gst, gmem, gmax>> else
       <<updateState st V pos, updateMemory mem pos T, 
      (if (Nat.ltb pos max) then max else Nat.add max 1) >>-<<gst, gmem, gmax>>
end.



Definition updateLocalAtAdress (M : MemoryLayer) (addr : nat) (T : newType): MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (Nat.eqb addr 0) then
       <<st, mem, max>>-<<gst, gmem, gmax>> else
       <<st, updateMemory mem addr T, max >>-<<gst, gmem, gmax>>
end.



Definition updateAtAdress (M : MemoryLayer) (addr : nat) (T : newType) : MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => updateLocalAtAdress M addr T
end.










 
Definition mem0 : Memory := fun n => error.
Definition state0 : State := fun x => 0%nat.
Definition stack0 := <<state0, mem0, 1>>-<<state0, mem0, 1>>.

Definition newPlus (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | num n1, num n2 => nrType (n1 + n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

