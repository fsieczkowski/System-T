(** This file defines the syntax of the System T extended with stream types. *)

(* Types *)
Inductive ty :=
| tnat : ty
| tarrow : ty -> ty -> ty
| stream : ty -> ty.

Notation " A '→' B " := (tarrow A B) (at level 30, right associativity) : t_scope.
Notation " 'ω' " := tnat : t_scope.
Open Scope t_scope.

(* Terms *)
(* The formalisation uses de Bruijn indices to deal with binders. *)
Inductive te :=
| var  : nat -> te
| lam  : ty -> te -> te
| appl : te -> te -> te
| z    : te
| s    : te -> te
| rec  : te -> te -> te -> te
| hd   : te -> te
| tl   : te -> te
| seed : te -> te -> te -> te.

Notation "'λ' A , M " := (lam A M) (at level 50) : t_scope.
Notation " # n " := (var n) (at level 20) : t_scope.
Notation " M @ N " := (appl M N) (at level 40, left associativity) : t_scope.

Close Scope t_scope.