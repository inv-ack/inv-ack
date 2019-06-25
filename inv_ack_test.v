Require Import inv_ack.
Require Import bin_inv_ack.


(* ********** Unary ********** *)

Time Compute inv_ack_linear 100.
Time Compute inv_ack_linear 1000.
Time Compute inv_ack_linear 10000.
Time Compute inv_ack_linear 100000.



(* ********** Binary ********** *)

Require Import BinNat. Open Scope N.

Definition bignum1 := 2^2^2^2.   (* 65536 *)
Definition bignum2 := bignum1^2. (* 4.3 x 10^9 *)
Definition bignum3 := 2^bignum1. (* 2.0 x 10^19728 *)
Definition bignum4 := bignum3^2. (* 4.0 x 10^39456 *)

Time Compute (bin_inv_ack bignum1).
Time Compute (bin_inv_ack bignum2).
Time Compute (bin_inv_ack bignum3).
Time Compute (bin_inv_ack bignum4).

Close Scope N.
