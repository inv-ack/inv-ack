Require Import inv_ack.
Require Import bin_inv_ack.
Require Extraction.


(* ********** Unary ********** *)

Time Compute inv_ack_linear 100.
Time Compute inv_ack_linear 1000.
Time Compute inv_ack_linear 10000.
Time Compute inv_ack_linear 100000.

(* ********** Binary ********** *)

Require Import BinNat. Open Scope N.

Definition n1 := 2^100.
Definition n2 := 2^1000.
Definition n3 := 2^10000.
Definition n4 := 2^100000.
Definition n5 := 2^1000000.
Definition n6 := 2^10000000. 
Definition n7 := 2^100000000.

Time Compute (bin_inv_ack n1). 
Time Compute (bin_inv_ack n2).
Time Compute (bin_inv_ack n3).
Time Compute (bin_inv_ack n4).
Time Compute (bin_inv_ack n5). (* warning, may cause stack overflow *)
Time Compute (bin_inv_ack n6). (* warning, may cause stack overflow *)
Time Compute (bin_inv_ack n7). (* warning, may cause stack overflow *)

Close Scope N.
