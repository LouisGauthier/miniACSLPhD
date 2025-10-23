From stdpp Require Import mapset natmap.
Require Export  operations_term.
Notation lrval K := (ptr K + val K)%type.
Notation lrval_term K := (ptr K + val_term K)%type.
(* Definition  of ACSL terms *)
Inductive term (K:iType) : iType :=
| TVar : nat -> term K
| TVal : lrval_term K -> term K
| TRtoL : term K -> term K
| TRofL : term K -> term K
| TLoad : term K → term K
| TBinOp : tbinop -> term K -> term K -> term K
| TUnOp : tunop -> term K -> term K                                
| TEltL : term K -> ref_seg K -> term K
| TEltR :term K -> ref_seg K -> term K
| TBlckLen : term K -> term K
| TOffset : term K -> term K                         
| TBaseAddr : term K -> term K
| TAt : term K -> labelname -> term K.

Inductive tctx_item (K : iType) : iType :=
| CTRtoL : tctx_item K
| CTLtoR : tctx_item K
| CTEltL : ref_seg K → tctx_item K
| CTEltR : ref_seg K → tctx_item K
| CTUnOp : unop → tctx_item K
| CTBinOpL : binop → term K → tctx_item K
| CTBinOpR : binop → term K → tctx_item K
| CTBlckLen : tctx_item K
| CTOffset : tctx_item K                       
| CTBaseAddr : tctx_item K.
Notation tctx K := (list (tctx_item K)).


Declare Scope term_scope.
Delimit Scope term_scope with T.
Bind Scope term_scope with term.
Local Open Scope term_scope.
Arguments TVar {_} _.
Arguments TVal {_} _.
Arguments TRtoL {_} _%term_scope.
Arguments TRofL {_} _%term_scope.
Arguments TLoad {_} _%term_scope.
Arguments TEltL {_} _%term_scope _.
Arguments TEltR {_} _%term_scope _.
Arguments TUnOp {_} _ _%term_scope.
Arguments TBinOp {_} _ _%term_scope _%term_scope.
Arguments TBlckLen {_} _%term_scope.
Arguments TOffset {_} _%term_scope.
Arguments TBaseAddr {_} _%term_scope.
Arguments TAt {_} _ _%term_scope.
