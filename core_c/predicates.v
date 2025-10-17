From stdpp Require Import mapset natmap.
Require Export  terms.
Inductive predic (K : iType) : iType :=
| PTrue : predic K
| PFalse : predic K
| PAt : predic K -> predic K
| PRelOp : compop -> term K -> term K ->  predic K
| POr : predic K -> predic K -> predic K
| PAnd : predic K -> predic K -> predic K
| PImpl : predic K -> predic K -> predic K
| PNot : predic K -> predic K
| PValid : term K -> predic K
| PInit : term K -> predic K.

Declare Scope pred_scope.
Delimit Scope pred_scope with P.
Bind Scope pred_scope with predic.
Local Open Scope pred_scope.

Arguments PTrue {_}.
Arguments PFalse {_}.
Arguments PAt {_} _%pred_scope.
Arguments PRelOp {_} _ _%term_scope _%term_scope.
Arguments POr {_} _%pred_scope _%pred_scope. 
Arguments PAnd {_} _%pred_scope _%pred_scope.
Arguments PImpl {_} _%pred_scope _%pred_scope.
Arguments PNot {_} _%pred_scope.
Arguments PValid {_} _%term_scope.
Arguments PInit {_} _%term_scope.
