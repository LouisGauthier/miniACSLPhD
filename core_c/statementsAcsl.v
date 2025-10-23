From Coq Require Import String. 
From stdpp Require Import stringmap mapset zmap.
(* From stdpp Require Import stringmap mapset zmap. *)
Require Import optionmap.
Require Export predicates predicate_eval statements smallstep.
Print predicate_to_prop.

Reserved Notation "Γ \ δ ⊢ₛ S1 ⇒ S2"
  (at level 74, δ at next level,
    format "Γ \  δ  ⊢ₛ  '[' S1  ⇒ '/'  S2 ']'").
Print sctx_item.

(** ACSL Statements *)
Inductive stmtacsl (K : iType) : iType :=
  | SADo : expr K → stmtacsl K
  | SASkip : stmtacsl K
  | SAGoto : labelname → stmtacsl K
  | SAThrow : nat → stmtacsl K
  | SAReturn : expr K → stmtacsl K
  | SACase : option Z → stmtacsl K
  | SALabel : labelname → stmtacsl K
  | SALocal : type K → stmtacsl K → stmtacsl K
  | SACatch : stmtacsl K → stmtacsl K
  | SAComp : stmtacsl K → stmtacsl K → stmtacsl K
  | SALoop : stmtacsl K → stmtacsl K
  | SAIf : expr K → stmtacsl K → stmtacsl K → stmtacsl K
  | SASwitch : expr K → stmtacsl K → stmtacsl K
| SAAssert : predic K → stmtacsl K.

Print esctx_item.
Arguments SADo {_} _.
Arguments SASkip {_}.
Arguments SAGoto {_} _%string.
Arguments SAThrow {_} _.
Arguments SAReturn {_} _.
Arguments SACase {_} _%Z.
Arguments SALabel {_} _%string.
Arguments SALocal {_} _%T _%S.
Arguments SACatch {_} _.
Arguments SAComp {_}_%S _%S.
Arguments SALoop {_} _%S.
Arguments SAIf {_} _%E _%S _%S.
Arguments SASwitch {_} _%E _%S.
Arguments SAAssert {_} _.


Notation funenvacsl K := (funmap (stmtacsl K)).


Inductive aesctx_item (K : iType) : iType :=
    ADoE : aesctx_item K
  | AReturnE : aesctx_item K
  | AIfE : stmtacsl K → stmtacsl K → aesctx_item K
  | ASwitchE : stmtacsl K → aesctx_item K.

Arguments ADoE {K}.
Arguments AReturnE {K}.
Arguments AIfE {K} (_ _)%stmt_scope.
Arguments ASwitchE {K} _%stmt_scope.

(* Undefined states*)
Inductive acslundef_state (K : iType) : iType :=
    AUndefExpr : ectx K → expr K → acslundef_state K
| AUndefBranch : aesctx_item K → lockset → val K → acslundef_state K
| AUndefPred : predic K -> acslundef_state K.

Arguments AUndefExpr {K} _%list_scope _%expr_scope.
Arguments AUndefBranch {K} _ _ _%val_scope.
Arguments AUndefPred {K} _. 

Inductive acslfocus (K : iType) : iType :=
    AFStmt : direction K → stmtacsl K → acslfocus K
  | AFExpr : expr K → acslfocus K
  | AFTerm : term K -> acslfocus K
  | AFCall : funname → list (val K) → acslfocus K
  | AFReturn : funname → val K → acslfocus K
  | AFUndef : acslundef_state K → acslfocus K.

Arguments AFStmt {_} _ _.
Arguments AFExpr {_} _.
Arguments AFTerm {_} _.
Arguments AFCall {_} _ _.
Arguments AFReturn {_} _ _.
Arguments AFUndef {_} _.

Inductive asctx_item (K : iType) : iType :=
    ACatch : asctx_item K
  | ACompL : stmtacsl K → asctx_item K
  | ACompR : stmtacsl K → asctx_item K
  | ALoop : asctx_item K
  | AIfL : expr K → stmtacsl K → asctx_item K
  | AIfR : expr K → stmtacsl K → asctx_item K
  | ASwitch : expr K → asctx_item K.

Arguments ACatch {K}.
Arguments ACompL {K} _%stmt_scope.
Arguments ACompR {K} _%stmt_scope.
Arguments ALoop {K}.
Arguments AIfL {K} _%expr_scope _%stmt_scope.
Arguments AIfR {K} _%expr_scope _%stmt_scope.
Arguments ASwitch {K} _%expr_scope.

Inductive acslctx_item (K : iType) : iType :=
  AStmt : asctx_item K → acslctx_item K
| ALocal : memory_basics.index → type K → acslctx_item K
| AExpr : expr K → aesctx_item K → acslctx_item K
| ATerm : term K -> acslctx_item K
| AFun : ectx K → acslctx_item K
| AParams : funname → list (memory_basics.index * type K) → acslctx_item K.

Notation acslctx K := (list (acslctx_item K)).

Arguments AStmt {_} _.
Arguments ALocal {_} _ _.
Arguments AExpr {_} _ _.
Arguments ATerm {_} _.
Arguments AFun {_} _.
Arguments AParams {_} _ _. 

#[global] Instance aesctx_item_subst {K} :
  Subst (aesctx_item K) (expr K) (stmtacsl K) := λ Ee e,
    match Ee with
    | ADoE => SADo e
    | AReturnE => SAReturn e
    | AIfE s1 s2 => SAIf e s1 s2
    | ASwitchE s => SASwitch e s
    end.

Record stateacsl (K : iType) : iType := Stateacsl
                                          { SACtx : acslctx K;
                                            SAFoc : acslfocus K;
                                            SAMem : mem K;
                                            SALabm : stringmap (mem K);
                                            SALabs : stringmap (stack K) }.

Arguments Stateacsl {_} _ _ _ _.
