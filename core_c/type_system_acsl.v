From stdpp Require Import fin_map_dom.
Require Export  operations state terms.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section typing.
  Context `{Env K}.

  (* !!! These two global instance are used to redefine notations (en,delt) ⊢ v : τlr 
   (broken by the export of terms)*)
  #[global] Instance lrval_typed:
    Typed (env K * memenv K) (lrtype K) (lrval K) := uncurry lrval_typed'.


  #[global] Instance ref_typed `{Env K} :
  PathTyped (env K) (type K) (type K) (ref K) := ref_typed'.

  Inductive type_term (K : iType) : iType :=
  | TtypeC : type K -> type_term K
  | TintZ : type_term K.
  
  Notation lrtype_term K := (ptr_type K + type_term K)%type.
  
  Arguments TtypeC {_} _.
  Arguments TintZ {_}.
  Check (_,_) ⊢ _ : _.

  Inductive tunop_typed (K : iType) (H : Env K) : tunop -> type_term K -> type_term K -> Prop :=
  | Tnegop_typed : forall  (taub sigmab : base_type K),
      unop_typed NegOp (baseT taub) (baseT sigmab) ->
      tunop_typed K H TNegOp (TtypeC (baseT taub)) (TtypeC (baseT sigmab))
                  
  | Tcomplop_typed : forall (taub sigmab : base_type K),
      unop_typed ComplOp (baseT taub) (baseT sigmab) ->
      tunop_typed K H TComplOp (TtypeC (baseT taub)) (TtypeC (baseT sigmab))
                  
  | TintZ_typed : forall (op : tunop),
      tunop_typed K H op TintZ TintZ.

  Inductive tbinop_typed (K:iType) (H : Env K) :
  tbinop -> type_term K -> type_term K -> type_term K -> Prop :=
| TShitfOp_typed : forall (tau1 tau2 sigma : base_type K) (op : shiftop),
    binop_typed (ShiftOp op) tau1 tau2 sigma ->
    tbinop_typed K H (TShiftOp op) (TtypeC tau1) (TtypeC tau2) (TtypeC sigma)
                 
| TBitOp_typed : forall (tau1 tau2 sigma : base_type K) (op : bitop),
    binop_typed (BitOp op) tau1 tau2 sigma ->
    tbinop_typed K H (TBitOp op) (TtypeC tau1) (TtypeC tau2) (TtypeC sigma)
                 
| TArithOp_typed : forall (tau1 tau2 sigma : base_type K) (op : arithop),
    binop_typed (ArithOp op) tau1 tau2 sigma ->
    tbinop_typed K H (TArithOp op) (TtypeC tau1) (TtypeC tau2) (TtypeC sigma)
                 
| TArithOp_typedZ : forall (op : arithop),
    tbinop_typed K H (TArithOp op) TintZ TintZ TintZ.

  
  Inductive term_typed (en : env K) (delt : memenv K) (ts : list (type K)) (l : labelname) :
    term K -> lrtype_term K -> Prop :=
  | TVar_typed tau i :
    ts !! i = Some tau -> term_typed en delt ts l (TVar i) (inl (TType tau)) 
                                     
  | TVal_typed_int v (τlr : lrtype K) (x : int_type K) (n : Z):
    ((en,delt) ⊢ v : τlr) →  maybe inr τlr = Some (TBase (TInt x))->
    term_typed en delt ts l (TVal (inr (ValC K (VBase (VInt x n))))) (inr (TintZ))
               
  | TVal_typed  v τlr : 
    (en,delt) ⊢ v : τlr → term_typed en delt ts l (TVal (inr (ValC K v))) (inr (TtypeC τlr))
                                     
  | TRtoL_typed t τp :
    term_typed en delt ts l t (inr (TtypeC (τp.*))) ->
                             term_typed en delt ts l (TRtoL t) (inl τp)
                                        
  | TLoad_typed_int t τ x :
    term_typed en delt ts l t (inl (TType τ)) → type_complete en τ → τ = TBase (TInt x) ->
    term_typed en delt ts l (TLoad t) (inr (TintZ))
               
  | TLoad_typed t τ :
    term_typed en delt ts l t (inl (TType τ)) -> type_complete en τ ->
    term_typed en delt ts l (TLoad t) (inr (TtypeC τ))
               
  | TEltL_typed t rs τ σ  :
    term_typed en delt ts l t (inl (TType τ)) → en ⊢ rs : τ ↣ σ ->
                                                        term_typed en delt ts l (TEltL t rs) (inl (TType σ))
                                                                   
  | TEltR_typed t rs τ (σ:type K)  :
    term_typed en delt ts l t (inr (TtypeC τ)) → en ⊢ rs : τ ↣ σ →   
                                                         term_typed en delt ts l (TEltR t rs) (inr (TtypeC σ))
                                                                    
  | TEltR_typed_int t rs τ (σ:type K) (x : int_type K) :
    term_typed en delt ts l t (inr (TtypeC τ)) → en ⊢ rs : τ ↣ σ →  σ = (TBase (TInt x)) ->
                                                term_typed en delt ts l (TEltR t rs) (inr (TintZ))                                                                  
                                                           
  | TUnOp_typed op t τ σ :
    tunop_typed _ _ op τ σ → term_typed en delt ts l t (inr (TintZ)) →
    term_typed en delt ts l (TUnOp op t) (inr σ)
               
  | TBinOp_typed op t1 t2 τ1 τ2 σ :
    tbinop_typed K H op τ1 τ2 σ → term_typed en delt ts l t1 (inr τ1) →
    term_typed en delt ts l t2 (inr τ2) →
    term_typed en delt ts l (TBinOp op t1 t2) (inr σ)
                                         
  | TRofL_typed t τp :
    term_typed en delt ts l t (inl τp) →
    term_typed en delt ts l (TRofL t) (inr (TtypeC (τp.*)))

  | TBlckLen_typed t :
    term_typed en delt ts l (TBlckLen t) (inr (TintZ))

  | TOffset_typed t : 
    term_typed en delt ts l (TOffset t) (inr (TintZ))

  | TBaseAddr_typed t tau :
    term_typed en delt ts l t (inl tau) ->
    term_typed en delt ts l (TBaseAddr t) (inr (TtypeC (tau.*)))

  | TAt_typed t lab σ :
    term_typed en delt ts lab t σ ->
    term_typed en delt ts l (TAt t lab) σ.
                                                         
End typing.
