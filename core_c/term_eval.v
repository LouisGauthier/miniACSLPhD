Require Export terms type_system operations_term.
Local Open Scope term_scope.
Require Import List String stringmap.
Import ListNotations.
Local Coercion Z.of_nat: nat >-> Z.
Notation lrval_term K := (ptr K + val_term K)%type.
Arguments ValC {_} _.
Arguments VInteger {_} _.
Check maybe (inl).

Definition memmap (K : iType) := stringmap (mem K).
Definition stackmap (K: iType) := stringmap (stack K).

#[global] Instance lmap_insert {K} :
  Insert string (mem K) (memmap K) := λ l m lm,
    <[l:=m]>lm.

#[global] Instance lmap_lookup {K} : Lookup string (mem K) (memmap K) :=
  @lookup _ _ (memmap K) _.

#[global] Instance stackmap_lookup {K} : Lookup string (stack K) (stackmap K) :=
  @lookup _ _ (stackmap K) _.



Parameter InvalidMemAccessPtr :forall K, ptr K -> ptr K.
Parameter InvalidMemAccessInt :forall K, ptr K -> Z.
Parameter InvalidMemAccessCompound : forall K, ptr K  -> list (val K).
Parameter InvalidMemAccessPtrLab :forall K, ptr K -> labelname -> ptr K.
Parameter InvalidMemAccessIntLab :forall K, ptr K -> labelname -> Z.
Parameter InvalidMemAccessCompoundLab : forall K, ptr K -> labelname -> list (val K).
Parameter InvalidBlockLen : forall K, ptr K -> Z.
Parameter InvalidOffset : forall K, ptr K -> Z.
Parameter InvalidBaseaddr : forall K, ptr K -> ptr K.

Arguments InvalidMemAccessInt {_} _.
Arguments InvalidMemAccessPtr {_} _.
Arguments InvalidMemAccessCompound {_} _.
Arguments InvalidMemAccessIntLab {_} _.
Arguments InvalidMemAccessPtrLab {_} _.
Arguments InvalidMemAccessCompoundLab {_} _.
Arguments InvalidBlockLen {_} _.
Arguments InvalidOffset {_} _.
Arguments InvalidBaseaddr {_} _.

                  
(*Function that evaluates ACSL terms*)
Definition convertInvalid `{Env K} (p : ptr K) : val_term K :=
  match p with
  | NULL pt => match pt with
               | TType (TBase (TInt _)) => VInteger (InvalidMemAccessInt p)
               | TType (TBase (TPtr _)) => ValC (VBase (VPtr (InvalidMemAccessPtr p)))
               | TType (TCompound Struct_kind t) => ValC (VStruct t (InvalidMemAccessCompound p))
               | TType (TCompound Union_kind t) => ValC (VUnionAll t (InvalidMemAccessCompound p))
               | _ => VInteger 0
               end
  | Ptr a => match (addr_type a) with
             | TType (TBase (TInt _)) => VInteger (InvalidMemAccessInt p)
             | TType (TBase (TPtr _)) => ValC (VBase (VPtr (InvalidMemAccessPtr p)))
             | TType (TCompound Struct_kind t) => ValC (VStruct t (InvalidMemAccessCompound p))
             | TType (TCompound Union_kind t) => ValC (VUnionAll t (InvalidMemAccessCompound p))
             | _ => VInteger 0
             end
  | _=> VInteger 0
  end.


(*Function that evaluates ACSL terms*)
Definition convertInvalidLab `{Env K} (p : ptr K) (l : labelname): val_term K :=
  match p with
  | NULL pt => match pt with
               | TType (TBase (TInt _)) => VInteger (InvalidMemAccessIntLab p l)
               | TType (TBase (TPtr _)) => ValC (VBase (VPtr (InvalidMemAccessPtrLab p l)))
               | TType (TCompound Struct_kind t) => ValC (VStruct t (InvalidMemAccessCompoundLab p l))
               | TType (TCompound Union_kind t) => ValC (VUnionAll t (InvalidMemAccessCompoundLab p l))
               | _ => VInteger 0
               end
  | Ptr a => match (addr_type a) with
             | TType (TBase (TInt _)) => VInteger (InvalidMemAccessIntLab p l)
             | TType (TBase (TPtr _)) => ValC (VBase (VPtr (InvalidMemAccessPtrLab p l)))
             | TType (TCompound Struct_kind t) => ValC (VStruct t (InvalidMemAccessCompoundLab p l))
             | TType (TCompound Union_kind t) => ValC (VUnionAll t (InvalidMemAccessCompoundLab p l))
             | _ => VInteger 0
             end
  | _=> VInteger 0
  end.

Check _ ≫= maybe inl.
Fixpoint term_eval `{Env K} (t : term K) (en : env K)
  (rho : stack K) (rhomap : stringmap (stack K))(m : mem K) (l :labelname)
  (labmap : stringmap (mem K)) : option (lrval_term K) :=
  match t with
  | TVar x  => let rhol :=
                 match l with
                 | "Here" => Some rho
                 |_ =>  stackmap_lookup l rhomap
                 end in
               match rhol with
               | Some sta =>
                   '(o,τ) ← sta !! x;
Some (inl (Ptr (addr_top o τ)))
| None => None
end
| TVal v => Some v
| TRtoL t1 => v ← term_eval t1 en rho rhomap m l labmap ≫= maybe inr;
let vc := match v with
          | ValC v1 => Some v1
          | _ => None
          end
in
match vc with
| Some v1 =>
    p ← maybe (VBase ∘ VPtr)  v1;
guard (ptr_alive' m p);
Some (inl p)
| _ => None
end
| TRofL t => p ← term_eval t en rho rhomap m l labmap ≫= maybe inl;
Some (inr (ValC (ptrV p)))
| TBinOp op t1 t2 =>  v1 ← term_eval t1 en rho rhomap m l labmap ≫= maybe inr;
v2 ← term_eval t2 en rho rhomap m l labmap ≫= maybe inr;
Some (inr (tval_binop en op v1 v2))
     
| TLoad t => p ← term_eval t en rho rhomap m l labmap ≫= maybe (inl);
let newmopt := match l with
               | "Here" => Some m
               | _ => lmap_lookup l labmap
               end in
match newmopt with
| Some newm =>
    let pi := match p with
              | NULL _ => Some (inr (convertInvalid p))
              | Ptr a => let v :=  newm !!{en} a in
                         match v with
                         | Some vc => match vc with
                                      | VBase(VInt _ x) => Some (inr (VInteger x))
                                      | _ => Some (inr (ValC vc))
                                      end
                         | None => Some (inr (convertInvalid p))
                         end   
              | _ => None
              end
    in pi
| None => Some (inr  (convertInvalidLab p l))
end
     
| TUnOp op t => v ← term_eval t en rho rhomap m l labmap ≫= maybe inr;
Some (inr (tval_unop op v))
     
| TEltL t rs =>  a ← term_eval t en rho rhomap m l labmap ≫= maybe (inl ∘ Ptr);
guard (addr_strict en a);
Some (inl (Ptr (addr_elt en rs a)))
     
| TEltR t rs => v ← term_eval t en rho rhomap m l labmap ≫= maybe (inr);
let vc := match v with
          |ValC v1 => Some v1
          | _ => None
          end
in
match vc with
| Some vc' =>
    v' ← vc' !!{en} rs;
Some (inr  (ValC v'))
| _ => None
end

| TBaseAddr t => v ← term_eval t en rho rhomap m l labmap ≫= maybe inr;
    let vc := match v with
              | ValC v1 => Some v1
              | _ => None      
              end
    in
    match vc with
    | Some v1 => p ← maybe (VBase ∘ VPtr)  v1;
    guard (ptr_alive' m p);
        match p with
        | Ptr a => Some (inl (Ptr (addr_top (addr_index a)(addr_type_object a))))
        | NULL _ => Some (inl (InvalidBaseaddr p))
        | _ => None
        end
    | _ => None
    end

| TOffset t => v ← term_eval t en rho rhomap m l labmap ≫= maybe inr;
    let vc := match v with
              | ValC v1 => Some v1
              | _ => None
              end
    in 
    match vc with
    | Some v1 => p ← maybe (VBase ∘ VPtr)  v1;
    guard (ptr_alive' m p);
        match p with
        | Ptr a => Some (inr (ValC(VBase(VInt (IntType Signed ptr_rank)
                                           ((addr_object_offset en a)/char_bits)))))
        | NULL _ => Some (inr (ValC (VBase (VInt (IntType Signed ptr_rank)
                                              (InvalidOffset p )))))
        | _ => None
        end
    | _ => None
end

| TBlckLen t => v ← term_eval t en rho rhomap m l labmap ≫= maybe inr;
    let vc := match v with
              | ValC v1 => Some v1
              | _ => None
              end
    in
    match vc with
    | Some v1 => p ← maybe (VBase ∘ VPtr)  v1;
    guard (ptr_alive' m p);
        match p with
            | Ptr a => Some (inr (ValC(VBase (VInt (IntType Signed ptr_rank)
                                                (size_of en (addr_type_object a))))))
            | NULL _ => Some (inr (ValC (VBase (VInt (IntType Signed ptr_rank)
                                                  (InvalidBlockLen p)))))
            | _ => None
        end
    | _ => None
end

| TAt t lab => term_eval t en rho rhomap m lab labmap

end.



Definition term_eval_right `{Env K} (t: term K) (en : env K)
  (rho : stack K) (rhomap : stringmap (stack K)) (m : mem K)
  (l : labelname) (labmap : stringmap (mem K)) : option(val_term K) :=
  term_eval t en rho rhomap m l labmap ≫= maybe inr.

Definition term_eval_left `{Env K} (t: term K) (en : env K)
  (rho : stack K) (rhomap : stringmap (stack K)) (m : mem K)
  (l : labelname) (labmap : stringmap (mem K)) : option (ptr K) :=
  term_eval t en rho rhomap m l labmap ≫= maybe inl.
