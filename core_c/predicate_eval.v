Require Export terms type_system operations_term predicates term_eval.
Local Open Scope pred_scope.
Require Import List String stringmap.
Import ListNotations.
Local Coercion Z.of_nat: nat >-> Z.

(* Predicate to know wether a value is initialized or not *)
Inductive init_val_list `{Env K} : list (val K) -> Prop :=
| init_list : forall (lv tlv: list (val K)) (hlv : val K),
    lv = hlv::tlv ->
    init_val hlv ->
    init_val_list lv
with
  init_bit_list `{Env K} : list (bit K) -> Prop :=
|init_bits : forall (lb tlb : list (bit K)) (hlb : bit K)(b : bool)(p : ptr_bit K),
    lb = hlb::tlb ->
    hlb =(BBit b) \/ hlb = BPtr p ->
    init_bit_list tlb ->
    init_bit_list lb
  with init_val `{Env K} : val K -> Prop :=
| initVBase : forall (en : Env K) (v : val K) (bt : base_type K) (vb : base_val K),
    v = VBase vb ->
    vb <> VIndet bt ->
    init_val v
| initVStruct : forall (en : Env K) (v : val K) (t : tag) (lval : list (val K)),
    v = VStruct t lval ->
    init_val_list lval ->
    init_val v
| initVUnion : forall (en : Env K) (t : tag) (n : nat) (v vu : val K),
    v = VUnion t n vu ->
    init_val vu ->
    init_val v
| initVUnionAll : forall (en : env K)(t : tag) (lval : list (val K)) (v : val K) (vecb : list (bit K)),
    v = VUnionAll t lval ->
    val_flatten en v = vecb ->
    init_bit_list vecb ->
    init_val v.

(* Evaluation of ACSL predicates : Translatio from predicates to Prop*)
Fixpoint predicate_to_prop `{Env K} (p : predic K ) (en : env K)
  (rho : stack K) (rhomap : stringmap (stack K)) (m : mem K) (l : labelname) (labmap : stringmap (mem K)): option Prop :=
  match p with
  | PTrue => Some True
  | PFalse => Some False
  | PAt p1 =>  predicate_to_prop p1 en rho rhomap m l labmap
  | PRelOp op t1 t2  => let v1 := term_eval_right t1 en rho rhomap m l labmap in
                        let v2 := term_eval_right t2 en rho rhomap m l labmap in
                        match v1,v2 with
                        | Some(val1), Some(val2) => Some (comp_valt op en val1 val2) 
                        | _,_ => None
                        end
  | POr p1 p2 =>  let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
                  let prop2 := predicate_to_prop p2 en rho rhomap m l labmap in
                  match prop1,prop2 with
                  | Some p1', Some p2' => Some (p1' \/ p2')
                  | _,_ => None
                  end
  | PAnd p1 p2 => let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
                  let prop2 := predicate_to_prop p2 en rho rhomap m l labmap in
                  match prop1,prop2 with
                  | Some p1', Some p2' => Some (p1' /\ p2')
                  | _,_ => None
                  end
  | PImpl p1 p2 => let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
                   let prop2 := predicate_to_prop p2 en rho rhomap m l labmap in
                   match prop1,prop2 with
                   | Some p1', Some p2' => Some (p1' -> p2')
                   | _,_ => None
                   end
  | PNot p1 => let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
               match prop1 with
               | Some p1' => Some (~p1')
               | _ => None
               end
  | PValid t1 => let v1 := term_eval_right t1 en rho rhomap m l labmap in
                 match v1 with
                 | Some (val1) => match val1 with
                                  | ValC (VBase (VPtr p)) => match p with
                                                             | NULL _ => Some False
                                                             | Ptr a => Some(ptr_alive' m p)
                                                             | FunPtr _ _ _ => Some True
                                                      end
                                  | _ => None
                                  end
                 | _ => None
                 end
                   
  (* Initialized *)
  | PInit t1 => let v1 := term_eval_right t1 en rho rhomap m l labmap in
                  match v1 with
                  |Some (val1) => match val1 with
                                  | ValC (VBase (VPtr p)) => match p with
                                                      | NULL _ => Some False
                                                      | Ptr a => let vad := m !!{en} a in
                                                                 match vad with
                                                                 | Some(vaddrok) => Some(init_val vaddrok)
                                                                 | _ => None
                                                                 end
                                                      | FunPtr _ _ _ => Some True
                                                                 
                                                      end
                                  | _ => None
                                  end
                  | None => None
                  end
  end.


