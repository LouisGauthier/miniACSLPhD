Require Export terms type_system operations_term predicates term_eval.
Local Open Scope pred_scope.
Require Import List String stringmap.
Import ListNotations.
Local Coercion Z.of_nat: nat >-> Z.

(*Indutive to know wether a list of values is initialized or not*)
Inductive init_val_list `{Env K} : list (val K) -> Prop :=
| init_list_empty : init_val_list []
| init_list : forall (lv tlv: list (val K)) (hlv : val K),
    lv = hlv::tlv ->
    init_val hlv ->
    init_val_list tlv ->
    init_val_list lv
with
(*Indutive to know wether a list of bits is initialized or not*)
  init_bit_list `{Env K} : list (bit K) -> Prop :=
  | init_bits_empty : init_bit_list []
|init_bits : forall (lb tlb : list (bit K)) (hlb : bit K)(b : bool)(p : ptr_bit K),
    lb = hlb::tlb ->
    hlb =(BBit b) \/ hlb = BPtr p ->
    init_bit_list tlb ->
    init_bit_list lb
(*Inductive to know wether a value is initialized or not*)
  with init_val `{Env K} : val K -> Prop :=
| initVBase : forall (en : Env K) (v : val K) (bt : base_type K) (vb : base_val K),
    v = VBase vb ->
    bt = type_of vb ->
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

(*Function to define the validity of a pointer*)
Definition valid_pointer `{Env K} (en : env K) (p : ptr K) (m : mem K) : Prop :=
  (ptr_alive' m p) /\
    match p with
    | Ptr a =>
        match (addr_type a) with
        | TType nty =>
            ( (0<= (addr_object_offset en a)/char_bits) /\
                (((addr_object_offset en a)/char_bits) + size_of en nty) <= size_of en (addr_type_object a) )
        | _ => False
        end
    | _ => False
    end.

(*Function to translate a miniACSL predicate to a Rocq Prop*)
Fixpoint predicate_to_prop `{Env K} (p : predic K ) (en : env K)
  (rho : stack K) (rhomap : stringmap (stack K)) (m : mem K) (l : labelname) (labmap : stringmap (mem K)): Prop :=
  match p with
  | PTrue => True
  | PFalse => False
  | PRelOp op t1 t2  => let v1 := term_eval_right t1 en rho rhomap m l labmap in
                        let v2 := term_eval_right t2 en rho rhomap m l labmap in
                        match v1,v2 with
                        | Some(val1), Some(val2) => comp_valt op en val1 val2
                        | _,_ => False
                        end
  | POr p1 p2 =>  let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
                  let prop2 := predicate_to_prop p2 en rho rhomap m l labmap in
                  prop1 \/ prop2
  | PAnd p1 p2 => let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
                  let prop2 := predicate_to_prop p2 en rho rhomap m l labmap in
                   prop1 /\prop2
  | PImpl p1 p2 => let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
                   let prop2 := predicate_to_prop p2 en rho rhomap m l labmap in
                   prop1 -> prop2
  | PNot p1 => let prop1 := predicate_to_prop p1 en rho rhomap m l labmap in
               ~prop1 
  | PValid t1 => let v1 := term_eval_right t1 en rho rhomap m l labmap in
                 match v1 with
                 | Some (val1) => match val1 with
                                  | ValC (VBase (VPtr p)) => valid_pointer en p m
                                      
                                  | _ => False
                                  end
                 | _ => False
                 end
                   
  (* Initialized *)
  | PInit t1 => let v1 := term_eval_right t1 en rho rhomap m l labmap in
                  match v1 with
                  |Some (val1) => match val1 with
                                  | ValC (VBase (VPtr p)) => valid_pointer en p m /\
                                                      (match p with
                                                      | NULL _ => False
                                                      | Ptr a => let vad := m !!{en} a in
                                                                 match vad with
                                                                 | Some(vaddrok) => init_val vaddrok
                                                                 | _ => False
                                                                 end
                                                      | FunPtr _ _ _ => False
                                                                 
                                                      end)
                                  | _ => False
                                  end
                  | None => False
                  end
  end.


Context `{Env K}.

(*Proof that initialized -> valid*)
Lemma initImpValid t en rho rhomap l labmap m :
  predicate_to_prop (PInit t) en rho rhomap m l labmap ->
  predicate_to_prop (PValid t) en rho rhomap m l labmap.
Proof.
  intro.
  unfold predicate_to_prop in H0.
  unfold predicate_to_prop.
  destruct (term_eval_right t en rho rhomap m l labmap).
  destruct v.
  destruct v.
  destruct b.
  assumption.
  assumption.
  assumption.
  destruct H0.
  all : assumption.
  
Qed.


(*Proof that valid -> pointer in proper bounds*)
Lemma offsetbound2 t a en rho rhomap l labmap m nty :
  predicate_to_prop (PValid t) en rho rhomap m l labmap /\
    term_eval_right t en rho rhomap m l labmap = Some (ValC (VBase (VPtr (Ptr a)))) /\
    addr_type a = TType nty -> 
  (0<=(addr_object_offset en a)/char_bits) /\
    (((addr_object_offset en a)/char_bits) + size_of en nty) <= size_of en (addr_type_object a).
  Proof.
    intros.
    destruct H0. destruct H1.
    unfold predicate_to_prop in H0.
    destruct (term_eval_right t en rho rhomap m l labmap).
    destruct v.
    destruct v.
    destruct b. discriminate. discriminate.    
    discriminate.
    injection H1. intro. unfold valid_pointer in H0. destruct H0. destruct p.
    discriminate. injection H3.
    intro.
    rewrite -> H5 in H4.
    destruct (addr_type a).
    injection H2.
    intro. rewrite <- H6.
    assumption.
    all: discriminate.
  Qed.
