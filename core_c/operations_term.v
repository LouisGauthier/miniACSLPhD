Require Export memory_map values.
Require Import pointer_casts.
Require Export expressions type_system fragmented.
Require Import Arith.
Local Open Scope ctype_scope.
Local Open Scope Z_scope.
Local Open Scope int_type_scope.
Local Coercion Z.of_nat: nat >-> Z.

Section operations_definitions2.
  Context `{Env K}.
  (* ACSL values *)
  Inductive val_term (K : iType) : iType :=
  | ValC : val K -> val_term K
  | VInteger : Z -> val_term K.
  
  Arguments ValC {_} _.
  Arguments VInteger {_} _.
  
  (* Underspecified constructor for division by zero *)
  Parameter divZ : Z -> Z.
  
  
  Inductive tbinop :=
  | TArithOp : arithop -> tbinop
  | TShiftOp : shiftop -> tbinop
  | TBitOp : bitop -> tbinop.
  
  Definition tbin_to_bin (op : tbinop):=
    match op with
    | TArithOp opa => ArithOp opa
    | TShiftOp ops => ShiftOp ops 
    | TBitOp opb => BitOp opb
    end.
  
  (* Arithop for integers with the divZ constructor if needed *)
  Definition arithopZ (op : arithop)(x y : Z) : Z :=
    match op, y with
    | DivOp, 0 => divZ x
    | DivOp, _ => x/y
    | PlusOp, _=> x+y
    | MinusOp, _ => x-y
    | MultOp, _ => x*y
    | ModOp, _ => x mod y
    end.

  
  Inductive tunop :=
  | TNegOp : tunop
  | TComplOp : tunop.

  Definition tun_to_un (op : tunop):=
    match op with
    | TNegOp  => NegOp 
    | TComplOp  => ComplOp 
    end.

  Definition tval_unop (op : tunop) (v : val_term K) : val_term K :=
    match v, op with
    | VInteger n, TNegOp => VInteger (-n)
    | ValC v,_ => ValC(val_unop (tun_to_un op) v)
    | _,_ => v
    end.

  
  (* New arithop function which takes the divZ constructor when there is a division by zero *)
  Definition new_arithop (op : arithop)(x y : Z) (τi1 τi2 : int_type K) : Z  :=
    match op, sign τi1, y with
    | DivOp, _, 0 => divZ x
    | _, _, _ => int_arithop op x τi1 y τi2
    end.

  (* New operation on int which take divide by zero in account *)
  Definition new_int_binop (op : arithop) (x1 x2 : Z) (τi1 τi2 : int_type K) : Z :=
     new_arithop op x1 x2 τi1 τi2
    .
  
  (* New operation on base_val which take divide by zero in account *)
  Definition new_base_val_binop (en : env K) (op : binop) (v1 v2 : base_val K): base_val K :=
    match v1, v2, op with
    | VInt τi1 x1, VInt τi2 x2, ArithOp aop =>
        VInt (int_binop_type_of op τi1 τi2) (new_int_binop aop x1 x2 τi1 τi2)
    |_,_, _ => base_val_binop en op v1 v2
    end.

  (* New operation on c values which take divide by zero in account *)
  Definition new_val_binop (en : env K) (op : binop) (v1 v2 : val K) : val K :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => VBase (new_base_val_binop en op vb1 vb2)
    | _,_ => val_binop en op v1 v2
    end.
  
  (*Last operation to sumup all modifications : arithmetic between C int and acsl integer 
    (convert
    to acsl integer) *)
  Definition tval_binop (en : env K) (op : tbinop) (vt1 vt2 : val_term K): val_term K :=
    match vt1,vt2,op with
    | VInteger n1, VInteger n2, TArithOp aop => VInteger (arithopZ aop n1 n2)
    | VInteger n1, ValC (VBase (VInt t n2)), TArithOp aop => VInteger (arithopZ aop n1 n2)
    | ValC (VBase (VInt t n1)), VInteger n2, TArithOp aop => VInteger (arithopZ aop n1 n2)
    | ValC v1, ValC v2, _ => ValC (new_val_binop en (tbin_to_bin op) v1 v2)
    | VInteger n1, ValC(ptrV p), TArithOp aop => ValC (ptrV (ptr_plus en n1 p))
    | ValC(ptrV p), VInteger n1, TArithOp aop => ValC (ptrV (ptr_plus en n1 p))
    | _,_,_ => vt1
    end.



  (* Inductive predicate used to know if a value and a list of values can be compared (predicate used in proofs) *)
  Inductive comparable : val K -> Prop :=
  | cmp_base : forall b, comparable (VBase b)
  | cmp_struct : forall t l, comparable_list l -> comparable (VStruct t l)
  | cmp_union : forall v i t, comparable v -> comparable (VUnion t i v)
  | cmp_unionall : forall l t, comparable_list l -> comparable (VUnionAll t l)
  with
    comparable_list : list (val K) -> Prop :=
  | cmp_nil : comparable_list []
  | cmp_cons : forall v l, comparable v -> comparable_list l -> comparable_list (v::l).

   
   (* Equality between C values *)
  Inductive eq_val : env K -> val K -> val K -> mem K -> Prop :=
  | eq_base : forall(en : env K) (vb1 vb2 : base_val K)(m : mem K),
      base_val_binop_ok en m (CompOp EqOp) vb1 vb2 ->
      new_base_val_binop en (CompOp EqOp) vb1 vb2 = VInt sintT 1 ->
      eq_val en (VBase vb1) (VBase vb2) m
  | eq_struct : forall (en : env K)
                      (lval1 lval2 : list (val K)) (tag1 tag2 : tag)(m : mem K),
      eq_list  en lval1 lval2 m
      -> eq_val en (VStruct tag1 lval1) (VStruct tag2 lval2) m
  | eq_union1 : forall (en : env K)(v1 v2 vu1 vu2 : val K)(tag1 tag2 : tag)(n1 n2 : nat)(m : mem K),
      v1 = VUnion tag1 n1 vu1 ->
      v2 = VUnion tag2 n2 vu2  ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2 m
  | eq_union2 : forall (en : env K) (v1 v2 vu1 : val K)
                       (tag1 tag2 : tag)(n1 : nat) (lval2 : list (val K))(m : mem K),
      v1 = VUnion tag1 n1 vu1 ->
      v2 = VUnionAll tag2 lval2 ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2 m
  | eq_union3 : forall (en : env K) (v1 v2 vu2 : val K)
                       (tag1 tag2 : tag)(n2 : nat) (lval1 : list (val K))(m : mem K),
      v2 = VUnion tag2 n2 vu2 ->
      v1 = VUnionAll tag1 lval1 ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2 m
  | eq_union4 : forall (en : env K) (v1 v2 : val K)
                       (tag1 tag2 : tag) (lval1 lval2 : list (val K))( m : mem K),
      v2 = VUnionAll tag2 lval2 ->
      v1 = VUnionAll tag1 lval1 ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2 m
  | eq_same : forall (en : env K)(v1 v2 : val K)(m : mem K),
      v1 = v2 ->
      eq_val en v1 v2 m
             
  (* Equality between list of C values *)
  with eq_list : env K -> list (val K) -> list (val K) -> mem K -> Prop :=
  | eq_list_empty : forall (en : env K) (m : mem K) ,
      eq_list  en [] [] m
  | eq_list_cons : forall (en : env K) (v1 v2 : val K) (lvq1 lvq2: list (val K))(m : mem K),
      eq_val en v1 v2 m ->
      eq_list en lvq1 lvq2 m ->
      eq_list en (v1::lvq1) (v2::lvq2) m
  | eq_list_same : forall (en : env K) (l : list (val K))(m : mem K),
      eq_list en l l m.
  
  (* Comparison of values *)
  Inductive comp_val : compop -> env K -> val K -> val K -> Prop :=
  | eq_value : forall (en : env K)(v1 v2 : val K)(m : mem K),
      eq_val en v1 v2 m  -> comp_val EqOp en v1 v2
  | comp_other : forall (op : compop)(en : env K) (v1 v2 : val K),
      new_val_binop en (CompOp op) v1 v2 = VBase (VInt sintT 1) ->
      comp_val op en v1 v2.

  (* Equality between ACSL values *)
  Inductive eq_valt : env K -> val_term K -> val_term K -> mem K-> Prop :=
  | eq_valc : forall (en : env K)(v1 v2 : val K)(m : mem K),
      eq_val en v1 v2 m -> eq_valt en (ValC v1) (ValC v2) m
  | eq_integer : forall (en : env K) (x y : Z)(m : mem K),
      x = y -> eq_valt en (VInteger x) (VInteger y) m
  | eq_integerInt : forall (en : env K) (x y : Z) (t : int_type K)(m : mem K),
      x = y -> eq_valt en (VInteger x) (ValC (VBase (VInt t y))) m
  | eq_intInteger : forall (en : env K) (x y : Z) (t : int_type K)(m : mem K),
      x = y -> eq_valt en (ValC (VBase (VInt t x))) (VInteger y) m
  | eq_samet : forall (en : env K) (v : val_term K)(m : mem K),
      eq_valt en v v m.
      
  (* Comparison of integers *)
  Inductive comp_int : compop -> Z -> Z -> Prop :=
  | eq_int : forall (x y: Z) , x = y -> comp_int EqOp x y
  | lt_int : forall (x y : Z), x < y -> comp_int LtOp x y
  | le_int : forall (x y : Z), x <= y -> comp_int LtOp x y.
  
 (* Comparison of ACSL values *)
  Inductive comp_valt : compop -> env K -> val_term K -> val_term K -> Prop :=
  | comp_valc : forall (en : env K)(v1 v2 : val K)(op : compop),
      comp_val op en v1 v2 -> comp_valt op en (ValC v1) (ValC v2)
  | eq_valuet : forall (en : env K)(v1 v2 : val_term K)(m : mem K),
      eq_valt en v1 v2 m -> comp_valt EqOp en v1 v2
  | comp_valInt : forall (en : env K)(x y : Z)(op : compop),
      comp_int op x y -> comp_valt op en (VInteger x) (VInteger y)
  | comp_intInteger : forall (en : env K)(x y : Z)(op : compop)(ty : int_type K),
      comp_int op x y -> comp_valt op en (ValC (VBase (VInt ty x))) (VInteger y)
  | comp_integerInt : forall (en : env K)(x y : Z)(op : compop)(ty : int_type K),
      comp_int op x y -> comp_valt op en (VInteger x) (ValC (VBase (VInt ty y))). 
  
    
  Lemma comp_valt_test : forall en, ~(comp_valt EqOp en (VInteger 8) (VInteger 0))/\
                                      (comp_valt EqOp en (VInteger (divZ 4)) (VInteger (divZ 4))).
  Proof.
    intros.
    split.
    intro excluded_middle.
    inversion excluded_middle.
    inversion H0.
    discriminate.
    inversion H4.
    discriminate.
    constructor.
    constructor.
    reflexivity.
  Qed.
  
  (* Assume that equality furnished in CH2O is symmetric*)
  Axiom eq_bval_sym : forall(v1 v2 : base_val K)(en : env K)(m : mem K),
      base_val_binop_ok en m (CompOp EqOp) v1 v2 ->
      base_val_binop en (CompOp EqOp) v1 v2 = (intV{sintT} 1)%B ->
      base_val_binop en (CompOp EqOp) v2 v1 = (intV{sintT} 1)%B.
  

  (* Proof that equality in CH2O with our modification is symetric *)
  Lemma eq_val_sym : forall(v1 v2 : base_val K)(en : env K)(m : mem K),
      base_val_binop_ok en m (CompOp EqOp) v1 v2 ->
      new_base_val_binop en (CompOp EqOp) v1 v2 = (intV{sintT} 1)%B ->
      new_base_val_binop en (CompOp EqOp) v2 v1 = (intV{sintT} 1)%B.
    Proof.
      intros.
      destruct v1, v2.
      all : try unfold base_val_binop_ok in H0. all : try contradiction.
      unfold new_base_val_binop.
      unfold new_base_val_binop in H1.
      apply (eq_bval_sym (intV{i} z) (intV{i0} z0) en m).
      unfold base_val_binop_ok. assumption.
      assumption.
      unfold new_base_val_binop.
      unfold new_base_val_binop in H1.
      apply (eq_bval_sym (ptrV p) (ptrV p0) en m). unfold base_val_binop_ok.
      assumption. assumption.
    Qed.


    
  (* Assume that equality furnished in CH2O is transitive *)
    Axiom eq_bval_trans : forall (v1 v2 v3 : base_val K)(en : env K)(m : mem K),
      base_val_binop_ok en m (CompOp EqOp) v1 v2 ->
      base_val_binop_ok en m (CompOp EqOp) v2 v3 ->
      base_val_binop en (CompOp EqOp) v1 v2 = (intV{sintT} 1)%B ->
      base_val_binop en (CompOp EqOp) v2 v3 = (intV{sintT} 1)%B ->
      base_val_binop en (CompOp EqOp) v1 v3 = (intV{sintT} 1)%B.
   
  (* Proof that equality in CH2O with our modification is transitive *)
    Lemma eq_val_trans : forall (v1 v2 v3 : base_val K)(en : env K)(m : mem K),
      base_val_binop_ok en m (CompOp EqOp) v1 v2 ->
      base_val_binop_ok en m (CompOp EqOp) v2 v3 ->
      new_base_val_binop en (CompOp EqOp) v1 v2 = (intV{sintT} 1)%B ->
      new_base_val_binop en (CompOp EqOp) v2 v3 = (intV{sintT} 1)%B ->
      new_base_val_binop en (CompOp EqOp) v1 v3 = (intV{sintT} 1)%B.

    Proof.
      intros.
      destruct v1, v2, v3.
      all : try unfold base_val_binop_ok in H0, H1. all : try contradiction.
      unfold new_base_val_binop in H2, H3.
      unfold new_base_val_binop.
      apply (eq_bval_trans (intV{i} z) (intV{i0} z0) (intV{i1} z1) en m).
      all : try unfold base_val_binop_ok. all : try assumption.
      unfold new_base_val_binop in H2, H3.
      unfold new_base_val_binop.
      apply (eq_bval_trans (ptrV p) (ptrV p0) (ptrV p1) en m).
      all : try unfold base_val_binop_ok.
      all : try assumption.
    Qed.

    (*Assume that the comparison condition is symetric*)
    Axiom eq_base_val_ok_sym : forall en m vb1 vb2,
      base_val_binop_ok en m (CompOp EqOp) vb1 vb2 -> base_val_binop_ok en m (CompOp EqOp) vb2 vb1.
    (*Assume that the comparison condtion is transitive*)
  Axiom eq_base_val_ok_trans : forall en m vb1 vb2 vb3,
      base_val_binop_ok en m (CompOp EqOp) vb1 vb2 ->
      base_val_binop_ok en m (CompOp EqOp) vb2 vb3 ->
      base_val_binop_ok en m (CompOp EqOp) vb1 vb3.
      
  (* Assume that comparing two C int is equivalent to compare their int part in their 
abstract representation*)
  Axiom int_cast_eq : forall (t t2 : int_type K) (en : env K) (x y : Z),
      new_base_val_binop en (CompOp EqOp) (VInt t x) (VInt t2 y) = (VInt sintT 1) <-> x = y.

  Section val_ind.


    Context (P : val K → Prop). (* The inductive property *)
    Context (HBase : ∀ b, P (VBase b)). (* VBase case *)
    Context (HStructNil :∀t, P (VStruct t [])). (* VStruct [] case *)
    Context (HStructCons : ∀ v l t t', P v → P (VStruct t l) → P (VStruct t' (v::l))).
    (* VStruct (v::l) case *)
    Context (HArrayNil :∀ t, P (VArray t [])). (* VArray [] case *)
    Context (HArrayCons : ∀ v l t, P v → P (VArray t l) → P (VArray t (v::l))).
    (* VStruct (v::l) case *)
    Context (HUnion :∀ t i v, P (VUnion t i v)).
    Context (HUnionAllNil : ∀ t, P (VUnionAll t [])).
    Context (HUnionAllCons : ∀ v l t t', P v -> P (VUnionAll t l) -> P(VUnionAll t' (v::l))).
    
    Fixpoint val_ind' v :=
      match v as v' return P v' with
      | VBase v => HBase v (* If v is a base, apply HBase *)
      | VStruct t l =>
          (* If it is a struct, do a recusion on the list
           We need to define the list function internally
           and not as a joined recursion else termination checker
           will complain *)
          let fix val_list_ind l := match l as l' return P (VStruct t l') with
                                    | [] => HStructNil t
                                    | v::l => HStructCons v l t _ (val_ind' v) (val_list_ind l)
                                    end in val_list_ind l
      | VArray t l =>
          let fix val_list_ind l := match l as l' return P (VArray t l') with
                                    | [] => HArrayNil t
                                    | v::l => HArrayCons v l t (val_ind' v) (val_list_ind l)
                                    end in val_list_ind l
      | VUnion t i v => HUnion t i v
      | VUnionAll t l =>
          let fix val_list_ind l := match l as l' return P (VUnionAll t l') with
                                    | [] => HUnionAllNil t
                                    | v::l => HUnionAllCons v l t _ (val_ind' v) (val_list_ind l)
                                    end in val_list_ind l
      end.
  End val_ind.
 
  
  Scheme eq_val_rec := Induction for eq_val Sort Prop
      with eq_list_rec := Induction for eq_list Sort Prop.

   
  (* Proof of reflexivity of the equality between ACSL values *)
  Lemma eq_valt_reflexive v en m : eq_valt en v v m.
  Proof.
    intros.
    apply eq_samet.
  Qed.
  
  (* Proof of symetry of the equality between C values *)
Lemma eq_val_symetric : forall(v1 v2 : val K)(en : env K)(m : mem K),
    eq_val en v1 v2 m -> eq_val en v2 v1 m.
  Proof.
    intros vl vr en m Hp.
    apply (eq_val_rec
             (λ en vl vr m (_:eq_val en vl vr m), eq_val en vr vl m)
             (λ en ll lr m (_: eq_list en ll lr m ), eq_list en lr ll m)).
    - intros. apply (eq_base en0 vb2 vb1). apply eq_base_val_ok_sym.
      assumption.
      apply (eq_val_sym vb1 vb2 en0 m0).
      assumption.
      assumption.
    - intros.  apply (eq_struct en0 lval2 lval1 tag2 tag1). assumption.
    - intros. apply (eq_union1 en0 v2 v1 vu2 vu1 tag2 tag1 n2 n1).
      assumption. assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_union3 en0 v2 v1 vu1 tag2 tag1 n1 lval2).
      assumption. assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_union2 en0 v2 v1 vu2 tag2 tag1 n2 lval1).
      assumption. assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_union4 en0 v2 v1 tag2 tag1 lval2 lval1). assumption.
      assumption. rewrite <- e1. reflexivity.
    - intros. apply eq_same. symmetry. assumption.
    - intros. apply (eq_list_empty).
    - intros. apply (eq_list_cons).
      assumption. assumption.
    - intros. apply eq_list_same.
    - intros. assumption.
  Qed.

  
  (* Proof of symetry between ACSL values *) 
  Lemma eq_val_term_symetric : forall(v1 v2 : val_term K)(en : env K)(m : mem K),
      eq_valt en v1 v2 m -> eq_valt en v2 v1 m.
    intros. inversion H0.
    apply (eq_valc en v3 v0 m).
    apply eq_val_symetric.
    assumption.
    apply eq_integer.
    symmetry.
    assumption.
    apply eq_intInteger. lia.
    apply eq_integerInt. lia.
    apply eq_samet.
  Qed.



  (* Proof of transitivity of equality between C values*)
  Lemma eq_val_transitive : forall (v1 v2 v3 : val K) (en : env K)(m : mem K),
      eq_val en v1 v2 m -> eq_val en v2 v3 m -> eq_val en v1 v3 m.
  Proof.
    intros v1 v2 v3 en m H12.
    apply (eq_val_rec
             (λ en v1 v2 m (_ : eq_val en v1 v2 m), ∀ v3, eq_val en v2 v3 m → eq_val en v1 v3 m)
             (λ en l1 l2 m (_ : eq_list en l1 l2 m), ∀ l3, eq_list en l2 l3 m → eq_list en l1 l3 m)).
    - intros en0 vb1 vb2 m2 Hok Hvb12 v3' H23. inversion H23. constructor.
      apply (eq_base_val_ok_trans en0 m2 vb1 vb2 vb3). assumption. assumption.
      apply (eq_val_trans vb1 vb2 vb3 en0 m2). assumption. assumption. assumption. assumption.
      discriminate. discriminate. discriminate. discriminate.  rewrite <- H0.
      apply eq_base. assumption. assumption.
    - intros en0 lval1 lval2 tag1 tag2 m2 Hl12 IHl v3' H23. inversion H23.
      constructor. apply IHl. assumption. discriminate. discriminate. discriminate. discriminate.
      rewrite <- H0. 
      apply eq_struct. assumption.
    - intros en0 v1' v2' vu1 vu2 tag1 tag2 n1 n2 m2 H1 H2 H12' v3' H23.
      inversion H23.
      rewrite -> H2 in H5. discriminate. rewrite -> H2 in H4. discriminate.
      apply (eq_union1 en0 v1' v3' vu1 vu3 tag1 tag3 n1 n3).
      assumption. assumption. rewrite -> H4 in H12'. assumption.
      apply (eq_union2 en0 v1' v3' vu1 tag1 tag3 n1 lval2). assumption. assumption.
      rewrite -> H4 in H12'. assumption.
      rewrite -> H2 in H3. discriminate.
      rewrite -> H2 in H3. discriminate.
      rewrite <- H0. apply (eq_union1 en0 v1' v2' vu1 vu2 tag1 tag2 n1 n2).
      assumption. assumption. assumption.
    - intros en0 v1' v2' vu1 tag1 tag2 n1 lval2 m2 H1 H2 H12' v3' H23. inversion H23. 
      rewrite <- H5 in H2. discriminate.
      rewrite <- H4 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      apply (eq_union1 en0 v1' v3' vu1 vu2 tag1 tag3 n1 n2).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      apply (eq_union2 en0 v1' v3' vu1 tag1 tag3 n1 lval0). assumption. assumption.
      rewrite <- H12' in H4. assumption.
      rewrite <- H0. apply (eq_union2 en0 v1' v2' vu1 tag1 tag2 n1 lval2).
      assumption. assumption. assumption.
    - intros en0 v1' v2' vu2 tag1 tag2 n2 lval1 m2 H2 H1 H12' v3' H23. inversion H23.
      rewrite <- H5 in H2. discriminate.
      rewrite <- H4 in H2. discriminate.
      apply (eq_union3 en0 v1' v3' vu0 tag1 tag3 n0 lval1).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      apply (eq_union4 en0 v1' v3' tag1 tag3 lval1 lval2).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      rewrite -> H2 in H3. discriminate.
      rewrite -> H2 in H3. discriminate.
      rewrite <- H0. apply (eq_union3 en0 v1' v2' vu2 tag1 tag2 n2 lval1 ).
      assumption. assumption. assumption.
    - intros en0 v1' v2' tag1 tag2 lval1 lval2 m2 H2 H1 H12' v3' H23. inversion H23.
      rewrite <- H5 in H2. discriminate.
      rewrite <- H4 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      apply (eq_union3 en0 v1' v3' vu2 tag1 tag3 n2 lval1).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      apply (eq_union4 en0 v1' v3' tag1 tag3 lval1 lval3).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      rewrite <- H0. apply (eq_union4 en0 v1' v2' tag1 tag2 lval1 lval2).
      assumption. assumption. assumption.
    - intros. inversion H0. rewrite e. rewrite <- H4.
      apply eq_base. assumption. assumption. rewrite e. rewrite <- H3.
      apply eq_struct. assumption.
      rewrite e. apply (eq_union1 en0 v4 v5 vu1 vu2 tag1 tag2 n1 n2).
      assumption. assumption. assumption.
      rewrite e. apply (eq_union2 en0 v4 v5 vu1 tag1 tag2 n1 lval2).
      assumption. assumption. assumption.
      rewrite e. apply (eq_union3 en0 v4 v5 vu2 tag1 tag2 n2 lval1).
      assumption. assumption. assumption.
      rewrite e. apply (eq_union4 en0 v4 v5 tag1 tag2 lval1 lval2).
      assumption. assumption. assumption.
      rewrite <- H1. rewrite e. apply eq_same. reflexivity.
    - intros. inversion H0. constructor. constructor.
    - intros en0 v0 v4 lv1 lv2 m2 H04 IH Hl12 IHl l3 Hv41213.
      inversion Hv41213. constructor.
      apply IH. assumption.
      apply IHl. assumption.
      constructor. assumption. assumption.
    - intros. assumption.
    - exact H12.
  Qed.

  
  (* Proof of transitivity of equality between ACSL values*)
  Lemma eq_valt_transitive : forall (v1 v2 v3 : val_term K) (en : env K)(m : mem K),
      eq_valt en v1 v2 m -> eq_valt en v2 v3 m -> eq_valt en v1 v3 m. 
    intros v1 v2 v3 en m H1 H2.
    inversion H1.
    inversion H2.
    
    + apply (eq_valc en v0 v6 m).
      rewrite <- H5 in H9.
      injection H9.
      intro.
      rewrite <- H12 in H0.
      apply (eq_val_transitive v0 v5 v6).
      assumption.
      assumption.
      
    + rewrite <- H9 in H5. discriminate.
    + rewrite <- H9 in H5. discriminate.
      
    + rewrite <- H9 in H5. injection H5. intro.
      destruct H0.
      destruct vb1. discriminate.
      discriminate.
      injection H12. intro. rewrite H14 in H13.
      apply int_cast_eq in H13.
      apply eq_intInteger.
      lia.
      unfold new_base_val_binop in H13.
      destruct vb2.
      unfold base_val_binop in H13. all : try discriminate.
      all : try rewrite -> H12 in H13. all : try discriminate.
      all : try rewrite H12 in H0. all : try discriminate.
      rewrite H0. 
      apply eq_intInteger.
      lia.
      
    + rewrite H9 in H5.
      rewrite <- H5.
      constructor.
      assumption.

    + destruct H2. discriminate.
      constructor.
      rewrite <- H4 in H1.
      injection H5.
      intro.
      lia.
      apply eq_integerInt.
      injection H5.
      lia.
      discriminate.
      rewrite <- H5.
      constructor.
      assumption.
      
    + destruct H2.
      destruct H2. injection H5. intro. rewrite <- H8 in H7.
      destruct vb2.
      all : try rewrite <- H8 in H2.
      all : try unfold base_val_binop_ok in H2.
      all : try contradiction.
      constructor.
      apply int_cast_eq in H7.
      lia.
      all : try discriminate.
      all : try rewrite H2 in H5. all : try discriminate.
      all : try rewrite H7 in H5. all : try discriminate.
      rewrite <- H5.
      constructor.
      assumption.
      rewrite <- H4 in H1.
      inversion H1.
      constructor.
      lia.
      rewrite <- H5.
      constructor. assumption.
     
    + destruct H2. discriminate. injection H5. intro. constructor. lia.
      injection H5. intro.  constructor. constructor. unfold base_val_binop_ok.
      unfold int_binop_ok. exact I. 
      unfold new_base_val_binop. apply (int_cast_eq t t0 en x y0). lia.
      discriminate. rewrite <- H5. constructor. assumption.
    + assumption.
  Qed.

  
End operations_definitions2.

