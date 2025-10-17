Require Export operations_term.
Local Open Scope Z_scope.
Local Coercion Z.of_nat: nat >-> Z.
Arguments ValC {_} _.
Arguments VInteger {_} _.
Context `{Env K}.

Lemma eq_paper : 5 + divZ 4 - 2 = 1 + divZ 4 + 2.
Proof.
  lia.
Qed.

 

Lemma int_pre_castneq : int_typed 5 (int_promote sintT ∪ int_promote sintT) ->
                        int_typed 1 (int_promote sintT ∪ int_promote sintT) ->
                        (int_pre_cast (int_promote sintT ∪ int_promote sintT) 1) <>
                          (int_pre_cast (int_promote sintT ∪ int_promote sintT) 5).

  intros.
  rewrite -> (int_pre_cast_self 5 (int_promote sintT ∪ int_promote sintT)) .
  rewrite -> (int_pre_cast_self 1 (int_promote sintT ∪ int_promote sintT)) .
  discriminate. assumption. assumption.
Qed.
Print env_type_env.
Print int_cast_spec.
Print IntEnvSpec.
Context `{IntEnvSpec K (H:=@env_type_env K H)}.
Lemma int_cast_self x τi : int_typed x τi → int_cast τi x = x.
Proof.
  Print int_cast_spec.
  intros; rewrite (int_cast_spec) by eauto using int_pre_cast_ok_self.
  eauto using int_pre_cast_self.
Qed.
Lemma int_castneq : int_typed 5 (int_promote sintT ∪ int_promote sintT) ->
                    int_typed 1 (int_promote sintT ∪ int_promote sintT) ->
                    (int_cast (int_promote sintT ∪ int_promote sintT) 1) <>
           (int_cast (int_promote sintT ∪ int_promote sintT) 5).
Proof.
  intros.
  rewrite -> (int_cast_self 5 (int_promote sintT ∪ int_promote sintT)).
  rewrite -> (int_cast_self 1 (int_promote sintT ∪ int_promote sintT)).
  discriminate. assumption. assumption.
Qed.

Lemma eq_paper3 : forall en t1, int_typed 5 (int_promote sintT ∪ int_promote sintT)->
                                int_typed 1 (int_promote sintT ∪ int_promote sintT)->
    ~(eq_val en (VStruct t1 [intV{sintT} 2; intV{sintT} 1])
        (VStruct t1 [intV{sintT} 2; intV{sintT} 5])) .
Proof.
  intros.
  intro excluded_middle.
  inversion excluded_middle.
  inversion H5.
  inversion H15.
  inversion H20.
  inversion H26.
  remember (decide
            (int_cast (int_promote sintT ∪ int_promote sintT) 1 =
               int_cast (int_promote sintT ∪ int_promote sintT) 5)) as e. induction e.
  all : try discriminate.
  apply int_castneq.
  assumption.
  assumption.
  simplify_equality'.
  Check intV{sintT} 2. Print IntEnvSpec. Print int_pre_cast. Print env_type_env. Check H1.
  apply a.
  Qed.

Print comp_valt.

 
Lemma eq_paper2 : forall en, ~(comp_valt EqOp en (VInteger 8) (VInteger 0))/\
                                         (comp_valt EqOp en (VInteger (divZ 4)) (VInteger (divZ 4))).
Proof.
  intros.
  split.
  intro excluded_middle.
  inversion excluded_middle.
  inversion H1.
  discriminate.  
  inversion H5.
  discriminate.
  apply eq_valuet.
  constructor.
  reflexivity.
Qed.
