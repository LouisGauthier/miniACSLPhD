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
