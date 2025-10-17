Require Export operations smallstep statementsAcsl.
Require Import String stringmap.

Definition memmap (K : iType) := stringmap (mem K).

Definition stackmap (K : iType) := stringmap (stack K).

Notation funacslenv K := (stringmap (stmtacsl K)).

#[global] Instance lmap_insert {K} :
  Insert string (mem K) (memmap K) := λ l m lm,
    <[l:=m]>lm.

#[global] Instance stackmap_insert {K} :
  Insert string (stack K) (stackmap K) := λ l m lm,
    <[l:=m]>lm.

#[global] Instance funacslenv_lookup {K} : Lookup string (stmtacsl K) (funacslenv K) :=
  @lookup _ _ (funacslenv K) _.

#[global] Instance stmtacsl_cases {K} : Cases (stmtacsl K) :=
  fix go s := let _ : Cases _ := @go in
  match s with
  | SADo _ | SASkip | SAGoto _ | SAThrow _ | SAReturn _ | SALabel _ => ∅
  | SACase mz => {[ mz ]}
  | SACatch s | SALocal _ s | SALoop s => cases s
  | SAComp s1 s2 | SAIf _ s1 s2 => cases s1 ∪ cases s2
  | SASwitch _ _ => ∅
  | SAAssert _ => ∅
  end.

#[global] Instance stmtacsl_labels {K} : Labels (stmtacsl K) :=
  fix go s := let _ : Labels _ := @go in
  match s with
  | SADo _ | SASkip | SAGoto _ | SAThrow _ | SAReturn _ | SACase _ => ∅
  | SALabel l => {[ l ]}
  | SACatch s | SALocal _ s | SALoop s | SASwitch _ s => labels s
  | SAComp s1 s2 | SAIf _ s1 s2 => labels s1 ∪ labels s2
  | SAAssert _ => ∅
  end.

#[global] Instance asctx_item_subst {K} :
    Subst (asctx_item K) (stmtacsl K) (stmtacsl K) := λ Es s,
  match Es with
  | ACatch => SACatch s
  | ACompL s2 => SAComp s s2
  | ACompR s1 => SAComp s1 s
  | ALoop => SALoop s
  | AIfL e s2 => SAIf e s s2
  | AIfR e s1 => SAIf e s1 s
  | ASwitch e => SASwitch e s
  end.

#[global] Instance maybe_ASwitch {K} : Maybe (@ASwitch K) := λ Es,
    match Es with ASwitch e => Some e | _ => None end.


Fixpoint locals2 (K : iType) (k : acslctx K) {struct k} : stack K :=
  match k with
  | ALocal o τ :: k0 => (o, τ) :: locals2 K k0
  | AStmt _ :: k0 | AExpr _ _ :: k0 => locals2 K k0
  | AParams _ oτs :: _ => oτs
  | _ => []
  end.
Arguments locals2 {_} _.

Fixpoint stmtacsl_to_stmt `{Env K} (sa : stmtacsl K) :=
  match sa with
  | SADo e => SDo e
  | SASkip => SSkip
  | SAGoto l => SGoto l
  | SAThrow n => SThrow n
  | SAReturn e => SReturn e
  | SACase mx => SCase mx
  | SALabel l => SLabel l
  | SALocal tau s => SLocal tau (stmtacsl_to_stmt s)
  | SACatch s => SCatch (stmtacsl_to_stmt s)
  | SAComp s1 s2 => SComp (stmtacsl_to_stmt s1) (stmtacsl_to_stmt s2)
  | SALoop s => SLoop (stmtacsl_to_stmt s)
  | SAIf e s1 s2 => SIf e (stmtacsl_to_stmt s1) (stmtacsl_to_stmt s2)
  | SASwitch e s => SSwitch e (stmtacsl_to_stmt s)
  | _ => SSkip
  end.

(*ATTENTION : si une semaine pour labals 
logiques alors go sinon pas de labels logiques (Here, ...)*)
Reserved Notation "Γ \ δ ⊢a S1 ⇒ S2"
  (at level 74, δ at next level,
    format "Γ \  δ  ⊢a  '[' S1  ⇒ '/'  S2 ']'").
Inductive acslstep `{Env K} (Γ : env K) (δ : funacslenv K) : relation (stateacsl K) :=
  (** Simple statements *)
| acslstep_skip m k labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ SASkip) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ SASkip) m labmap stmap
| acslstep_goto m k l labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SAGoto l)) m labmap stmap ⇒
    Stateacsl k (AFStmt (↷ l) (SAGoto l)) m labmap stmap
| acslstep_throw m k n labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SAThrow n)) m labmap stmap ⇒
    Stateacsl k (AFStmt (↑ n) (SAThrow n)) m labmap stmap
| acslstep_case m k mx labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SACase mx)) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SACase mx)) m labmap stmap
| acslstep_in_label m k l labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SALabel l)) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SALabel l)) m (lmap_insert l m labmap)
    (stackmap_insert l (locals2 k) stmap)
| acslstep_expr m k E e labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (aesctx_item_subst E e)) m labmap stmap ⇒
    Stateacsl (AExpr e E :: k) (AFExpr e) m labmap stmap
    
(**i Expressions: *)
| acslstep_expr_head m1 m2 k (E : ectx K) e1 e2 labmap stmap :
  Γ\ locals2 k ⊢ₕ e1, m1 ⇒ e2, m2 →
  Γ\ δ ⊢a Stateacsl k (AFExpr (subst E e1)) m1 labmap stmap ⇒
    Stateacsl k (AFExpr (subst E e2)) m2 labmap stmap
| acslstep_expr_call m k Ω f τs τ E Ωs vs labmap stmap :
  length Ωs = length vs →
  let e := (call %{Ω} (FunPtr f τs τ) @ #{Ωs}* vs)%E in
  Γ\ δ ⊢a Stateacsl k (AFExpr (subst E e)) m labmap stmap ⇒
    Stateacsl (AFun E :: k) (AFCall f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m) labmap stmap
| acslstep_expr_undef m k (E : ectx K) e labmap stmap :
  is_redex e → ¬Γ \ locals2 k ⊢ₕ safe e, m →
  Γ\ δ ⊢a Stateacsl k (AFExpr (subst E e)) m labmap stmap ⇒
    Stateacsl k (AFUndef (AUndefExpr E e)) m labmap stmap
    
 (**i For finished expressions: *)
| acslstep_expr_do m k e Ω v labmap stmap :
  Γ\ δ ⊢a Stateacsl (AExpr e (ADoE) :: k) (AFExpr (#{Ω} v)) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SADo e)) (mem_unlock Ω m) labmap stmap
| acslstep_expr_ret m k e Ω v labmap stmap :
  Γ\ δ ⊢a Stateacsl (AExpr e (AReturnE) :: k) (AFExpr (#{Ω} v)) m labmap stmap ⇒
    Stateacsl k (AFStmt (⇈ v) (SAReturn e)) (mem_unlock Ω m) labmap stmap
| acslstep_expr_if_true m k e Ω vb s1 s2 labmap stmap :
  base_val_branchable m vb → ¬base_val_is_0 vb →
  Γ\ δ ⊢a Stateacsl (AExpr e (AIfE s1 s2) :: k) (AFExpr (#{Ω} VBase vb)) m labmap stmap ⇒
    Stateacsl (AStmt (AIfL e s2) :: k) (AFStmt ↘ s1) (mem_unlock Ω m) labmap stmap
| acslstep_expr_if_false m k e Ω vb s1 s2 labmap stmap :
  base_val_branchable m vb → base_val_is_0 vb →
  Γ\ δ ⊢a Stateacsl (AExpr e (AIfE s1 s2) :: k) (AFExpr(#{Ω} VBase vb)) m labmap stmap ⇒
    Stateacsl (AStmt (AIfR e s1) :: k) (AFStmt ↘ s2) (mem_unlock Ω m) labmap stmap
| acslstep_expr_if_indet m k e Ω vb s1 s2 labmap stmap :
  ¬base_val_branchable m vb →
  Γ\ δ ⊢a Stateacsl (AExpr e (AIfE s1 s2) :: k) (AFExpr(#{Ω} VBase vb)) m labmap stmap ⇒
    Stateacsl k (AFUndef (AUndefBranch (AIfE s1 s2) Ω (VBase vb))) m labmap stmap
| acslstep_switch_case m k e Ω τi x s labmap stmap :
  Some x ∈ cases s →
  Γ\ δ ⊢a Stateacsl (AExpr e (ASwitchE s) :: k) (AFExpr(#{Ω} (intV{τi} x))) m labmap stmap ⇒
    Stateacsl (AStmt (ASwitch e) :: k)
    (AFStmt (↓ (Some x)) s) (mem_unlock Ω m) labmap stmap
| acslstep_switch_default m k e Ω τi x s labmap stmap :
  Some x ∉ cases s → None ∈ cases s →
  Γ\ δ ⊢a Stateacsl (AExpr e (ASwitchE s) :: k) (AFExpr(#{Ω} (intV{τi} x))) m labmap stmap ⇒
    Stateacsl (AStmt (ASwitch e) :: k) (AFStmt (↓ None) s) (mem_unlock Ω m) labmap stmap
| acslstep_switch_out m k e Ω τi x s labmap stmap :
  Some x ∉ cases s → None ∉ cases s →
  Γ\ δ ⊢a Stateacsl (AExpr e (ASwitchE s) :: k) (AFExpr(#{Ω} (intV{τi} x))) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SASwitch e s)) (mem_unlock Ω m) labmap stmap
| acslstep_switch_indet m k e Ω vb s labmap stmap :
  ¬base_val_branchable m vb →
  Γ\ δ ⊢a Stateacsl (AExpr e (ASwitchE s) :: k) (AFExpr(#{Ω} VBase vb)) m labmap stmap ⇒
    Stateacsl k (AFUndef (AUndefBranch (ASwitchE s) Ω (VBase vb))) m labmap stmap

(**i For compound statements: *)
| acslstep_in_comp m k s1 s2 labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SAComp s1 s2)) m labmap stmap ⇒
    Stateacsl (AStmt (ACompL s2) :: k) (AFStmt ↘ s1) m labmap stmap
| acslstep_out_comp1 m k s1 s2 labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ACompL s2) :: k) (AFStmt ↗ s1) m labmap stmap ⇒
    Stateacsl (AStmt (ACompR s1) :: k) (AFStmt ↘ s2) m labmap stmap
| acslstep_out_comp2 m k s1 s2 labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ACompR s1) :: k) (AFStmt ↗ s2) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SAComp s1 s2)) m labmap stmap 
| acslstep_in_catch m k s labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SACatch s)) m labmap stmap ⇒
    Stateacsl (AStmt (ACatch) :: k) (AFStmt ↘ s) m labmap stmap 
| acslstep_out_catch m k s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ACatch) :: k) (AFStmt ↗ s) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SACatch s)) m labmap stmap
| acslstep_in_loop m k s labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SALoop s)) m labmap stmap ⇒
    Stateacsl (AStmt (ALoop) :: k) (AFStmt ↘ s) m labmap stmap
| acslstep_out_loop m k s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ALoop) :: k) (AFStmt ↗ s) m labmap stmap ⇒
    Stateacsl k (AFStmt ↘ (SALoop s)) m labmap stmap
| acslstep_out_if1 m k e s1 s2 labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (AIfL e s2) :: k) (AFStmt ↗ s1) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SAIf e s1 s2)) m labmap stmap
| acslstep_out_if2 m k e s1 s2 labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (AIfR e s1) :: k) (AFStmt ↗ s2) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SAIf e s1 s2)) m labmap stmap
| acslstep_out_switch m k e s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ASwitch e) :: k) (AFStmt ↗ s) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SASwitch e s)) m labmap stmap
    
(**i For function calls *)
| acslstep_call m k f s os vs labmap stmap :
  funacslenv_lookup f δ = Some s → Forall_fresh (dom indexset m) os →
  length os = length vs →
  Γ\ δ ⊢a Stateacsl k (AFCall f vs) m labmap stmap ⇒
    Stateacsl (AParams f (zip os (type_of <$> vs)) :: k)
    (AFStmt ↘ s) (mem_alloc_list Γ os vs m) labmap stmap
| acslstep_free_params m k f oτs s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AParams f oτs :: k) (AFStmt ↗ s) m labmap stmap ⇒
    Stateacsl k (AFReturn f voidV) (foldr mem_free m (oτs.*1)) labmap stmap
| acslstep_free_params_top m k f oτs v s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AParams f oτs :: k) (AFStmt (⇈ v) s) m labmap stmap ⇒
    Stateacsl k (AFReturn f v) (foldr mem_free m (oτs.*1)) labmap stmap
| acslstep_return m k f E v labmap stmap :
  Γ\ δ ⊢a Stateacsl (AFun E :: k) (AFReturn f v) m labmap stmap ⇒
    Stateacsl k (AFExpr(subst E (#v)%E)) m labmap stmap
    
(**i For non-local control flow: *)
| acslstep_label_here m k l labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt (↷ l) (SALabel l)) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SALabel l)) m labmap stmap
| acslstep_throw_here m k s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ACatch) :: k) (AFStmt (↑ 0) s) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SACatch s)) m labmap stmap
| acslstep_throw_further m k s n labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt (ACatch) :: k) (AFStmt (↑ (S n)) s) m labmap stmap ⇒
    Stateacsl k (AFStmt (↑ n) (SACatch s)) m labmap stmap
| acslstep_case_here m k mx labmap stmap :
  Γ\ δ ⊢a Stateacsl k (AFStmt (↓ mx) (SACase mx)) m labmap stmap ⇒
    Stateacsl k (AFStmt ↗ (SACase mx)) m labmap stmap
| acslstep_goto_in m k Es l s labmap stmap :
  l ∈ labels s →
  Γ\ δ ⊢a Stateacsl k (AFStmt (↷ l) (subst Es s)) m labmap stmap ⇒
    Stateacsl (AStmt Es :: k) (AFStmt (↷ l) s) m labmap stmap
| acslstep_switch_in m k Es mx s labmap stmap :
  maybe ASwitch Es = None → mx ∈ cases s →
  Γ\ δ ⊢a Stateacsl k (AFStmt (↓ mx) (subst Es s)) m labmap stmap ⇒
    Stateacsl (AStmt Es :: k) (AFStmt (↓ mx) s) m labmap stmap
| acslstep_top_out m k Es v s labmap stmap :
  Γ\ δ ⊢a Stateacsl (AStmt Es :: k) (AFStmt (⇈ v) s) m labmap stmap ⇒
    Stateacsl k (AFStmt (⇈ v) (subst Es s)) m labmap stmap
| acslstep_goto_out m k Es l s labmap stmap :
  l ∉ labels s →
  Γ\ δ ⊢a Stateacsl (AStmt Es :: k) (AFStmt (↷ l) s) m labmap stmap ⇒
    Stateacsl k (AFStmt (↷ l) (subst Es s)) m labmap stmap
| acslstep_throw_out m k Es n s labmap stmap :
  Es ≠ ACatch →
  Γ\ δ ⊢a Stateacsl (AStmt Es :: k) (AFStmt (↑ n) s) m labmap stmap ⇒
    Stateacsl k (AFStmt (↑ n) (subst Es s)) m labmap stmap
    
(**i For block scopes: *)
| acslstep_in_block m k d o τ s labmap stmap :
  direction_in d (stmtacsl_to_stmt s) → o ∉ dom indexset m →
  Γ\ δ ⊢a Stateacsl k (AFStmt d (SALocal τ s)) m labmap stmap ⇒
    Stateacsl (ALocal o τ :: k) (AFStmt d s) 
    (mem_alloc Γ o false perm_full (val_new Γ τ) m) labmap stmap
| acslstep_out_block m k d o τ s labmap stmap :
  direction_out d (stmtacsl_to_stmt s) →
  Γ\ δ ⊢a Stateacsl (ALocal o τ :: k) (AFStmt d s) m labmap stmap ⇒
    Stateacsl k (AFStmt d (SALocal τ s)) (mem_free o m) labmap stmap

| acslstep_assert k stmap labmap m p pr l :
  pr = predicate_to_prop p Γ (locals2 k) stmap m l labmap  ->
  Γ\ δ ⊢a Stateacsl k (AFStmt ↘ (SAAssert p)) m labmap stmap ⇒ 
    Stateacsl k (AFStmt ↗ (SAAssert p)) m labmap stmap
 
  
where "Γ \ δ  ⊢a S1 ⇒ S2" := (@acslstep _ _ Γ δ S1%S S2%S) : C_scope.

