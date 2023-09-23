
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro hpf,
  apply hpf,
  exact hp,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hpf,
  by_cases hp : P,
  -- Caso P:
    exact hp,
  -- Caso ¬P:
    exfalso,
    apply hpf,
    exact hp,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  --Parte ¬¬P → P:
    exact doubleneg_elim P,
  --Parte P → ¬¬P:
    exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hor,
  cases hor with hp hq,
  --Caso hp:
    right,
    exact hp,
  --Caso hq:  
    left,
    exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hpq,
  cases hpq with hp hq,
  split,
  --Parte Q:
    exact hq,
  --Parte P:
    exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hor,
  intro hp,
  cases hor with hpf hq,
  --Caso hpf:
    exfalso,
    apply hpf,
    exact hp,
  --Caso hq:
    exact hq,  
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hor,
  intro hpf,
  cases hor with hp hq,
  --Caso hp:
    exfalso,
    apply hpf,
    exact hp,
  --Caso hq:
    exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro hqf,
  intro hp,
  apply hqf,
  exact hpq hp,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hqp,
  intro hp,
  by_cases hq : Q,
  --Caso Q:
    exact hq,
  --Caso ¬Q:
    have hpf := hqp hq,
    exfalso,
    apply hpf,
    exact hp,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  --Parte (P → Q) → ¬Q → ¬P:
    exact impl_as_contrapositive P Q,
  --Parte (¬Q → ¬P) → P → Q
    exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have hor : P ∨ ¬P,
  by_cases hp : P,
  --Caso P:
    left,
    exact hp,
  --Caso ¬P:
    right,
    exact hp,
  apply h,
  exact hor,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro hpf,
  apply hpf,
  apply h,
  intro hp,
  exfalso,
  apply hpf,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  sorry,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  sorry,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  sorry,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  sorry,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  sorry,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  sorry,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin 
  intro hpor,
  cases hpor with hp hor,
  cases hor with hq hr,
  --Caso hq:
    left,
    split,
    --Parte P:
      exact hp,
    --Parte Q:  
      exact hq,
  --Caso hr:    
    right,
    split,
    --Parte P:
      exact hp,
    --Parte R:
      exact hr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hor,
  cases hor with hpq hpr,
  --Caso hpq:
    split,
    --Parte P:
      exact hpq.1,
    --Parte Q ∨ R:
      left,
      exact hpq.2,
  --Caso hpr:  
    split,
    --Parte P:
      exact hpr.1,
    --Parte Q ∨ R:  
      right,
      exact hpr.2,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hor,
  cases hor with hp hqr,
  --Caso hp:
    split,
    --Parte P ∨ Q:
      left,
      exact hp,
    --Parte P ∨ R:
      left,
      exact hp,
  --Caso hqr:
    split,
    --Parte P ∨ Q:
      right,
      exact hqr.1,
    --Parte P ∨ R:
      right,
      exact hqr.2,  
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hor hor',
  cases hor with hp hq,
  --Caso hp:
    left,
    exact hp,
  --Caso hq:
    cases hor' with hp hr,
    --Caso hp:
      left,
      exact hp,
    --Caso hr:
      right,
      split,
      --Parte Q:
        exact hq,
      --Parte R: 
        exact hr,   
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h hp hq,
  have hpq : P∧Q,
    split,
    --Parte P:
      exact hp,
    --Parte Q:
      exact hq,
  apply h,
  exact hpq,      
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h hpq,
  have hq := h hpq.1,
  apply hq,
  exact hpq.2,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hpq,
  exact hpq.1,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hpq,
  exact hpq.2
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  --Parte (P∧P) → P
    intro hpp,
    exact hpp.1,
  --Parte P → (P∧P)
    intro hp,
    split,
      --Parte P:
      exact hp,
      --Parte P':
      exact  hp,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  --Parte (P∨P) → P
    intro hor,
    cases hor with hp hp',
    --Caso hp:
      exact hp,
    --Caso hp',
      exact hp',
  --Parte P → (P∨P)
    intro hp,
    left,
    exact hp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
