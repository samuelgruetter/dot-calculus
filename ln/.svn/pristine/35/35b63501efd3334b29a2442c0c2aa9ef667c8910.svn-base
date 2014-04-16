
(* Due to a bug in the [induction using] tactic of Coq,
   if you want to perform an induction over an environment, 
   you need to declare it so that the body of the definition 
   of [ctx] comes from the module [Env] and not [LibEnv],
   e.g. [Definition ctx := LibEnv.env typ]. Otherwise, you get
   the error "Cannot recognize a statement based on LibEnv.env." *)

Lemma env_ind : forall A (P : LibEnv.env A -> Prop),
  (P empty) ->
  (forall E x v, P E -> P (E & x ~ v)) ->
  (forall E, P E).
Proof. apply env_ind. Qed.
