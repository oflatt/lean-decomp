∀ {motive : (a : Stmt) → (a_1 a_2 : State) → (a,a_1) ==> a_2 → Prop} {a : Stmt} {a_1 a_2 : State} (t : (a,a_1) ==> a_2),
  (∀ (s : State), motive skip s s ⋯) →
    (∀ (x : Variable) (a : State → Nat) (s : State), motive (assign x a) s (fun v => if v = x then a s else s v) ⋯) →
      (∀ {S T : Stmt} {s t u : State} (hS : (S,s) ==> t) (hT : (T,t) ==> u), motive (S;; T) s u ⋯) →
        (∀ {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : (S,s) ==> t),
            motive (ifThenElse B S T) s t ⋯) →
          (∀ {B : State → Prop} {s t : State} (hcond : ¬B s) (S T : Stmt) (hbody : (T,s) ==> t),
              motive (ifThenElse B S T) s t ⋯) →
            (∀ {B : State → Prop} {S : Stmt} {s t u : State} (hcond : B s) (hbody : (S,s) ==> t)
                (hrest : (whileDo B S,t) ==> u), motive (whileDo B S) s u ⋯) →
              (∀ {B : State → Prop} {S : Stmt} {s : State} (hcond : ¬B s), motive (whileDo B S) s s ⋯) →
                motive a a_1 a_2 t
