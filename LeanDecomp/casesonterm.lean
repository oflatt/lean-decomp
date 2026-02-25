  [apply]  intro h
    apply Classical.byContradiction
    intro h_1
    let h_1 := h_1
    let prf : False := by
      exact
        @LeanDecomp.BigStepTest.BigStep.casesOn
          (fun (a : LeanDecomp.BigStepTest.Stmt) (a_1 a_2 : LeanDecomp.BigStepTest.State)
              (x : LeanDecomp.BigStepTest.BigStep a a_1 a_2) =>
            ∀ (h_2 : @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) a)
              (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s a_1) (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t a_2)
              (h :
                @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                  (LeanDecomp.BigStepTest.BigStep a a_1 a_2) x),
              False)
          (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t h
          (fun (s_1 : LeanDecomp.BigStepTest.State) =>
            Lean.Grind.intro_with_eq.{0}
              (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                LeanDecomp.BigStepTest.Stmt.skip)
              False
              (∀ (h_2 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State t s_1)
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep LeanDecomp.BigStepTest.Stmt.skip s_1 s_1)
                    (LeanDecomp.BigStepTest.BigStep.skip s_1)),
                False)
              (@eq_false'
                (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  LeanDecomp.BigStepTest.Stmt.skip)
                fun
                  (h :
                    @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                      LeanDecomp.BigStepTest.Stmt.skip) =>
                @False.elim.{0} False
                  (@noConfusion_of_Nat.{1} LeanDecomp.BigStepTest.Stmt LeanDecomp.BigStepTest.Stmt.ctorIdx
                    (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) LeanDecomp.BigStepTest.Stmt.skip h))
              fun (h_2 : False) =>
              False.casesOn.{0}
                (fun (x : False) =>
                  ∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1)
                    (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t s_1)
                    (h :
                      @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                        (LeanDecomp.BigStepTest.BigStep LeanDecomp.BigStepTest.Stmt.skip s_1 s_1)
                        (LeanDecomp.BigStepTest.BigStep.skip s_1)),
                    False)
                h_2)
          (fun (x : LeanDecomp.BigStepTest.Variable) (a : LeanDecomp.BigStepTest.State → Nat)
              (s_1 : LeanDecomp.BigStepTest.State) =>
            Lean.Grind.intro_with_eq.{0}
              (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                (LeanDecomp.BigStepTest.Stmt.assign x a))
              False
              (∀ (h_2 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1)
                (h_3 :
                  @Eq.{1} LeanDecomp.BigStepTest.State t fun (v : LeanDecomp.BigStepTest.Variable) =>
                    @ite.{1} Nat (@Eq.{1} LeanDecomp.BigStepTest.Variable v x) (instDecidableEqString v x) (a s_1)
                      (s_1 v))
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.assign x a) s_1
                      fun (v : LeanDecomp.BigStepTest.Variable) =>
                      @ite.{1} Nat (@Eq.{1} LeanDecomp.BigStepTest.Variable v x) (instDecidableEqString v x) (a s_1)
                        (s_1 v))
                    (LeanDecomp.BigStepTest.BigStep.assign x a s_1)),
                False)
              (@eq_false'
                (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  (LeanDecomp.BigStepTest.Stmt.assign x a))
                fun
                  (h :
                    @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                      (LeanDecomp.BigStepTest.Stmt.assign x a)) =>
                @False.elim.{0} False
                  (@noConfusion_of_Nat.{1} LeanDecomp.BigStepTest.Stmt LeanDecomp.BigStepTest.Stmt.ctorIdx
                    (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) (LeanDecomp.BigStepTest.Stmt.assign x a) h))
              fun (h_2 : False) =>
              False.casesOn.{0}
                (fun (x_1 : False) =>
                  ∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1)
                    (h_4 :
                      @Eq.{1} LeanDecomp.BigStepTest.State t fun (v : LeanDecomp.BigStepTest.Variable) =>
                        @ite.{1} Nat (@Eq.{1} LeanDecomp.BigStepTest.Variable v x) (instDecidableEqString v x) (a s_1)
                          (s_1 v))
                    (h :
                      @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                        (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.assign x a) s_1
                          fun (v : LeanDecomp.BigStepTest.Variable) =>
                          @ite.{1} Nat (@Eq.{1} LeanDecomp.BigStepTest.Variable v x) (instDecidableEqString v x) (a s_1)
                            (s_1 v))
                        (LeanDecomp.BigStepTest.BigStep.assign x a s_1)),
                    False)
                h_2)
          (fun {S_1 T_1 : LeanDecomp.BigStepTest.Stmt} {s_1 t_1 u : LeanDecomp.BigStepTest.State}
              (hS : LeanDecomp.BigStepTest.BigStep S_1 s_1 t_1) (hT : LeanDecomp.BigStepTest.BigStep T_1 t_1 u) =>
            Lean.Grind.intro_with_eq.{0}
              (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                (LeanDecomp.BigStepTest.Stmt.seq S_1 T_1))
              False
              (∀ (h_2 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State t u)
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.seq S_1 T_1) s_1 u)
                    (@LeanDecomp.BigStepTest.BigStep.seq S_1 T_1 s_1 t_1 u hS hT)),
                False)
              (@eq_false'
                (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  (LeanDecomp.BigStepTest.Stmt.seq S_1 T_1))
                fun
                  (h :
                    @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                      (LeanDecomp.BigStepTest.Stmt.seq S_1 T_1)) =>
                @False.elim.{0} False
                  (@noConfusion_of_Nat.{1} LeanDecomp.BigStepTest.Stmt LeanDecomp.BigStepTest.Stmt.ctorIdx
                    (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) (LeanDecomp.BigStepTest.Stmt.seq S_1 T_1) h))
              fun (h_2 : False) =>
              False.casesOn.{0}
                (fun (x : False) =>
                  ∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t u)
                    (h :
                      @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                        (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.seq S_1 T_1) s_1 u)
                        (@LeanDecomp.BigStepTest.BigStep.seq S_1 T_1 s_1 t_1 u hS hT)),
                    False)
                h_2)
          (fun {B_1 : LeanDecomp.BigStepTest.State → Prop} {s_1 t_1 : LeanDecomp.BigStepTest.State} (hcond_1 : B_1 s_1)
              (S_1 T_1 : LeanDecomp.BigStepTest.Stmt) (hbody : LeanDecomp.BigStepTest.BigStep S_1 s_1 t_1)
              (h_2 :
                @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  (LeanDecomp.BigStepTest.Stmt.ifThenElse B_1 S_1 T_1)) =>
            @LeanDecomp.BigStepTest.Stmt.ifThenElse.noConfusion.{0}
              (∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t t_1)
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                    (@LeanDecomp.BigStepTest.BigStep.if_true B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                False)
              B S T B_1 S_1 T_1 h_2
              fun (a_eq : @Eq.{1} (LeanDecomp.BigStepTest.State → Prop) B B_1)
                (a_eq_1 : @Eq.{1} LeanDecomp.BigStepTest.Stmt S S_1)
                (a_eq_2 : @Eq.{1} LeanDecomp.BigStepTest.Stmt T T_1) (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1)
                (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t t_1) =>
              @False.elim.{0}
                (∀
                  (h :
                    @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                      (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                      (@LeanDecomp.BigStepTest.BigStep.if_true B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                  False)
                (@Eq.mp.{0} True False
                  (@Eq.trans.{1} Prop True (LeanDecomp.BigStepTest.BigStep S s t) False
                    (@Eq.trans.{1} Prop True (LeanDecomp.BigStepTest.BigStep S_1 s_1 t_1)
                      (LeanDecomp.BigStepTest.BigStep S s t)
                      (@Eq.symm.{1} Prop (LeanDecomp.BigStepTest.BigStep S_1 s_1 t_1) True
                        (@eq_true (LeanDecomp.BigStepTest.BigStep S_1 s_1 t_1) hbody))
                      (@congr.{1, 1} LeanDecomp.BigStepTest.State Prop (LeanDecomp.BigStepTest.BigStep S_1 s_1)
                        (LeanDecomp.BigStepTest.BigStep S s) t_1 t
                        (@congr.{1, 1} LeanDecomp.BigStepTest.State (LeanDecomp.BigStepTest.State → Prop)
                          (LeanDecomp.BigStepTest.BigStep S_1) (LeanDecomp.BigStepTest.BigStep S) s_1 s
                          (@congrArg.{1, 1} LeanDecomp.BigStepTest.Stmt
                            (LeanDecomp.BigStepTest.State → LeanDecomp.BigStepTest.State → Prop) S_1 S
                            LeanDecomp.BigStepTest.BigStep (@Eq.symm.{1} LeanDecomp.BigStepTest.Stmt S S_1 a_eq_1))
                          (@Eq.symm.{1} LeanDecomp.BigStepTest.State s s_1 h_3))
                        (@Eq.symm.{1} LeanDecomp.BigStepTest.State t t_1 h_4)))
                    (@eq_false (LeanDecomp.BigStepTest.BigStep S s t) h_1))
                  True.intro))
          (fun {B_1 : LeanDecomp.BigStepTest.State → Prop} {s_1 t_1 : LeanDecomp.BigStepTest.State}
              (hcond_1 : Not (B_1 s_1)) (S_1 T_1 : LeanDecomp.BigStepTest.Stmt)
              (hbody : LeanDecomp.BigStepTest.BigStep T_1 s_1 t_1)
              (h_2 :
                @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  (LeanDecomp.BigStepTest.Stmt.ifThenElse B_1 S_1 T_1)) =>
            @LeanDecomp.BigStepTest.Stmt.ifThenElse.noConfusion.{0}
              (∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t t_1)
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                    (@LeanDecomp.BigStepTest.BigStep.if_false B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                False)
              B S T B_1 S_1 T_1 h_2
              fun (a_eq : @Eq.{1} (LeanDecomp.BigStepTest.State → Prop) B B_1)
                (a_eq_1 : @Eq.{1} LeanDecomp.BigStepTest.Stmt S S_1)
                (a_eq_2 : @Eq.{1} LeanDecomp.BigStepTest.Stmt T T_1)
                (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) =>
              @False.elim.{0}
                (∀ (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t t_1)
                  (h :
                    @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                      (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                      (@LeanDecomp.BigStepTest.BigStep.if_false B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                  False)
                (@Eq.mp.{0} True False
                  (@Eq.trans.{1} Prop True (B_1 s_1) False
                    (@Eq.trans.{1} Prop True (B s) (B_1 s_1) (@Eq.symm.{1} Prop (B s) True (@eq_true (B s) hcond))
                      (@eq_of_heq.{1} Prop (B s) (B_1 s_1)
                        (@Eq.ndrec.{0, 1} (LeanDecomp.BigStepTest.State → Prop) B
                          (fun (x : LeanDecomp.BigStepTest.State → Prop) => @HEq.{1} Prop (B s) Prop (x s_1))
                          ((fun (a a' : LeanDecomp.BigStepTest.State)
                                (e_1 : @Eq.{1} LeanDecomp.BigStepTest.State a a') =>
                              @Eq.ndrec.{0, 1} LeanDecomp.BigStepTest.State a
                                (fun (a' : LeanDecomp.BigStepTest.State) => @HEq.{1} Prop (B a) Prop (B a'))
                                (@HEq.refl.{1} Prop (B a)) a' e_1)
                            s s_1 h_3)
                          B_1 a_eq)))
                    (@eq_false (B_1 s_1) hcond_1))
                  True.intro))
          (fun {B_1 : LeanDecomp.BigStepTest.State → Prop} {S_1 : LeanDecomp.BigStepTest.Stmt}
              {s_1 t_1 u : LeanDecomp.BigStepTest.State} (hcond_1 : B_1 s_1)
              (hbody : LeanDecomp.BigStepTest.BigStep S_1 s_1 t_1)
              (hrest : LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) t_1 u) =>
            Lean.Grind.intro_with_eq.{0}
              (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1))
              False
              (∀ (h_2 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State t u)
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) s_1 u)
                    (@LeanDecomp.BigStepTest.BigStep.while_true B_1 S_1 s_1 t_1 u hcond_1 hbody hrest)),
                False)
              (@eq_false'
                (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1))
                fun
                  (h :
                    @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                      (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1)) =>
                @False.elim.{0} False
                  (@noConfusion_of_Nat.{1} LeanDecomp.BigStepTest.Stmt LeanDecomp.BigStepTest.Stmt.ctorIdx
                    (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) h))
              fun (h_2 : False) =>
              False.casesOn.{0}
                (fun (x : False) =>
                  ∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t u)
                    (h :
                      @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                        (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) s_1 u)
                        (@LeanDecomp.BigStepTest.BigStep.while_true B_1 S_1 s_1 t_1 u hcond_1 hbody hrest)),
                    False)
                h_2)
          (fun {B_1 : LeanDecomp.BigStepTest.State → Prop} {S_1 : LeanDecomp.BigStepTest.Stmt}
              {s_1 : LeanDecomp.BigStepTest.State} (hcond_1 : Not (B_1 s_1)) =>
            Lean.Grind.intro_with_eq.{0}
              (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1))
              False
              (∀ (h_2 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1) (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State t s_1)
                (h :
                  @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                    (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) s_1 s_1)
                    (@LeanDecomp.BigStepTest.BigStep.while_false B_1 S_1 s_1 hcond_1)),
                False)
              (@eq_false'
                (@Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                  (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1))
                fun
                  (h :
                    @Eq.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T)
                      (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1)) =>
                @False.elim.{0} False
                  (@noConfusion_of_Nat.{1} LeanDecomp.BigStepTest.Stmt LeanDecomp.BigStepTest.Stmt.ctorIdx
                    (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) h))
              fun (h_2 : False) =>
              False.casesOn.{0}
                (fun (x : False) =>
                  ∀ (h_3 : @Eq.{1} LeanDecomp.BigStepTest.State s s_1)
                    (h_4 : @Eq.{1} LeanDecomp.BigStepTest.State t s_1)
                    (h :
                      @HEq.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h
                        (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.whileDo B_1 S_1) s_1 s_1)
                        (@LeanDecomp.BigStepTest.BigStep.while_false B_1 S_1 s_1 hcond_1)),
                    False)
                h_2)
          (@Eq.refl.{1} LeanDecomp.BigStepTest.Stmt (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T))
          (@Eq.refl.{1} LeanDecomp.BigStepTest.State s) (@Eq.refl.{1} LeanDecomp.BigStepTest.State t)
          (@HEq.refl.{0} (LeanDecomp.BigStepTest.BigStep (LeanDecomp.BigStepTest.Stmt.ifThenElse B S T) s t) h)
    exact prf
