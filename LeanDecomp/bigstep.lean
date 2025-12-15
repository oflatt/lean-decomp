import LeanDecomp.ProofTermMacro

@[expose] public section
abbrev Variable := String

def State := Variable → Nat

inductive Stmt : Type where
  | skip : Stmt
  | assign : Variable → (State → Nat) → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo : (State → Prop) → Stmt → Stmt

infix:60 ";; " => Stmt.seq

export Stmt (skip assign seq ifThenElse whileDo)

set_option quotPrecheck false in
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

inductive BigStep : Stmt → State → State → Prop where
  | skip (s : State) : BigStep skip s s
  | assign (x : Variable) (a : State → Nat) (s : State) : BigStep (assign x a) s (s[x ↦ a s])
  | seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u
  | if_true {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : BigStep S s t) :
    BigStep (ifThenElse B S T) s t
  | if_false {B : State → Prop} {s t : State} (hcond : ¬ B s) (S T : Stmt) (hbody : BigStep T s t) :
    BigStep (ifThenElse B S T) s t
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t) (hrest : BigStep (whileDo B S) t u) :
    BigStep (whileDo B S) s u
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S) s s

notation:55 "(" S:55 "," s:55 ")" " ==> " t:55 => BigStep S s t

example {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind [BigStep]

attribute [grind] BigStep

theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind

theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t → (T, s) ==> t := by
  grind

theorem cases_if_of_true2 : ∀ {B : State → Prop} {S T : Stmt} {s t : State} (hcond : B s), BigStep (Stmt.ifThenElse B S T) s t → BigStep S s t := by
  intros B S T s t hcond h
  classical
  apply Classical.byContradiction
  intro h_1
  exact
    (fun (h_1 : Not (BigStep S s t)) =>
        @id.{0} False
          (@BigStep.casesOn
            (fun (a : Stmt) (a_1 a_2 : State) (x : BigStep a a_1 a_2) =>
              ∀ (h_2 : @Eq.{1} Stmt (Stmt.ifThenElse B S T) a) (h_3 : @Eq.{1} State s a_1) (h_4 : @Eq.{1} State t a_2)
                (h : @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep a a_1 a_2) x), False)
            (Stmt.ifThenElse B S T) s t h
            (fun (s_1 : State) =>
              Lean.Grind.intro_with_eq.{0} (@Eq.{1} Stmt (Stmt.ifThenElse B S T) Stmt.skip) False
                (∀ (h_2 : @Eq.{1} State s s_1) (h_3 : @Eq.{1} State t s_1)
                  (h : @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep Stmt.skip s_1 s_1) (BigStep.skip s_1)),
                  False)
                (@eq_false' (@Eq.{1} Stmt (Stmt.ifThenElse B S T) Stmt.skip)
                  fun (h : @Eq.{1} Stmt (Stmt.ifThenElse B S T) Stmt.skip) =>
                  @False.elim.{0} False (@noConfusion_of_Nat.{1} Stmt Stmt.ctorIdx (Stmt.ifThenElse B S T) Stmt.skip h))
                fun (h_2 : False) =>
                False.casesOn.{0}
                  (fun (x : False) =>
                    ∀ (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t s_1)
                      (h : @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep Stmt.skip s_1 s_1) (BigStep.skip s_1)),
                      False)
                  h_2)
            (fun (x : Variable) (a : State → Nat) (s_1 : State) =>
              Lean.Grind.intro_with_eq.{0} (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.assign x a)) False
                (∀ (h_2 : @Eq.{1} State s s_1)
                  (h_3 :
                    @Eq.{1} State t fun (v : Variable) =>
                      @ite.{1} Nat (@Eq.{1} Variable v x) (instDecidableEqString v x) (a s_1) (s_1 v))
                  (h :
                    @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h
                      (BigStep (Stmt.assign x a) s_1 fun (v : Variable) =>
                        @ite.{1} Nat (@Eq.{1} Variable v x) (instDecidableEqString v x) (a s_1) (s_1 v))
                      (BigStep.assign x a s_1)),
                  False)
                (@eq_false' (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.assign x a))
                  fun (h : @Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.assign x a)) =>
                  @False.elim.{0} False
                    (@noConfusion_of_Nat.{1} Stmt Stmt.ctorIdx (Stmt.ifThenElse B S T) (Stmt.assign x a) h))
                fun (h_2 : False) =>
                False.casesOn.{0}
                  (fun (x_1 : False) =>
                    ∀ (h_3 : @Eq.{1} State s s_1)
                      (h_4 :
                        @Eq.{1} State t fun (v : Variable) =>
                          @ite.{1} Nat (@Eq.{1} Variable v x) (instDecidableEqString v x) (a s_1) (s_1 v))
                      (h :
                        @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h
                          (BigStep (Stmt.assign x a) s_1 fun (v : Variable) =>
                            @ite.{1} Nat (@Eq.{1} Variable v x) (instDecidableEqString v x) (a s_1) (s_1 v))
                          (BigStep.assign x a s_1)),
                      False)
                  h_2)
            (fun {S_1 T_1 : Stmt} {s_1 t_1 u : State} (hS : BigStep S_1 s_1 t_1) (hT : BigStep T_1 t_1 u) =>
              Lean.Grind.intro_with_eq.{0} (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.seq S_1 T_1)) False
                (∀ (h_2 : @Eq.{1} State s s_1) (h_3 : @Eq.{1} State t u)
                  (h :
                    @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.seq S_1 T_1) s_1 u)
                      (@BigStep.seq S_1 T_1 s_1 t_1 u hS hT)),
                  False)
                (@eq_false' (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.seq S_1 T_1))
                  fun (h : @Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.seq S_1 T_1)) =>
                  @False.elim.{0} False
                    (@noConfusion_of_Nat.{1} Stmt Stmt.ctorIdx (Stmt.ifThenElse B S T) (Stmt.seq S_1 T_1) h))
                fun (h_2 : False) =>
                False.casesOn.{0}
                  (fun (x : False) =>
                    ∀ (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t u)
                      (h :
                        @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.seq S_1 T_1) s_1 u)
                          (@BigStep.seq S_1 T_1 s_1 t_1 u hS hT)),
                      False)
                  h_2)
            (fun {B_1 : State → Prop} {s_1 t_1 : State} (hcond_1 : B_1 s_1) (S_1 T_1 : Stmt) (hbody : BigStep S_1 s_1 t_1)
                (h_2 : @Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.ifThenElse B_1 S_1 T_1)) =>
              @Stmt.ifThenElse.noConfusion.{0}
                (∀ (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t t_1)
                  (h :
                    @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                      (@BigStep.if_true B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                  False)
                B S T B_1 S_1 T_1 h_2
                fun (a_eq : @Eq.{1} (State → Prop) B B_1) (a_eq_1 : @Eq.{1} Stmt S S_1) (a_eq_2 : @Eq.{1} Stmt T T_1)
                  (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t t_1) =>
                @False.elim.{0}
                  (∀
                    (h :
                      @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                        (@BigStep.if_true B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                    False)
                  (@Eq.mp.{0} True False
                    (@Eq.trans.{1} Prop True (BigStep S s t) False
                      (@Eq.trans.{1} Prop True (BigStep S_1 s_1 t_1) (BigStep S s t)
                        (@Eq.symm.{1} Prop (BigStep S_1 s_1 t_1) True (@eq_true (BigStep S_1 s_1 t_1) hbody))
                        (@congr.{1, 1} State Prop (BigStep S_1 s_1) (BigStep S s) t_1 t
                          (@congr.{1, 1} State (State → Prop) (BigStep S_1) (BigStep S) s_1 s
                            (@congrArg.{1, 1} Stmt (State → State → Prop) S_1 S BigStep (@Eq.symm.{1} Stmt S S_1 a_eq_1))
                            (@Eq.symm.{1} State s s_1 h_3))
                          (@Eq.symm.{1} State t t_1 h_4)))
                      (@eq_false (BigStep S s t) h_1))
                    True.intro))
            (fun {B_1 : State → Prop} {s_1 t_1 : State} (hcond_1 : Not (B_1 s_1)) (S_1 T_1 : Stmt)
                (hbody : BigStep T_1 s_1 t_1) (h_2 : @Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.ifThenElse B_1 S_1 T_1)) =>
              @Stmt.ifThenElse.noConfusion.{0}
                (∀ (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t t_1)
                  (h :
                    @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                      (@BigStep.if_false B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                  False)
                B S T B_1 S_1 T_1 h_2
                fun (a_eq : @Eq.{1} (State → Prop) B B_1) (a_eq_1 : @Eq.{1} Stmt S S_1) (a_eq_2 : @Eq.{1} Stmt T T_1)
                  (h_3 : @Eq.{1} State s s_1) =>
                @False.elim.{0}
                  (∀ (h_4 : @Eq.{1} State t t_1)
                    (h :
                      @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.ifThenElse B_1 S_1 T_1) s_1 t_1)
                        (@BigStep.if_false B_1 s_1 t_1 hcond_1 S_1 T_1 hbody)),
                    False)
                  (@Eq.mp.{0} True False
                    (@Eq.trans.{1} Prop True (B_1 s_1) False
                      (@Eq.trans.{1} Prop True (B s) (B_1 s_1) (@Eq.symm.{1} Prop (B s) True (@eq_true (B s) hcond))
                        (@eq_of_heq.{1} Prop (B s) (B_1 s_1)
                          (@Eq.ndrec.{0, 1} (State → Prop) B (fun (x : State → Prop) => @HEq.{1} Prop (B s) Prop (x s_1))
                            ((fun (a a' : State) (e_1 : @Eq.{1} State a a') =>
                                @Eq.ndrec.{0, 1} State a (fun (a' : State) => @HEq.{1} Prop (B a) Prop (B a'))
                                  (@HEq.refl.{1} Prop (B a)) a' e_1)
                              s s_1 h_3)
                            B_1 a_eq)))
                      (@eq_false (B_1 s_1) hcond_1))
                    True.intro))
            (fun {B_1 : State → Prop} {S_1 : Stmt} {s_1 t_1 u : State} (hcond_1 : B_1 s_1) (hbody : BigStep S_1 s_1 t_1)
                (hrest : BigStep (Stmt.whileDo B_1 S_1) t_1 u) =>
              Lean.Grind.intro_with_eq.{0} (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1)) False
                (∀ (h_2 : @Eq.{1} State s s_1) (h_3 : @Eq.{1} State t u)
                  (h :
                    @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.whileDo B_1 S_1) s_1 u)
                      (@BigStep.while_true B_1 S_1 s_1 t_1 u hcond_1 hbody hrest)),
                  False)
                (@eq_false' (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1))
                  fun (h : @Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1)) =>
                  @False.elim.{0} False
                    (@noConfusion_of_Nat.{1} Stmt Stmt.ctorIdx (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1) h))
                fun (h_2 : False) =>
                False.casesOn.{0}
                  (fun (x : False) =>
                    ∀ (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t u)
                      (h :
                        @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.whileDo B_1 S_1) s_1 u)
                          (@BigStep.while_true B_1 S_1 s_1 t_1 u hcond_1 hbody hrest)),
                      False)
                  h_2)
            (fun {B_1 : State → Prop} {S_1 : Stmt} {s_1 : State} (hcond_1 : Not (B_1 s_1)) =>
              Lean.Grind.intro_with_eq.{0} (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1)) False
                (∀ (h_2 : @Eq.{1} State s s_1) (h_3 : @Eq.{1} State t s_1)
                  (h :
                    @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.whileDo B_1 S_1) s_1 s_1)
                      (@BigStep.while_false B_1 S_1 s_1 hcond_1)),
                  False)
                (@eq_false' (@Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1))
                  fun (h : @Eq.{1} Stmt (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1)) =>
                  @False.elim.{0} False
                    (@noConfusion_of_Nat.{1} Stmt Stmt.ctorIdx (Stmt.ifThenElse B S T) (Stmt.whileDo B_1 S_1) h))
                fun (h_2 : False) =>
                False.casesOn.{0}
                  (fun (x : False) =>
                    ∀ (h_3 : @Eq.{1} State s s_1) (h_4 : @Eq.{1} State t s_1)
                      (h :
                        @HEq.{0} (BigStep (Stmt.ifThenElse B S T) s t) h (BigStep (Stmt.whileDo B_1 S_1) s_1 s_1)
                          (@BigStep.while_false B_1 S_1 s_1 hcond_1)),
                      False)
                  h_2)
            (@Eq.refl.{1} Stmt (Stmt.ifThenElse B S T)) (@Eq.refl.{1} State s) (@Eq.refl.{1} State t)
            (@HEq.refl.{0} (BigStep (Stmt.ifThenElse B S T) s t) h)))
      h_1

theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔ (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  grind =>
    instantiate only [BigStep.if_true, BigStep.if_false]
    cases #8de8
    · cases #52a7
      · cases #860f
      · cases #74ed <;> cases #860f
    · cases #1c13

end

showProofTerm cases_if_of_true
