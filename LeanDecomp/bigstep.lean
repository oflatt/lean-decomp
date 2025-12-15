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


#print cases_if_of_true

theorem cases_if_of_true2 : ∀ {B : State → Prop} {S T : Stmt} {s t : State}, B s → (ifThenElse B S T,s) ==> t → (S,s) ==> t :=
  fun {B} {S T} {s t} hcond h =>
  Classical.byContradiction fun h_1 =>
    id
      (BigStep.casesOn (motive := fun a a_1 a_2 x => ifThenElse B S T = a → s = a_1 → t = a_2 → h ≍ x → False) h
        (fun s_1 =>
          Lean.Grind.intro_with_eq (ifThenElse B S T = skip) False (s = s_1 → t = s_1 → h ≍ BigStep.skip s_1 → False)
            (eq_false' fun h => False.elim (noConfusion_of_Nat Stmt.ctorIdx h)) fun h_2 =>
            False.casesOn (fun x => s = s_1 → t = s_1 → h ≍ BigStep.skip s_1 → False) h_2)
        (fun x a s_1 =>
          Lean.Grind.intro_with_eq (ifThenElse B S T = assign x a) False
            (s = s_1 → (t = fun v => if v = x then a s_1 else s_1 v) → h ≍ BigStep.assign x a s_1 → False)
            (eq_false' fun h => False.elim (noConfusion_of_Nat Stmt.ctorIdx h)) fun h_2 =>
            False.casesOn
              (fun x_1 => s = s_1 → (t = fun v => if v = x then a s_1 else s_1 v) → h ≍ BigStep.assign x a s_1 → False)
              h_2)
        (fun {S_1 T_1} {s_1 t_1 u} hS hT =>
          Lean.Grind.intro_with_eq (ifThenElse B S T = S_1;; T_1) False
            (s = s_1 → t = u → h ≍ BigStep.seq hS hT → False)
            (eq_false' fun h => False.elim (noConfusion_of_Nat Stmt.ctorIdx h)) fun h_2 =>
            False.casesOn (fun x => s = s_1 → t = u → h ≍ BigStep.seq hS hT → False) h_2)
        (fun {B_1} {s_1 t_1} hcond_1 S_1 T_1 hbody h_2 =>
          Stmt.ifThenElse.noConfusion h_2 fun a_eq a_eq_1 a_eq_2 h_3 h_4 =>
            False.elim
              (Eq.mp
                (Eq.trans
                  (Eq.trans (Eq.symm (eq_true hbody))
                    (congr (congr (congrArg BigStep (Eq.symm a_eq_1)) (Eq.symm h_3)) (Eq.symm h_4)))
                  (eq_false h_1))
                True.intro))
        (fun {B_1} {s_1 t_1} hcond_1 S_1 T_1 hbody h_2 =>
          Stmt.ifThenElse.noConfusion h_2 fun a_eq a_eq_1 a_eq_2 h_3 =>
            False.elim
              (Eq.mp
                (Eq.trans
                  (Eq.trans (Eq.symm (eq_true hcond))
                    (eq_of_heq (a_eq ▸ (fun a a' e_1 => e_1 ▸ HEq.refl (B a)) s s_1 h_3)))
                  (eq_false hcond_1))
                True.intro))
        (fun {B_1} {S_1} {s_1 t_1 u} hcond_1 hbody hrest =>
          Lean.Grind.intro_with_eq (ifThenElse B S T = whileDo B_1 S_1) False
            (s = s_1 → t = u → h ≍ BigStep.while_true hcond_1 hbody hrest → False)
            (eq_false' fun h => False.elim (noConfusion_of_Nat Stmt.ctorIdx h)) fun h_2 =>
            False.casesOn (fun x => s = s_1 → t = u → h ≍ BigStep.while_true hcond_1 hbody hrest → False) h_2)
        (fun {B_1} {S_1} {s_1} hcond_1 =>
          Lean.Grind.intro_with_eq (ifThenElse B S T = whileDo B_1 S_1) False
            (s = s_1 → t = s_1 → h ≍ BigStep.while_false hcond_1 → False)
            (eq_false' fun h => False.elim (noConfusion_of_Nat Stmt.ctorIdx h)) fun h_2 =>
            False.casesOn (fun x => s = s_1 → t = s_1 → h ≍ BigStep.while_false hcond_1 → False) h_2)
        (Eq.refl (ifThenElse B S T)) (Eq.refl s) (Eq.refl t) (HEq.refl h))

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
