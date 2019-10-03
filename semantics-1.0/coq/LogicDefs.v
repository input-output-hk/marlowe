Require Import ZArith_base.
Require Import Coq.ZArith.Int.
Require Import Coq.Structures.OrderedType.
Require Import FSets.FMapAVL.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.

Open Scope Int_scope.

Inductive EquationTerm {a: Type} := NegVar : a -> @EquationTerm a
                                                         | Var : a -> @EquationTerm a
                                                         | Const : Z -> EquationTerm.

Inductive Equation {a: Type} := LE : list (@EquationTerm a) -> list (@EquationTerm a) -> @Equation a.

Inductive Logic {a: Type} := Eq : @Equation a -> @Logic a
                                            | Not : @Logic a -> @Logic a
                                            | And : list (@Logic a) -> @Logic a
                                            | Or : list (@Logic a) -> @Logic a.


Module LabelledLogic (a : OrderedType).

Definition t := a.t.

Module SOL_MAP := FMapAVL.Make(a).
Definition emptySOLMap := SOL_MAP.empty Z.
Definition SOL_MAP_TYPE := SOL_MAP.t Z.
Module SOL_P := WProperties_fun a SOL_MAP.
Module SOL_F := SOL_P.F.

Lemma in_a_eq_in : forall x0 l, ~ InA (SOL_MAP.eq_key (elt:=Z)) x0 l -> ~ In x0 l.
intros.
induction l.
simpl.
intuition.
intuition.
remember (SOL_MAP.eq_key (elt:=Z)) as eqA.
simpl in H0.
destruct H0.
assert (eqA x0 a).
rewrite H0.
rewrite HeqeqA.
apply a.eq_refl.
assert (InA eqA x0 (a :: l)).
apply InA_cons_hd.
exact H2.
intuition.
intuition.
Defined.

Theorem no_dup_elements : forall x : SOL_MAP_TYPE, NoDup (SOL_MAP.elements x).
intros.
generalize (SOL_MAP.elements_3w).
intros.
assert (forall m, NoDupA (SOL_MAP.eq_key (elt:=Z)) (SOL_MAP.elements (elt:=Z) m) -> NoDup (SOL_MAP.elements m)).
intros.
induction H0.
apply NoDup_nil.
apply NoDup_cons.
apply in_a_eq_in.
apply H0.
apply IHNoDupA.
apply H0.
apply H.
Defined.

Fixpoint term_value (term : list (@EquationTerm t)) (sol : SOL_MAP_TYPE) : option Z :=
         match term with
         | nil => Some 0%Z
         | h :: t =>
             let this_term := match h with
                                        | NegVar t0 => match SOL_MAP.find t0 sol with
                                                                 | Some z => Some (- z)%Z
                                                                 | None => None
                                                                end
                                        | Var t0 => SOL_MAP.find t0 sol
                                        | Const z => Some z
                                     end in
             match this_term with
              | Some z => match term_value t sol with
                                    | Some rz => Some (z + rz)%Z
                                    | None => None
                                  end
              | None => Some 0%Z
             end
         end.

Definition valid_solution_equ (log : @Equation t) (sol : SOL_MAP_TYPE) : option bool :=
      match log with
       | LE l l0 =>
           match term_value l sol with
            | Some z =>
                match term_value l0 sol with
                 | Some z0 => if Z_le_gt_dec z z0 then Some true else Some false
                 | None => None
                end
           | None => None
          end
      end.

Fixpoint valid_solution_log (log : @Logic t) (sol : SOL_MAP_TYPE) : option bool :=
  match log with
   | Eq e => valid_solution_equ e sol
   | Not log0 => match (valid_solution_log log0 sol) with
                           | Some b => Some (negb b)
                           | None => None
                         end
   | And l => fold_left (fun (acc : option bool) (sl : Logic) =>
                                    match acc with
                                      | Some accb =>
                                             match valid_solution_log sl sol with
                                              | Some b => Some (andb b accb)
                                              | None => None
                                             end
                                      | None => None
                                    end) l (Some true)
   | Or l => fold_left (fun (acc : option bool) (sl : Logic) =>
                                    match acc with
                                      | Some accb =>
                                              match valid_solution_log sl sol with
                                                 | Some b => Some (orb b accb)
                                                 | None => None
                                              end
                                      | None => None
                                    end) l (Some false)
  end.

Definition valid_solution (log : @Logic t) (sol : SOL_MAP_TYPE) : bool :=
  match valid_solution_log log sol with
    | Some b => b
    | None => false
  end.

Lemma foldl_idemp : forall y s, fold_left (fun (acc : option bool) (sl : Logic) =>
         match acc with
         | Some accb =>
             match valid_solution_log sl s with
             | Some b0 => Some (andb b0 accb)
             | None => None
             end
         | None => None
         end) y None = None.
intro y.
induction y.
simpl.
reflexivity.
intros.
simpl.
rewrite IHy.
reflexivity.
Defined.

Theorem valid_solution_and : forall x : @Logic t, forall y : list (@Logic t), forall s : SOL_MAP_TYPE, andb (valid_solution x s) (valid_solution (And y) s) = (valid_solution (And (x::y)) s).
intros.
unfold valid_solution.
assert ({valid_solution_log x s = None} + {valid_solution_log x s <> None}).
decide equality.
decide equality.
destruct H.
simpl.
rewrite e.
simpl.
induction y.
simpl.
reflexivity.
simpl.
rewrite <- IHy.
reflexivity.
simpl.
remember (valid_solution_log x s).
destruct o.
clear n.
remember ((fun (acc : option bool) (sl : Logic) =>
     match acc with
     | Some accb =>
         match valid_solution_log sl s with
         | Some b0 => Some (andb b0 accb)
         | None => None
         end
     | None => None
     end)).
assert (forall a b, o (Some a) b = match (valid_solution_log b s) with | Some b0 => Some (andb b0 a) | None => None end).
intros.
rewrite Heqo0.
reflexivity.
destruct b.
reflexivity.
simpl.
induction y.
simpl.
reflexivity.
simpl.
rewrite H.
assert ({match valid_solution_log a s with
                | Some b0 => Some (andb b0 false)
                | None => None
                end = Some false} + {match valid_solution_log a s with
                | Some b0 => Some (andb b0 false)
                | None => None
                end = None}).
destruct (valid_solution_log a s).
left.
rewrite (Bool.andb_false_r).
reflexivity.
right.
reflexivity.
destruct H0.
rewrite e.
rewrite <- IHy.
reflexivity.
rewrite e.
clear e.
rewrite Heqo0.
rewrite foldl_idemp.
reflexivity.
destruct n.
reflexivity.
Defined.

Theorem valid_solution_not : forall x : @Logic t, forall s : SOL_MAP_TYPE, andb (valid_solution x s) (valid_solution (Not x) s) = false.
intro x.
induction x; intros.
unfold valid_solution.
simpl.
destruct (valid_solution_equ e s).
intuition.
reflexivity.
unfold valid_solution in *.
simpl.
destruct (valid_solution_log x s).
intuition.
reflexivity.
unfold valid_solution.
assert ((valid_solution_log (Not (And l)) s) = (match (valid_solution_log (And l) s) with
                                                                     | Some b => Some (negb b)
                                                                     | None => None
                                                                    end)).
reflexivity.
rewrite H.
clear H.
destruct (valid_solution_log (And l) s); intuition.
unfold valid_solution.
assert ((valid_solution_log (Not (Or l)) s) = (match (valid_solution_log (Or l) s) with
                                                                   | Some b => Some (negb b)
                                                                   | None => None
                                                                  end)).
reflexivity.
rewrite H.
clear H.
destruct (valid_solution_log (Or l) s); intuition.
Defined.

Lemma fold_left_idemp : forall x y : Type, forall f : x -> y -> x, forall i : x, (forall a : y, f i a = i) -> (forall (l : list y), fold_left f l i = i).
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite H.
exact IHl.
Defined.

Lemma fold_left_idemp_prop : forall x y : Type, forall P : x -> Prop, forall f : x -> y -> x, (forall i : x, forall a : y, P i -> P (f i a)) -> (forall (i : x), forall (l : list y), P i -> P (fold_left f l i)).
intros.
assert (forall x y : Type, forall (l : list y), forall (i : x), forall P : x -> Prop, forall f : x -> y -> x, (forall i : x, forall a : y, P i -> P (f i a)) -> (P i -> P (fold_left f l i))).
clear.
intros x y l.
induction l; intros; simpl.
exact H0.
apply IHl.
apply H.
apply H.
exact H0.
apply H1; auto.
Defined.

Fixpoint orbs (x : option bool) (y : option bool) : (option bool) :=
         match x with
         | Some b => match y with
                     | Some b0 => Some (b || b0)%bool
                     | None => None
                     end
         | None => None
         end.

Lemma fold_left_assoc: forall B t f h acc, (forall (l l2 : B) (a : option bool), f (f a l) l2 = f (f a l2) l) -> fold_left f (h::t) acc = (f (fold_left f t acc) h).
intros B t.
induction t; intros.
simpl.
reflexivity.
simpl.
rewrite <- IHt.
simpl.
rewrite H.
reflexivity.
apply H.
Defined.

Lemma orbs_and_or: forall y x sl, valid_solution_log (Or (x::y)) sl = orbs (valid_solution_log x sl) (valid_solution_log (Or y) sl).
intros.
assert (valid_solution_log (Or (x :: y)) sl =
                      fold_left (fun (acc : option bool) (s : Logic) =>
                                    match acc with
                                      | Some accb =>
                                              match valid_solution_log s sl with
                                                 | Some b => Some (orb b accb)
                                                 | None => None
                                              end
                                      | None => None
                                    end) (x :: y) (Some false)).
reflexivity.
rewrite H.
remember (fun (acc : option bool) (sl0 : Logic) =>
   match acc with
   | Some accb =>
       match valid_solution_log sl0 sl with
       | Some b => Some (b || accb)%bool
       | None => None
       end
   | None => None
   end) as f.
rewrite fold_left_assoc.
rewrite Heqf.
simpl.
rewrite <- Heqf.
destruct (valid_solution_log x sl); destruct (fold_left f y (Some false)); reflexivity.
intros.
rewrite Heqf.
destruct (valid_solution_log l sl).
destruct (valid_solution_log l2 sl).
destruct a.
rewrite Bool.orb_comm.
rewrite <- Bool.orb_assoc.
assert ( (orb b1 b0) =  (orb b0 b1) ).
apply Bool.orb_comm.
rewrite H0.
reflexivity.
reflexivity.
destruct a.
reflexivity.
reflexivity.
destruct a.
destruct (valid_solution_log l2 sl).
reflexivity.
reflexivity.
reflexivity.
Defined.

Theorem valid_solution_log_or : forall x : @Logic t, forall y : list (@Logic t), forall s : SOL_MAP_TYPE, forall a b c : bool, (((valid_solution_log x s = Some a) /\ (valid_solution_log (Or y) s = Some b)) \/ (valid_solution_log (Or (x::y)) s = Some c)) ->
                                                     (orb (valid_solution x s) (valid_solution (Or y) s) = (valid_solution (Or (x::y)) s)).
intros.
destruct H.
destruct H.
unfold valid_solution.
rewrite orbs_and_or.
rewrite H.
rewrite H0.
reflexivity.
unfold valid_solution.
rewrite orbs_and_or.
rewrite orbs_and_or in H.
destruct (valid_solution_log x s); destruct (valid_solution_log (Or y) s); try reflexivity; inversion H.
Defined.


End LabelledLogic.







