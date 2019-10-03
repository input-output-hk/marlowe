Require Import ZArith_base.
Require Import FSets.FMapAVL.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Structures.OrderedType.


Fixpoint conjWith {a : Type} (f : a -> a -> Prop) (x : list a) (y : list a) : Prop :=
  match x, y with
    | nil, nil => True
    | hx :: tx, hy :: ty => (f hx hy) /\ (conjWith f tx ty)
    | _, _ => False
  end.

Theorem conjWithSym :  forall a : Type, forall equ : a -> a -> Prop,  forall y x : list a, (forall x y : a, equ x y -> equ y x) -> @conjWith a equ x y -> @conjWith a equ y x.
intros a equ y.
induction y.
simpl.
intros.
destruct x.
simpl.
reflexivity.
simpl.
destruct H0.
intros.
simpl.
destruct x.
simpl.
destruct H0.
simpl.
simpl in H0.
destruct H0.
split.
apply H.
exact H0.
apply IHy.
apply H.
apply H1.
Defined.

Theorem conjWithTrans :  forall a : Type, forall equ : a -> a -> Prop,  forall y x z : list a, (forall x y z : a, equ x y -> equ y z -> equ x z) -> @conjWith a equ x y -> @conjWith a equ y z -> @conjWith a equ x z.
intros a equ y.
induction y; intros.
destruct x; destruct z; auto; inversion H0.
destruct x; destruct z; auto; inversion H1.
simpl in H0.
simpl in H1.
destruct H0.
destruct H1.
simpl.
split.
apply (H a1 a0 a2).
apply H0.
apply H1.
apply IHy.
apply H.
apply H4.
apply H5.
Defined.

Fixpoint conjWith2 {a : Type} (f : a -> a -> Prop) (g : a -> a -> Prop) (x : list a) (y : list a) : Prop :=
  match x, y with
    | nil, nil => False
    | hx :: tx, hy :: ty => (f hx hy) \/ ((g hx hy) /\ (conjWith2 f g tx ty))
    | nil, _ => True
    | _, _ => False
  end.

Theorem conjWith2Trans :  forall a : Type, forall equ : a -> a -> Prop, forall ltu : a -> a -> Prop,  forall z x y : list a, (forall x y z : a, equ x y -> equ y z -> equ x z) -> (forall x y z : a, ltu x y -> equ y z -> ltu x z) -> (forall x y z : a, equ x y -> ltu y z -> ltu x z) ->  (forall x y z : a, ltu x y -> ltu y z -> ltu x z) -> @conjWith2 a ltu equ x y -> @conjWith2 a ltu equ y z -> @conjWith2 a ltu equ x z.
intros a equ ltu z.
induction z.
intros.
destruct x.
simpl.
destruct y; auto.
destruct y; auto.
intros.
destruct y; auto.
destruct x; auto.
simpl in H1.
absurd True; auto.
destruct x; auto.
simpl.
simpl in *.
destruct H3; destruct H4.
left.
apply (H2 a2 a1 a0); auto.
destruct H4.
left.
apply (H0 a2 a1 a0); auto.
destruct H3.
left.
apply (H1 a2 a1 a0); auto.
destruct H3.
destruct H4.
right.
split.
apply (H a2 a1 a0); auto.
apply (IHz x y H H0 H1 H2).
apply H5.
apply H6.
Defined.

Theorem conjWith2LtNotEq :  forall a : Type, forall equ : a -> a -> Prop, forall ltu : a -> a -> Prop,  forall x y : list a, (forall x y : a, ltu x y -> ~ equ x y) -> @conjWith2 a ltu equ x y -> ~ @conjWith a equ x y.
intros a equ ltu x.
induction x; intros; intuition.
destruct y; auto.
destruct y; auto.
simpl in *.
destruct H0.
destruct H1.
apply (H a0 a1); auto.
destruct H0.
destruct H1.
apply (IHx y).
apply H.
apply H2.
apply H3.
Defined.

   Theorem compareZdec : forall x y : Z, {Z.lt x y} + {Z.eq x y} + {Z.gt x y}.
      intros x y.
      assert ({(x < y)%Z} + {(x >= y)%Z}).
      apply (Z_lt_ge_dec x y).
      destruct H.
      left; left; auto.
      assert ({(x = y)%Z} + {(x <> y)%Z}).
      apply (Z.eq_dec x y).
      destruct H.
      left; right; auto.
      right.
      auto with *.
      Defined.


   Theorem compareZ : forall x y : Z, Compare Z.lt Z.eq x y.
      intros.
      assert ({Z.lt x y} + {Z.eq x y} + {Z.gt x y}).
      apply compareZdec.
      destruct H.
      destruct s.
      apply LT.
      exact l.
      apply EQ.
      exact e.
      apply GT.
      auto with *.
    Defined.

  Theorem doubleInduction : forall {t : Type}, forall P : (list t -> list t -> Set), (forall y : list t, P nil y) -> (forall x : list t, P x nil) -> (forall x y : t, forall n m : list t, P n m -> P (x::n) (y::m)) -> forall n m : list t, P n m.
    intros t P X0 X1 X2 n.
    induction n.
    apply X0.
    intros.
    destruct m.
    apply X1.
    apply X2.
    apply IHn.
  Defined.


  Theorem eq_equiv : forall a b : list Z, (a = b) <-> conjWith Z.eq a b.
    intros.
    generalize b.
    clear b.
    induction a.
    destruct b.
    intuition.
    split.
    intros.
    rewrite <- H.
    intuition.
    intros.
    inversion H.
    intros.
    destruct b.
    simpl.
    intuition.
    inversion H.
    split; intros.
    rewrite <- H.
    simpl.
    intuition.
    apply IHa.
    reflexivity.
    inversion H.
    inversion H0.
    assert (a0 = b).
    apply IHa.
    exact H1.
    rewrite H3.
    reflexivity.
  Defined.

Open Scope Int_scope.

Module Type ListType.
  Parameter s : Type.
  Parameter Inline st : s -> list Z.
End ListType.

Module ListToOT (O : ListType) <: OrderedType.
  Include O.
  Definition t := s.
  Definition eq (a : t) (b : t): Prop := eq (st a) (st b).
  Definition lt (a : t) (b : t): Prop := conjWith2 Z.lt Z.eq (st a) (st b).

  Theorem eq_refl : forall x : t, eq x x.
    intros; reflexivity.
  Defined.
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
    intros.
    unfold eq.
    rewrite H.
    reflexivity.
  Defined.
  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    intros.
    unfold eq in *.
    rewrite <- H0.
    exact H.
  Defined.
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    intros.
    unfold lt in *.
    apply (conjWith2Trans Z Z.eq Z.lt (st z) (st x) (st y)); try intros x0 y0 z0.
    apply Z.eq_trans.
    intros.
    rewrite H2 in H1.
    exact H1.
    intros.
    rewrite <- H1 in H2.
    exact H2.
    intros.
    apply (Z.lt_trans x0 y0 z0).
    exact H1.
    exact H2.
    exact H.
    exact H0.
  Defined.
  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
     unfold lt.
     unfold eq.
     intros.
     intuition.
     apply eq_equiv in H0.
     apply (conjWith2LtNotEq Z Z.eq Z.lt (st x) (st y)).
     apply Z.lt_neq.
     apply H.
     exact H0.
   Defined.

  Theorem compareList : forall x y : list Z, {conjWith2 Z.lt Z.eq x y} + {x = y} +
{conjWith2 Z.lt Z.eq y x}.
    intros.
    apply (doubleInduction (fun (x y : list Z) => {conjWith2 Z.lt Z.eq x y} + {x = y} + {conjWith2 Z.lt Z.eq y x})).
    intros.
    destruct y0.
    simpl.
    left.
    right.
    reflexivity.
    simpl.
    left.
    left.
    exact I.
    destruct x0.
    simpl.
    left.
    right.
    reflexivity.
    simpl.
    right.
    exact I.
    intros.
    assert ({Z.lt x0 y0} + {Z.eq x0 y0} + {Z.gt x0 y0}).
    apply compareZdec.
    simpl.
    destruct H0.
    destruct s0.
    left.
    left.
    left.
    exact l.
    destruct H.
    destruct s0.
    left.
    left.
    right.
    split.
    exact e.
    exact c.
    left.
    right.
    rewrite e.
    rewrite e0.
    reflexivity.
    right.
    right.
    split.
    symmetry.
    exact e.
    exact c.
    right.
    left.
    apply Z.gt_lt.
    exact g.
  Defined.

  Theorem compareDec : forall x y : t, {lt x y} + {eq x y} + {lt y x}.
    intros.
    unfold lt.
    unfold eq.
    apply compareList.
  Defined.

   Theorem compare : forall x y : t, Compare lt eq x y.
     intros x y.
     assert ({lt x y} + {eq x y} + {lt y x}).
     apply compareDec.
     destruct H.
     destruct s0.
     apply LT.
     exact l.
     apply EQ.
     exact e.
     apply GT.
     exact l.
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    intros.
    assert ({lt x y} + {eq x y} + {lt y x}).
    apply compareDec.
    destruct H.
    destruct s0.
    right.
    apply lt_not_eq.
    exact l.
    left.
    exact e.
    right.
    intuition.
    apply eq_sym in H.
    absurd (eq y x).
    apply lt_not_eq.
    exact l.
    apply H.
  Defined.

Add Parametric Relation : t (eq)
         reflexivity proved by (eq_refl)
         symmetry proved by (eq_sym)
         transitivity proved by (eq_trans)
         as eq_setoid.

End ListToOT.

