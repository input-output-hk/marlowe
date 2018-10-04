Require Import Coq.Bool.Bool.
Require Import ZArith_base.
Require Import Coq.ZArith.Int.
Require Import OTFromList.
Require Import Semantics.
Require Import Coq.FSets.FSetProperties.
Require Import Inputs.

Open Scope Int_scope.

(* Set IdentCC *)
Module CID_LT <: ListType.
  Definition s := IdentCCT.
  Definition st (cct : IdentCCT) : list Z :=
     match cct with
      | IdentCC z => z :: nil
     end.
End CID_LT.
Module CID_OT := ListToOT(CID_LT).
Module CID_SET := FSetAVL.Make (CID_OT).
Definition emptyCIDSet := CID_SET.empty.
Module CID_PROP := WProperties_fun CID_OT CID_SET.
Module CID_FM := CID_PROP.FM.

(* Set (IdentPay, Person) *)
Module PID_LT <: ListType.
  Definition s : Type := (IdentPayT * Person).
  Definition st (cct : IdentPayT * Person) : list Z :=
     let (i, p) := cct in
       match i with
         | IdentPay z => z :: p :: nil
       end.
End PID_LT.
Module PID_OT := ListToOT(PID_LT).
Module PID_SET := FSetAVL.Make (PID_OT).
Definition emptyPIDSet := PID_SET.empty.
Module PID_PROP := WProperties_fun PID_OT PID_SET.
Module PID_FM := PID_PROP.FM.

(* Set (IdentChoice, Person) *)
Module ChID_LT <: ListType.
  Definition s : Type := (IdentChoiceT * Person).
  Definition st (cct : IdentChoiceT * Person) : list Z :=
     let (i, p) := cct in
       match i with
         | IdentChoice z => z :: p :: nil
       end.
End ChID_LT.
Module ChID_OT := ListToOT(ChID_LT).
Module ChID_SET := FSetAVL.Make (ChID_OT).
Definition emptyChIDSet := ChID_SET.empty.
Module ChID_PROP := WProperties_fun ChID_OT ChID_SET.
Module ChID_FM := ChID_PROP.FM.

(* Identifier accumulator *)

Record IdAccT := IdAcc {
                               cc : CID_SET.t;
                               rp : PID_SET.t
                            }.

Definition emptyIdAccT : IdAccT := {| cc := emptyCIDSet; rp := emptyPIDSet |}.

Definition unionIdAccT (acc1 : IdAccT) (acc2 : IdAccT) : IdAccT :=
   match acc1 with
       | {| cc := cc0; rp := rp0 |} =>
          match acc2 with
           | {| cc := cc1; rp := rp1 |} => {| cc := CID_SET.union cc0 cc1; rp := PID_SET.union rp0 rp1 |}
          end
   end.

Definition areDisjointAccT (acc1 : IdAccT) (acc2 : IdAccT) : bool := 
       match acc1 with
       | {| cc := cc0; rp := rp0 |} =>
           match acc2 with
           | {| cc := cc1; rp := rp1 |} =>
               CID_SET.is_empty (CID_SET.inter cc0 cc1) && PID_SET.is_empty (PID_SET.inter rp0 rp1)
           end
       end.

Definition addCommitIDifNotThere (ide : IdentCCT) (acc : option IdAccT) : option IdAccT :=
      match acc with
       | Some {| cc := cc0; rp := rp0 |} =>
           if CID_SET.mem ide cc0
           then None
           else Some {| cc := CID_SET.add ide cc0; rp := rp0 |}
       | None => None
      end.

Definition addCommitID (ide : IdentCCT) (acc : IdAccT) : IdAccT :=
      match acc with
       | {| cc := cc0; rp := rp0 |} => {| cc := CID_SET.add ide cc0; rp := rp0 |}
      end.

Definition addPaymentIDifNotThere (ide : IdentPayT) (per : Person) (acc : option IdAccT) : option IdAccT :=
      match acc with
       | Some {| cc := cc0; rp := rp0 |} =>
           if PID_SET.mem (ide, per) rp0
           then None
           else Some {| cc := cc0; rp := PID_SET.add (ide, per) rp0 |}
       | None => None
      end.

Definition addPaymentID (ide : IdentPayT) (per : Person) (acc : IdAccT) : IdAccT :=
      match acc with
       | {| cc := cc0; rp := rp0 |} => {| cc := cc0; rp := PID_SET.add (ide, per) rp0 |}
      end.

Definition combineIndependent (acc1 : option IdAccT) (acc2 : option IdAccT) : option IdAccT :=
    match acc1 with
       | Some i => match acc2 with
                            | Some i0 => Some (unionIdAccT i i0)
                            | None => None
                          end
       | None => match acc2 with
                          | Some _ | _ => None
                        end
    end.

Definition combineDependent (acc1 : option IdAccT) (acc2 : option IdAccT) : option IdAccT :=
     match acc1 with
       | Some i =>
           match acc2 with
             | Some i0 => if areDisjointAccT i i0 then Some (unionIdAccT i i0) else None
             | None => None
           end
       | None => match acc2 with
                          | Some _ | _ => None
                        end
     end.

Fixpoint collectIdentifiersIfUnique (c : Contract) : option IdAccT :=
    match c with
         | Null => Some emptyIdAccT
         | CommitCash identcc _ _ _ _ c1 c2 =>
             addCommitIDifNotThere identcc
               (combineDependent (collectIdentifiersIfUnique c1) (collectIdentifiersIfUnique c2))
         | RedeemCC _ c0 => collectIdentifiersIfUnique c0
         | Pay identpay _ p2 _ _ c0 => addPaymentIDifNotThere identpay p2 (collectIdentifiersIfUnique c0)
         | Both c1 c2 => combineDependent (collectIdentifiersIfUnique c1) (collectIdentifiersIfUnique c2)
         | Choice _ c1 c2 | When _ _ c1 c2 =>
             combineDependent (collectIdentifiersIfUnique c1) (collectIdentifiersIfUnique c2)
    end.

Definition areIdentifiersUnique (c : Contract) : bool :=
  match collectIdentifiersIfUnique c with
     | Some _ => true
     | None => false
  end.

Fixpoint removeDuplicateRedeem (acc : list Action) : list Action :=
         match acc with
         | nil => nil
         | a :: acc0 => match a with
                                | DuplicateRedeem i p => removeDuplicateRedeem acc0
                                | _ => a :: removeDuplicateRedeem acc0
                               end
         end.

Definition removeDuplicateRedeemFull (X : StateT * Contract * OST * AS) : (StateT * Contract * OST * AS) :=
  let (p, a) := X in
  let (p0, o) := p in
  let (s, c) := p0 in (s, c, o, removeDuplicateRedeem a).

Definition removeDuplicateRedeemBlock (X : StateT * Contract * AS) : (StateT * Contract * AS) :=
  let (p, a) := X in (p, removeDuplicateRedeem a).

Theorem fold_left_ind : forall {A} {B}, forall l : list B, forall f : A -> B -> A, forall P : A -> Prop, forall x : A, P x -> (forall a : A, forall b : B, P a -> P (f a b)) -> P (fold_left f l x).
intros A B l.
induction l; intros.
exact H.
simpl.
apply IHl.
apply H0.
exact H.
exact H0.
Defined.

Fixpoint collect_IdAccT_from_AS (ac : AS) : IdAccT :=
       match ac with
         | nil => emptyIdAccT
         | SuccessfulPay i _ p _ :: ac0 | ExpiredPay i _ p _ :: ac0 | FailedPay i _ p _ :: ac0 =>
            let acn := collect_IdAccT_from_AS ac0 in addPaymentID i p acn
         | SuccessfulCommit i _ _ :: ac0 => let acn := collect_IdAccT_from_AS ac0 in addCommitID i acn
         | CommitRedeemed _ _ _ :: ac0 | ExpiredCommitRedeemed _ _ _ :: ac0 | DuplicateRedeem _ _ :: ac0 |
           ChoiceMade _ _ _ :: ac0 => collect_IdAccT_from_AS ac0
       end.

Definition idAccTEquals (x y : IdAccT) : Prop.
destruct x.
destruct y.
exact (CID_SET.Equal cc0 cc1 /\ PID_SET.Equal rp0 rp1).
Defined.

Definition idAccTSubset(x y : IdAccT) : Prop.
destruct x.
destruct y.
exact (CID_SET.Subset cc0 cc1 /\ PID_SET.Subset rp0 rp1).
Defined.

Definition collect_IdAccT_from_State (st : StateT) : IdAccT :=
       match st with
       | {| sc := sc |} =>
           fold_left
             (fun (acc : IdAccT) (el : IdentCCT * CCStatus) =>
              match acc with
                | {| cc := cc0; rp := rp0 |} => {| cc := CID_SET.add (let (i, _) := el in i) cc0; rp := rp0 |}
              end) (SC_MAP.elements sc) emptyIdAccT
       end.

Lemma intersection_with_empty_IdAccT : forall x, areDisjointAccT x emptyIdAccT = true.
intros.
destruct x.
unfold areDisjointAccT.
unfold emptyIdAccT.
assert (CID_SET.Empty (CID_SET.inter cc0 emptyCIDSet)).
unfold CID_SET.Empty.
intros.
intuition.
apply CID_SET.inter_2 in H.
apply CID_SET.empty_1 in H.
exact H.
assert (PID_SET.Empty (PID_SET.inter rp0 emptyPIDSet)).
unfold PID_SET.Empty.
intros.
intuition.
apply PID_SET.inter_2 in H0.
apply PID_SET.empty_1 in H0.
exact H0.
intuition.
Defined.

Lemma subsetAndUnionWithNil : forall cc0 rp0 cc1 rp1 i0 i, {| cc := cc0; rp := rp0 |} = unionIdAccT i0 {| cc := cc1; rp := rp1 |} ->
                idAccTSubset (unionIdAccT {| cc := cc1; rp := rp1 |} (collect_IdAccT_from_AS nil)) {| cc := CID_SET.add i cc0; rp := rp0 |}.
intros.
unfold idAccTSubset.
simpl.
split.
unfold CID_SET.Subset.
intros.
assert (CID_SET.In a cc1).
assert (CID_SET.In a cc1 \/ CID_SET.In a emptyCIDSet).
apply (CID_SET.union_1).
exact H0.
destruct H1.
exact H1.
unfold emptyCIDSet in H1.
assert (forall a : CID_SET.elt, ~ CID_SET.In a CID_SET.empty).
apply (CID_SET.empty_1).
assert (~ CID_SET.In a CID_SET.empty).
apply H2.
contradiction.
unfold unionIdAccT in H.
destruct i0.
inversion H.
assert (CID_SET.In a (CID_SET.union cc2 cc1)).
apply CID_SET.union_3.
exact H1.
remember (CID_SET.union cc2 cc1).
apply (CID_SET.add_2).
exact H2.
unfold unionIdAccT in H.
destruct i0.
inversion H.
unfold PID_SET.Subset.
intros.
unfold emptyPIDSet in H0.
assert (PID_SET.In a rp1).
assert (PID_SET.In a rp1 \/ PID_SET.In a PID_SET.empty).
apply (PID_SET.union_1).
exact H0.
destruct H3.
exact H3.
assert (forall a : PID_SET.elt, ~PID_SET.In a PID_SET.empty).
apply (PID_SET.empty_1).
assert (~ PID_SET.In a PID_SET.empty).
apply H4.
contradiction.
apply (PID_SET.union_3).
exact H3.
Defined.

Lemma subsetUnionAndAdd : forall cc1 cc2 rp1 rp2 i, idAccTSubset (unionIdAccT {| cc := cc1; rp := rp1 |} {| cc := CID_SET.add i emptyCIDSet; rp := emptyPIDSet |})
                                                    {| cc := CID_SET.add i (CID_SET.union cc1 cc2); rp := PID_SET.union rp1 rp2 |}.
intros.
unfold idAccTSubset.
unfold CID_SET.Subset.
unfold PID_SET.Subset.
unfold unionIdAccT.
assert (CID_SET.Empty CID_SET.empty).
apply (CID_SET.empty_1).
assert (PID_SET.Empty PID_SET.empty).
apply (PID_SET.empty_1).
split; intros.
assert ({i = a} + {i <> a}).
decide equality.
apply Z.eq_dec.
destruct H2.
rewrite e.
apply (CID_SET.add_1).
reflexivity.
apply CID_SET.union_1 in H1.
destruct H1.
apply (CID_SET.add_2).
apply CID_SET.union_2.
exact H1.
apply CID_SET.add_3 in H1.
unfold emptyCIDSet in H1.
unfold CID_SET.Empty in H1.
assert (~ CID_SET.In a CID_SET.empty).
apply H.
contradiction.
destruct i.
destruct a.
intuition.
inversion H2.
rewrite H4 in n.
apply n.
reflexivity.
apply PID_SET.union_2.
assert (PID_SET.In a rp1 \/ PID_SET.In a emptyPIDSet).
apply PID_SET.union_1.
apply H1.
destruct H2.
exact H2.
unfold PID_SET.Empty in H0.
assert (~ PID_SET.In a emptyPIDSet).
apply H0.
contradiction.
Defined.

Lemma disjointIntersectionWithAlmostEmpty : forall cc0 rp0 i0 i1 i, {| cc := cc0; rp := rp0 |} = unionIdAccT i0 i1 -> false = CID_SET.mem i cc0 ->
                                                                              areDisjointAccT i0 {| cc := CID_SET.add i emptyCIDSet; rp := emptyPIDSet |} = true.
intros.
unfold areDisjointAccT.
destruct i0.
apply andb_true_iff.
split; [apply CID_SET.is_empty_1 | apply PID_SET.is_empty_1].
unfold CID_SET.Empty.
intros.
intuition.
assert ({a = i} + {a <> i}).
decide equality.
apply (Z.eq_dec).
destruct H2.
subst.
apply CID_SET.inter_1 in H1.
unfold unionIdAccT in H.
destruct i1.
inversion H.
clear H.
apply (CID_SET.union_2 cc2) in H1.
rewrite <- H3 in H1.
apply CID_SET.mem_1 in H1.
rewrite H1 in H0.
discriminate H0.
assert (~ CID_SET.In a (CID_SET.add i emptyCIDSet)).
intuition.
assert (CID_SET.Empty emptyCIDSet).
apply (CID_SET.empty_1).
unfold CID_SET.Empty in H3.
apply (H3 a).
apply (@CID_SET.add_3 emptyCIDSet i a).
destruct i.
destruct a.
intuition.
inversion H4.
rewrite H6 in n.
apply n.
reflexivity.
exact H2.
apply H2.
apply (CID_SET.inter_2 (s := cc1)).
exact H1.
unfold PID_SET.Empty.
intros.
assert (PID_SET.Empty emptyPIDSet).
apply (PID_SET.empty_1).
unfold PID_SET.Empty in H1.
intuition.
apply (PID_SET.inter_2) in H2.
apply (H1 a).
exact H2.
Defined.

Lemma disjointIntersectionWithAlmostEmpty2 : forall cc0 rp0 i p0, false = PID_SET.mem (i, p0) rp0 ->
                                                                         areDisjointAccT {| cc := cc0; rp := rp0 |} {| cc := emptyCIDSet; rp := PID_SET.add (i, p0) emptyPIDSet |} = true.
intros.
unfold areDisjointAccT.
apply andb_true_iff.
split; [apply CID_SET.is_empty_1 | apply PID_SET.is_empty_1].
intuition.
unfold PID_SET.Empty.
intros.
intuition.
assert ({a = (i, p0)} + {a <> (i, p0)}).
decide equality.
apply (Z.eq_dec).
decide equality.
apply (Z.eq_dec).
destruct H1.
subst.
apply PID_SET.inter_1 in H0.
destruct i.
apply PID_SET.mem_1 in H0.
rewrite H0 in H.
discriminate H.
assert (~ PID_SET.In a (PID_SET.add (i, p0) emptyPIDSet)).
intuition.
assert (PID_SET.Empty emptyPIDSet).
apply (PID_SET.empty_1).
unfold PID_SET.Empty in H2.
apply (H2 a).
apply (@PID_SET.add_3 emptyPIDSet (i, p0) a).
destruct a.
destruct i.
destruct i0.
intuition.
inversion H3.
rewrite H5 in n.
rewrite H6 in n.
apply n.
reflexivity.
exact H1.
apply H1.
apply (PID_SET.inter_2 (s := rp0)).
exact H0.
Defined.

Lemma subsetOfItselfAndUnionWithNil : forall x, idAccTSubset (unionIdAccT x emptyIdAccT) x.
intros.
unfold idAccTSubset.
unfold unionIdAccT.
unfold emptyIdAccT.
destruct x.
split.
rewrite (CID_PROP.empty_union_2).
apply CID_PROP.FM.Subset_refl.
unfold emptyCIDSet.
apply (CID_SET.empty_1).
rewrite (PID_PROP.empty_union_2).
apply PID_PROP.FM.Subset_refl.
unfold emptyPIDSet.
apply (PID_SET.empty_1).
Defined.

Lemma disjointWithEmpty : forall x, areDisjointAccT x emptyIdAccT = true.
intros.
unfold areDisjointAccT.
unfold emptyIdAccT.
destruct x.
apply andb_true_intro.
split.
apply CID_PROP.FM.is_empty_iff.
apply CID_PROP.empty_inter_2.
apply (CID_SET.empty_1).
apply PID_PROP.FM.is_empty_iff.
apply PID_PROP.empty_inter_2.
apply (PID_SET.empty_1).
Defined.

Lemma paySubsetSlightlySmaller : forall cc0 rp0 p0 i, idAccTSubset (unionIdAccT {| cc := cc0; rp := rp0 |} {| cc := emptyCIDSet; rp := PID_SET.add (i, p0) emptyPIDSet |})
                                                                                                    {| cc := cc0; rp := PID_SET.add (i, p0) rp0 |}.
split.
apply CID_PROP.subset_equal.
apply CID_PROP.empty_union_2.
apply CID_SET.empty_1.
rewrite <- PID_PROP.singleton_equal_add.
rewrite PID_PROP.union_sym.
rewrite <- PID_PROP.add_union_singleton.
apply PID_PROP.subset_equal.
apply PID_PROP.equal_refl.
Defined.


Lemma subset_of_disjoint_is_disjoint_CID_SET : forall cc0 cc1 cc2 cc3, CID_SET.Empty (CID_SET.inter cc0 cc1) -> CID_SET.Subset cc2 cc0 -> CID_SET.Subset cc3 cc1 -> CID_SET.Empty (CID_SET.inter cc2 cc3).
intros.
unfold CID_SET.Empty in *.
unfold CID_SET.Subset in *.
intros.
intuition.
assert (CID_SET.In a cc2).
apply (@CID_SET.inter_1 cc2 cc3 a).
exact H2.
assert (CID_SET.In a cc3).
apply (@CID_SET.inter_2 cc2 cc3 a).
exact H2.
assert (CID_SET.In a cc0).
apply H0.
apply H3.
assert (CID_SET.In a cc1).
apply H1.
apply H4.
apply (H a).
apply (CID_SET.inter_3).
exact H5.
exact H6.
Defined.

Lemma subset_of_disjoint_is_disjoint_PID_SET : forall rp0 rp1 rp2 rp3, PID_SET.Empty (PID_SET.inter rp0 rp1) -> PID_SET.Subset rp2 rp0 -> PID_SET.Subset rp3 rp1 -> PID_SET.Empty (PID_SET.inter rp2 rp3).
intros.
unfold PID_SET.Empty in *.
unfold PID_SET.Subset in *.
intros.
intuition.
assert (PID_SET.In a rp2).
apply (@PID_SET.inter_1 rp2 rp3 a).
exact H2.
assert (PID_SET.In a rp3).
apply (@PID_SET.inter_2 rp2 rp3 a).
exact H2.
assert (PID_SET.In a rp0).
apply H0.
apply H3.
assert (PID_SET.In a rp1).
apply H1.
apply H4.
apply (H a).
apply (PID_SET.inter_3).
exact H5.
exact H6.
Defined.


Lemma subset_of_disjoint_is_disjoint : forall x x0 i i0, areDisjointAccT i i0 = true -> idAccTSubset x i -> idAccTSubset x0 i0 -> areDisjointAccT x x0 = true.
intros.
unfold areDisjointAccT in *.
unfold idAccTSubset in *.
destruct i.
destruct i0.
destruct x.
destruct x0.
destruct H0.
apply (andb_prop) in H.
destruct H.
apply (andb_true_intro).
split; [apply CID_SET.is_empty_1 | apply PID_SET.is_empty_1].
apply CID_SET.is_empty_2 in H.
destruct H1.
apply (subset_of_disjoint_is_disjoint_CID_SET cc0 cc1); assumption.
apply PID_SET.is_empty_2 in H3.
destruct H1.
apply (subset_of_disjoint_is_disjoint_PID_SET rp0 rp1); assumption.
Defined.

Lemma areDisjointAccT_comm : forall i i0, areDisjointAccT i i0 = areDisjointAccT i0 i.
intros.
unfold areDisjointAccT.
destruct i.
destruct i0.
assert (CID_SET.is_empty (CID_SET.inter cc0 cc1) = CID_SET.is_empty (CID_SET.inter cc1 cc0)).
rewrite CID_PROP.inter_sym.
reflexivity.
assert (PID_SET.is_empty (PID_SET.inter rp0 rp1) = PID_SET.is_empty (PID_SET.inter rp1 rp0)).
rewrite PID_PROP.inter_sym.
reflexivity.
rewrite H.
rewrite H0.
reflexivity.
Defined.

Definition IdAccT_Equal (x y : IdAccT) : Prop :=
       match x with
        | {| cc := cc0; rp := rp0 |} =>
           match y with
             | {| cc := cc1; rp := rp1 |} => CID_SET.Equal cc0 cc1 /\ PID_SET.Equal rp0 rp1
           end
      end.

Lemma IdAccT_Equal_refl : forall x : IdAccT, IdAccT_Equal x x.
intros.
destruct x.
simpl.
split.
apply CID_PROP.equal_refl.
apply PID_PROP.equal_refl.
Defined.

Lemma IdAccT_Equal_sym : forall x y : IdAccT, IdAccT_Equal x y -> IdAccT_Equal y x.
intros.
destruct x.
destruct y.
simpl.
intros; split; destruct H; apply CID_PROP.equal_sym in H; apply PID_PROP.equal_sym in H0; assumption.
Defined.

Lemma IdAccT_Equal_trans: forall x y z : IdAccT, IdAccT_Equal x y -> IdAccT_Equal y z -> IdAccT_Equal x z.
intros.
destruct x.
destruct y.
destruct z.
simpl.
unfold IdAccT_Equal in *.
split;
destruct H;
destruct H0.
apply (@CID_PROP.equal_trans cc0 cc1 cc2); assumption.
apply (@PID_PROP.equal_trans rp0 rp1 rp2); assumption.
Defined.


Add Parametric Relation : IdAccT (IdAccT_Equal)
  reflexivity proved by (IdAccT_Equal_refl)
  symmetry proved by (IdAccT_Equal_sym)
  transitivity proved by (IdAccT_Equal_trans)
  as eq_idacct_rel.

Add Morphism unionIdAccT
 with signature IdAccT_Equal ==> IdAccT_Equal ==> IdAccT_Equal
 as idacct_eq_union_mor.
intros.
unfold IdAccT_Equal in *.
unfold unionIdAccT in *.
destruct x.
destruct y.
destruct x0.
destruct y0.
destruct H.
destruct H0.
split.
rewrite H.
rewrite H0.
apply CID_PROP.equal_refl.
rewrite H1.
rewrite H2.
apply PID_PROP.equal_refl.
Defined.

Add Parametric Morphism (i : IdentPayT) (p : Person) :
  (addPaymentID i p) with signature (IdAccT_Equal ==> IdAccT_Equal) as idacct_eq_addpay_mor.
intros.
unfold IdAccT_Equal.
unfold addPaymentID.
destruct x.
destruct y.
inversion H.
split.
exact H0.
rewrite H1.
reflexivity.
Defined.

Add Parametric Morphism (i : IdentCCT) :
  (addCommitID i) with signature (IdAccT_Equal ==> IdAccT_Equal) as idacct_eq_addcc_mor.
intros.
unfold IdAccT_Equal.
unfold addCommitID.
destruct x.
destruct y.
inversion H.
split.
rewrite H0.
reflexivity.
rewrite H1.
reflexivity.
Defined.

Lemma IdAccT_Subset_refl : forall x : IdAccT, idAccTSubset x x.
intros.
destruct x.
simpl.
split.
apply CID_PROP.subset_refl.
apply PID_PROP.subset_refl.
Defined.

Lemma IdAccT_Subset_trans: forall x y z : IdAccT, idAccTSubset x y -> idAccTSubset y z -> idAccTSubset x z.
intros.
destruct x.
destruct y.
destruct z.
simpl.
unfold idAccTSubset in *.
split;
destruct H;
destruct H0.
apply (@CID_PROP.subset_trans cc0 cc1 cc2); assumption.
apply (@PID_PROP.subset_trans rp0 rp1 rp2); assumption.
Defined.

Add Parametric Relation : IdAccT (idAccTSubset)
  reflexivity proved by (IdAccT_Subset_refl)
  transitivity proved by (IdAccT_Subset_trans)
  as subset_idacct_rel.

Add Morphism unionIdAccT
 with signature IdAccT_Equal ==> IdAccT_Equal ==> idAccTSubset
 as idacct_sub_union_mor.
intros.
unfold IdAccT_Equal in *.
unfold unionIdAccT in *.
destruct x.
destruct y.
destruct x0.
destruct y0.
destruct H.
destruct H0.
split.
rewrite H.
rewrite H0.
apply CID_PROP.subset_refl.
rewrite H1.
rewrite H2.
apply PID_PROP.subset_refl.
Defined.


Instance proper_idAccTSubset : Proper (IdAccT_Equal ==> IdAccT_Equal ==> flip impl) idAccTSubset.
unfold Proper.
unfold respectful.
intros.
unfold impl.
unfold flip.
intros.
unfold idAccTSubset in *.
unfold IdAccT_Equal in *.
unfold idAccTSubset in *.
destruct x.
destruct y.
destruct x0.
destruct y0.
destruct H.
destruct H0.
destruct H1.
split.
rewrite H.
rewrite H0.
rewrite H1.
reflexivity.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
Defined.

Definition idAccTDisjoint (x y : IdAccT) : Prop := areDisjointAccT x y = true.

Theorem idAccTDisjoint_reflect : forall x y, reflect (idAccTDisjoint x y) (areDisjointAccT x y).
intros.
assert ({idAccTDisjoint x y} + {~ idAccTDisjoint x y}).
unfold idAccTDisjoint.
decide equality.
destruct H.
rewrite i.
apply ReflectT.
exact i.
remember (areDisjointAccT x y).
destruct b.
unfold idAccTDisjoint in n.
rewrite <- Heqb in n.
destruct n.
reflexivity.
apply ReflectF.
exact n.
Defined.

Lemma IdAccT_Disjoint_sym : forall x y : IdAccT, idAccTDisjoint x y -> idAccTDisjoint y x.
intros.
destruct (Bool.reflect_iff (idAccTDisjoint y x) (areDisjointAccT y x)).
apply idAccTDisjoint_reflect.
apply H1.
destruct (Bool.reflect_iff (idAccTDisjoint x y) (areDisjointAccT x y)).
apply idAccTDisjoint_reflect.
apply H2 in H.
clear H0 H1 H2 H3.
unfold areDisjointAccT in *.
destruct x.
destruct y.
rewrite andb_true_intro.
reflexivity.
apply andb_prop in H.
destruct H.
split.
rewrite (CID_PROP.inter_sym).
exact H.
rewrite (PID_PROP.inter_sym).
exact H0.
Defined.

Add Parametric Relation : IdAccT (idAccTDisjoint)
  symmetry proved by (IdAccT_Disjoint_sym)
  as disjoint_idacct_rel.

Instance proper_idAccTDisjoint : Proper (IdAccT_Equal ==> IdAccT_Equal ==> flip impl) idAccTDisjoint.
unfold Proper.
unfold respectful.
intros.
unfold impl.
unfold flip.
intros.
unfold idAccTDisjoint in *.
unfold IdAccT_Equal in *.
unfold areDisjointAccT in *.
destruct x.
destruct y.
destruct x0.
destruct y0.
destruct H.
destruct H0.
apply andb_true_intro.
apply andb_true_iff in H1.
destruct H1.
split.
rewrite H.
rewrite H0.
rewrite H1.
reflexivity.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
Defined.

Lemma addCommitIDifNotThereSomeAnd : forall i c x, Some x = addCommitIDifNotThere i c -> {y | Some y = c}.
intros.
unfold addCommitIDifNotThere in H.
destruct c;
try destruct i0;
try destruct (CID_SET.mem i cc0); inversion H.
exists {| cc := cc0; rp := rp0 |}.
reflexivity.
Defined.

Lemma addPaymentIDifNotThereSomeAnd : forall i p c x, Some x = addPaymentIDifNotThere i p c -> {y | Some y = c}.
intros.
unfold addPaymentIDifNotThere in H.
destruct c;
try destruct i0;
try destruct (CID_SET.mem i cc0); inversion H.
exists {| cc := cc0; rp := rp0 |}.
reflexivity.
Defined.

Lemma combineDependentAnd : forall c1 c2 x, Some x = combineDependent c1 c2 -> {y | Some (fst y) = c1 /\ Some (snd y) = c2}.
intros.
unfold combineDependent in H.
destruct c1;
destruct c2;
destruct areDisjointAccT; inversion H.
exists (i, i0).
split; reflexivity.
Defined.

Lemma addCommitIDifNotThereSomeSubset : forall i c x y, Some x = addCommitIDifNotThere i c -> Some y = c -> idAccTSubset y x.
intros.
unfold addCommitIDifNotThere in H.
destruct c;
try destruct i0;
try destruct (CID_SET.mem i cc0); inversion H.
inversion H0.
clear H.
clear H0.
unfold idAccTSubset.
split.
apply CID_PROP.subset_add_2.
reflexivity.
reflexivity.
Defined.

Lemma addPaymentIDifNotThereSubset : forall i p c x y, Some x = addPaymentIDifNotThere i p c -> Some y = c -> idAccTSubset y x.
intros.
unfold addPaymentIDifNotThere in H.
destruct c;
try destruct i0;
try destruct (CID_SET.mem i cc0); inversion H.
destruct PID_SET.mem.
inversion H.
unfold idAccTSubset.
destruct y.
destruct x.
inversion H.
inversion H0.
inversion H2.
split.
reflexivity.
clear H H0 H2.
apply PID_PROP.subset_add_2.
reflexivity.
Defined.

Lemma combineDependentSubset :  forall x y z c1 c2, Some x = combineDependent c1 c2 -> Some y = c1 -> Some z = c2 -> idAccTSubset y x /\ idAccTSubset z x.
intros.
unfold combineDependent in H.
rewrite <- H0 in H.
rewrite <- H1 in H.
destruct areDisjointAccT; inversion H.
unfold idAccTSubset.
unfold unionIdAccT.
destruct x.
destruct y.
destruct z.
split.
split.
apply CID_PROP.union_subset_1.
apply PID_PROP.union_subset_1.
split.
apply CID_PROP.union_subset_2.
apply PID_PROP.union_subset_2.
Defined.

Lemma subsetOfUnion : forall x0 x1 x, idAccTSubset x0 x -> idAccTSubset x1 x -> idAccTSubset (unionIdAccT x0 x1) x.
intros.
unfold idAccTSubset in *.
unfold unionIdAccT.
destruct x0.
destruct x.
destruct x1.
destruct H.
destruct H0.
split.
apply CID_PROP.union_subset_3; assumption.
apply PID_PROP.union_subset_3; assumption.
Defined.

Ltac case_an expr n := let b := fresh in remember (expr) as b eqn: n; destruct b.
Ltac dup hyp name := generalize hyp; intro name.

Lemma sub_contract_is_still_unique : forall  c2 x inp c0 s0 a0 s os, Some x = collectIdentifiersIfUnique c2 -> (s0, c0, a0) = step inp s c2 os -> {y | Some y = collectIdentifiersIfUnique c0 /\ idAccTSubset y x}.
induction c2; intros.
(* Null *)
simpl in H0.
exists emptyIdAccT.
inversion H0.
split.
reflexivity.
inversion H.
reflexivity.
(* CommitCash *)
dup H Heqold_x.
simpl in H.
assert {y | Some y = (combineDependent (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2))}.
apply (addCommitIDifNotThereSomeAnd i _ x).
exact H.
destruct X.
assert ({y | Some (fst y) = (collectIdentifiersIfUnique c2_1) /\ Some (snd y) = (collectIdentifiersIfUnique c2_2)}).
apply (combineDependentAnd _ _ x0).
exact e.
destruct X.
destruct a.
destruct x1.
simpl in H1.
simpl in H2.
simpl in H0.
case_an (expired (blockNumber os) t || expired (blockNumber os) t0) if_cond1.
rewrite orb_comm in if_cond1.
rewrite <- if_cond1 in H0.
exists i1.
inversion H0.
rewrite <- H2.
split.
reflexivity.
transitivity x0.
assert (idAccTSubset i0 x0 /\ idAccTSubset i1 x0).
apply (combineDependentSubset x0 i0 i1 (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2)); assumption.
destruct H3.
exact H7.
apply (addCommitIDifNotThereSomeSubset i (combineDependent (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2))); assumption.
destruct (CC_SET.mem (CC i p (evalMoney s m) t0) (Semantics.cc inp)).
rewrite orb_comm in if_cond1.
rewrite <- if_cond1 in H0.
exists i0.
inversion H0.
rewrite <- H1.
split.
reflexivity.
transitivity x0.
assert (idAccTSubset i0 x0 /\ idAccTSubset i1 x0).
apply (combineDependentSubset x0 i0 i1 (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2)); assumption.
destruct H3.
exact H3.
apply (addCommitIDifNotThereSomeSubset i (combineDependent (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2))); assumption.
inversion H0.
rewrite <- Heqold_x.
exists x.
split; reflexivity.
(* RedeemCC *)
Ltac solve hyp e x := inversion hyp; subst; try rewrite <- e; exists x; split; (try reflexivity; try assumption).
dup H Heqold_x.
simpl in H.
simpl in H0.
case_an (SC_MAP.find i (sc s)) match_arg1.
destruct c.
case_an c match_arg2.
case_an (RC_SET.mem (RC i p c1) (rc inp)) if_arg1.
solve H0 e x.
solve H0 e x.
solve H0 e x.
solve H0 e x.
(* Pay *)
dup H Heqold_x.
simpl in H.
assert {y | Some y = collectIdentifiersIfUnique c2}.
apply (addPaymentIDifNotThereSomeAnd i p0 _ x); assumption.
destruct X.
assert (idAccTSubset x0 x).
apply (addPaymentIDifNotThereSubset i p0 (collectIdentifiersIfUnique c2) x x0); assumption.
simpl in H0.
case_an (expired (blockNumber os) t) if_cond1.
solve H0 e x0.
case_an (RP_MAP.find (elt:=Cash) (i, p0) (Semantics.rp inp)) match_val1.
case_an (c =? evalMoney s m)%Z if_cond2.
case_an (evalMoney s m >=? 0)%Z if_cond3.
case_an (stateUpdate s p p0 (blockNumber os) (evalMoney s m)) match_val2.
solve H0 e x0.
solve H0 e x0.
solve H0 e x0.
solve H0 e x.
solve H0 e x.
(* Both *)
dup H Heqold_x.
simpl in H.
assert ({y | Some (fst y) = (collectIdentifiersIfUnique c2_1) /\ Some (snd y) = (collectIdentifiersIfUnique c2_2)}).
apply (combineDependentAnd _ _ x); assumption.
destruct X.
destruct x0.
simpl in a.
destruct a.
assert (idAccTSubset i x /\ idAccTSubset i0 x).
apply (combineDependentSubset x i i0 (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2)); assumption.
destruct H3.
simpl in H0.
case_an (step inp s c2_1 os) step1_val.
destruct p.
case_an (step inp s1 c2_2 os) step2_val.
destruct p.
assert {y : IdAccT | Some y = collectIdentifiersIfUnique c /\ idAccTSubset y i}.
apply (IHc2_1 i inp c s1 a s os); assumption.
assert {y : IdAccT | Some y = collectIdentifiersIfUnique c1 /\ idAccTSubset y i0}.
apply (IHc2_2 i0 inp c1 s2 a1 s1 os); assumption.
destruct X.
destruct X0.
destruct a2.
destruct a3.
case_an (nulldec c) if_cond1.
solve H0 e x1.
transitivity i0; assumption.
case_an (nulldec c1) if_cond2.
solve H0 e x0.
transitivity i; assumption.
solve H0 e (unionIdAccT x0 x1).
simpl.
rewrite <- H5.
rewrite <- H7.
simpl.
simpl in Heqold_x.
rewrite <- H1 in Heqold_x.
rewrite <- H2 in Heqold_x.
simpl in Heqold_x.
case_an (areDisjointAccT x0 x1) are_disjoint_val.
reflexivity.
case_an (areDisjointAccT i i0) are_disjoint_val2; [ |inversion Heqold_x].
assert (areDisjointAccT x0 x1 = true).
apply (subset_of_disjoint_is_disjoint x0 x1 i i0); try symmetry; assumption.
rewrite H9 in are_disjoint_val.
discriminate are_disjoint_val.
apply subsetOfUnion.
transitivity i; assumption.
transitivity i0; assumption.
(* Choice *)
dup H Heqold_x.
simpl in H.
assert ({y | Some (fst y) = (collectIdentifiersIfUnique c2_1) /\ Some (snd y) = (collectIdentifiersIfUnique c2_2)}).
apply (combineDependentAnd _ _ x); assumption.
destruct X.
destruct x0.
simpl in a.
destruct a.
assert (idAccTSubset i x /\ idAccTSubset i0 x).
apply (combineDependentSubset x i i0 (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2)); assumption.
destruct H3.
simpl in H0.
case_an (interpretObs s o os) if_cond1.
solve H0 e i.
solve H0 e i0.
(* When *)
dup H Heqold_x.
simpl in H.
assert ({y | Some (fst y) = (collectIdentifiersIfUnique c2_1) /\ Some (snd y) = (collectIdentifiersIfUnique c2_2)}).
apply (combineDependentAnd _ _ x); assumption.
destruct X.
destruct x0.
simpl in a.
destruct a.
assert (idAccTSubset i x /\ idAccTSubset i0 x).
apply (combineDependentSubset x i i0 (collectIdentifiersIfUnique c2_1) (collectIdentifiersIfUnique c2_2)); assumption.
destruct H3.
simpl in H0.
case_an (expired (blockNumber os) t) if_cond1;
case_an (interpretObs s o os) if_cond2.
solve H0 e i0.
solve H0 e i0.
solve H0 e i.
solve H0 e x.
Defined.

Lemma unionWithNil : forall a, IdAccT_Equal (unionIdAccT (collect_IdAccT_from_AS nil) (a)) (a).
intros.
unfold IdAccT_Equal.
unfold unionIdAccT.
unfold collect_IdAccT_from_AS.
unfold emptyIdAccT.
destruct a.
split.
apply CID_PROP.empty_union_1.
apply CID_SET.empty_1.
apply PID_PROP.empty_union_1.
apply PID_SET.empty_1.
Defined.

Lemma add_before_or_after_union_pay : forall i p a b, IdAccT_Equal (addPaymentID i p (unionIdAccT a b))
                                                                                                  (unionIdAccT (addPaymentID i p a) b).
intros.
unfold IdAccT_Equal.
unfold addPaymentID.
unfold unionIdAccT.
destruct a.
destruct b.
split.
reflexivity.
symmetry.
apply PID_PROP.union_add.
Defined.

Lemma add_before_or_after_union_cc : forall i a b, IdAccT_Equal (addCommitID i (unionIdAccT a b))
                                                                                                  (unionIdAccT (addCommitID i a) b).
intros.
unfold IdAccT_Equal.
unfold addCommitID.
unfold unionIdAccT.
destruct a.
destruct b.
split.
symmetry.
apply CID_PROP.union_add.
reflexivity.
Defined.

Lemma collect_append_dist : forall a a0, IdAccT_Equal (collect_IdAccT_from_AS (a ++ a0)) (unionIdAccT (collect_IdAccT_from_AS a) (collect_IdAccT_from_AS a0)).
induction a.
induction a0.
simpl.
split.
rewrite CID_PROP.empty_union_1.
apply CID_PROP.equal_refl.
unfold emptyCIDSet.
apply CID_SET.empty_1.
rewrite PID_PROP.empty_union_1.
apply PID_PROP.equal_refl.
unfold emptyPIDSet.
apply PID_SET.empty_1.
rewrite app_nil_l in *.
rewrite unionWithNil.
reflexivity.
intros.
assert (collect_IdAccT_from_AS ((a :: a0) ++ a1) = collect_IdAccT_from_AS (a :: (a0 ++ a1))).
reflexivity.
rewrite H.
clear H.
assert (forall ac, collect_IdAccT_from_AS ac = match ac with
         | nil => emptyIdAccT
         | SuccessfulPay i _ p _ :: ac0 | ExpiredPay i _ p _ :: ac0 | FailedPay i _ p _ :: ac0 =>
             addPaymentID i p (collect_IdAccT_from_AS ac0)
         | SuccessfulCommit i _ _ :: ac0 => addCommitID i (collect_IdAccT_from_AS ac0)
         | CommitRedeemed _ _ _ :: ac0 | ExpiredCommitRedeemed _ _ _ :: ac0 | DuplicateRedeem _ _ :: ac0 |
           ChoiceMade _ _ _ :: ac0 => collect_IdAccT_from_AS ac0
       end).
destruct ac; reflexivity.
rewrite H in |- *.
rewrite (H (a :: a0)).
clear H.
destruct a.
rewrite IHa.
unfold IdAccT_Equal.
apply add_before_or_after_union_pay.
rewrite IHa.
unfold IdAccT_Equal.
apply add_before_or_after_union_pay.
rewrite IHa.
unfold IdAccT_Equal.
apply add_before_or_after_union_pay.
rewrite IHa.
unfold IdAccT_Equal.
apply add_before_or_after_union_cc.
rewrite IHa.
reflexivity.
rewrite IHa.
reflexivity.
rewrite IHa.
reflexivity.
rewrite IHa.
reflexivity.
Defined.

Ltac split_andH := match goal with h : _ /\ _ |- _ => destruct h end.
Ltac split_andG := match goal with |- _ /\ _ => split end.
Ltac split_ands := repeat split_andH; repeat split_andG.
Ltac unfold_idAccT := try unfold IdAccT_Equal in *; unfold idAccTSubset in *; unfold unionIdAccT in *; unfold areDisjointAccT in *; split_ands.
Ltac unfold_idAccT_nosplit := try unfold IdAccT_Equal in *; unfold idAccTSubset in *; unfold unionIdAccT in *.

Lemma IdAccT_union_subset_1 : forall x y, idAccTSubset x (unionIdAccT x y).
destruct x.
destruct y.
unfold_idAccT; [apply CID_PROP.union_subset_1 | apply PID_PROP.union_subset_1 ].
Defined.

Lemma IdAccT_union_subset_2 : forall x y, idAccTSubset y (unionIdAccT x y).
destruct x.
destruct y.
unfold_idAccT; [apply CID_PROP.union_subset_2 | apply PID_PROP.union_subset_2 ].
Defined.

Lemma IdAccT_union_subset_3 : forall x y z, idAccTSubset x z -> idAccTSubset y z -> idAccTSubset (unionIdAccT x y) z.
destruct x.
destruct y.
destruct z.
unfold_idAccT; intuition.
Defined.

Lemma IdAccT_union_subset_4 : forall x y z, idAccTSubset x y -> idAccTSubset (unionIdAccT x z) (unionIdAccT y z).
intros.
destruct x.
destruct y.
destruct z.
unfold_idAccT; [apply CID_PROP.union_subset_4 | apply PID_PROP.union_subset_4 ]; assumption.
Defined.

Lemma IdAccT_union_subset_5 : forall x y z, idAccTSubset x y -> idAccTSubset (unionIdAccT z x) (unionIdAccT z y).
intros.
destruct x.
destruct y.
destruct z.
unfold_idAccT; [apply CID_PROP.union_subset_5 | apply PID_PROP.union_subset_5 ]; assumption.
Defined.

Lemma IdAccT_subset_union_1 : forall x y z, (idAccTSubset (unionIdAccT x y) z  -> idAccTSubset x z).
intros.
destruct x.
destruct y.
destruct z.
unfold_idAccT.
unfold CID_SET.Subset in *.
intros.
apply H.
apply CID_SET.union_2; assumption.
unfold PID_SET.Subset in *.
intros.
apply H0.
apply PID_SET.union_2; assumption.
Defined.

Lemma IdAccT_subset_union_2 : forall x y z, (idAccTSubset (unionIdAccT x y) z  -> idAccTSubset y z).
intros.
destruct x.
destruct y.
destruct z.
unfold_idAccT.
unfold CID_SET.Subset in *.
intros.
apply H.
apply CID_SET.union_3; assumption.
unfold PID_SET.Subset in *.
intros.
apply H0.
apply PID_SET.union_3; assumption.
Defined.

Lemma idAccT_union_s_m_1 : forall x0 y y0, idAccTSubset x0 y0 -> (idAccTSubset x0 (unionIdAccT y y0)).
intros.
destruct x0.
destruct y.
destruct y0.
unfold_idAccT.
unfold CID_SET.Subset.
intros.
apply CID_SET.union_3.
apply H.
exact H1.
unfold PID_SET.Subset.
intros.
apply PID_SET.union_3.
apply H0.
exact H1.
Defined.

Lemma idAccT_union_s_m_2 : forall x y y0, idAccTSubset x y -> (idAccTSubset x (unionIdAccT y y0)).
intros.
destruct x.
destruct y.
destruct y0.
unfold_idAccT.
unfold CID_SET.Subset.
intros.
apply CID_SET.union_2.
apply H.
exact H1.
unfold PID_SET.Subset.
intros.
apply PID_SET.union_2.
apply H0.
exact H1.
Defined.

Lemma idAccT_union_refl : forall x, IdAccT_Equal x (unionIdAccT x x).
intros.
unfold_idAccT.
destruct x;intuition.
Defined.

Lemma idAccT_subset_replace_lhs : forall x y z, IdAccT_Equal x y -> idAccTSubset x z -> idAccTSubset y z.
intros.
unfold_idAccT.
destruct y.
destruct z.
destruct x.
destruct H.
inversion H0.
rewrite <- H2.
rewrite <- H.
rewrite <- H1.
rewrite <- H3.
split; reflexivity.
Defined.

Lemma subsets_and_union_Both : forall x x0 y y0 i i0, forall c1 c2, idAccTSubset (unionIdAccT x y0) i0 -> idAccTSubset (unionIdAccT x0 y) i ->
                                                     idAccTSubset (unionIdAccT (if nulldec c1 then x else if nulldec c2 then x0 else unionIdAccT x0 x)
                                                                                               (unionIdAccT y y0)) (unionIdAccT i i0).
intros.
apply IdAccT_union_subset_3.
apply IdAccT_subset_union_1 in H.
apply IdAccT_subset_union_1 in H0.
assert (idAccTSubset (unionIdAccT x0 x) (unionIdAccT i i0)).
apply IdAccT_union_subset_3.
apply idAccT_union_s_m_2.
exact H0.
apply idAccT_union_s_m_1.
exact H.
case_an (nulldec c1) ifcond1; [| case_an (nulldec c2) ifcond2]; try assumption.
apply idAccT_union_s_m_1.
exact H.
apply idAccT_union_s_m_2.
exact H0.
apply IdAccT_subset_union_2 in H.
apply IdAccT_subset_union_2 in H0.
apply IdAccT_union_subset_3.
apply idAccT_union_s_m_2.
exact H0.
apply idAccT_union_s_m_1.
exact H.
Defined.

Lemma union_disjoint_IdAccT : forall x0 x a0 a, idAccTDisjoint x0 (unionIdAccT a a0) ->
                                                                          idAccTDisjoint x (unionIdAccT a a0) ->
                                                                          idAccTDisjoint (unionIdAccT x0 x) (unionIdAccT a a0).
intros.
assert (forall x y, reflect (idAccTDisjoint x y) (areDisjointAccT x y)).
apply (idAccTDisjoint_reflect).
generalize (Bool.reflect_iff).
intros.
remember (unionIdAccT x0 x).
remember (unionIdAccT a a0).
rewrite (H1 (idAccTDisjoint i i0) (areDisjointAccT i i0)); [| apply X].
rewrite (H1 (idAccTDisjoint x0 i0) (areDisjointAccT x0 i0)) in H; [| apply X].
rewrite (H1 (idAccTDisjoint x i0) (areDisjointAccT x i0)) in H0; [| apply X].
destruct x0.
destruct x.
destruct a0.
destruct a.
subst.
clear X H1.
unfold_idAccT.
apply andb_true_iff in H0.
apply andb_true_iff in H.
destruct H0.
destruct H.
apply andb_true_intro.
split.
apply CID_SET.is_empty_1.
apply CID_SET.is_empty_2 in H.
apply CID_SET.is_empty_2 in H0.
clear H1.
clear H2.
unfold CID_SET.Empty in *.
intros.
intuition.
generalize (CID_SET.inter_1 H1).
generalize (CID_SET.inter_2 H1).
intros.
apply (CID_SET.union_1) in H2.
apply (CID_SET.union_1) in H3.
destruct H3.
apply (H a).
apply (CID_SET.inter_3).
exact H3.
destruct H2.
apply (CID_SET.union_2).
exact H2.
apply (CID_SET.union_3).
exact H2.
apply (H0 a).
apply (CID_SET.inter_3).
exact H3.
destruct H2.
apply (CID_SET.union_2).
exact H2.
apply (CID_SET.union_3).
exact H2.
apply PID_SET.is_empty_1.
apply PID_SET.is_empty_2 in H2.
apply PID_SET.is_empty_2 in H1.
clear H0.
clear H.
unfold PID_SET.Empty in *.
intros.
intuition.
generalize (PID_SET.inter_1 H).
generalize (PID_SET.inter_2 H).
intros.
apply (PID_SET.union_1) in H0.
apply (PID_SET.union_1) in H3.
destruct H3.
apply (H2 a).
apply (PID_SET.inter_3).
exact H3.
destruct H0.
apply (PID_SET.union_2).
exact H0.
apply (PID_SET.union_3).
exact H0.
apply (H1 a).
apply (PID_SET.inter_3).
exact H3.
destruct H0.
apply (PID_SET.union_2).
exact H0.
apply (PID_SET.union_3).
exact H0.
Defined.

Lemma disjoint_and_union_Both : forall a a0 c1 c2 x x0 i0 i, true = areDisjointAccT i i0 ->
                                                             idAccTSubset (unionIdAccT x a0) i0 ->
                                                             idAccTSubset (unionIdAccT x0 a) i ->
                                                             areDisjointAccT x a0 = true ->
                                                             areDisjointAccT x0 a = true ->
   idAccTDisjoint (if nulldec c1 then x else if nulldec c2 then x0 else unionIdAccT x0 x) (unionIdAccT a a0).
intros.
assert (idAccTDisjoint x (unionIdAccT a a0) /\ idAccTDisjoint x0 (unionIdAccT a a0)).
destruct x.
destruct x0.
destruct a.
destruct a0.
destruct i.
destruct i0.
split.
let x := match goal with |- idAccTDisjoint ?a _ => a end in
let y := match goal with |- idAccTDisjoint _ ?b => b end in
apply (@Bool.reflect_iff  (idAccTDisjoint x y) (areDisjointAccT x y)).
apply idAccTDisjoint_reflect.
unfold_idAccT.
symmetry in H.
apply andb_true_iff in H.
apply andb_true_iff in H2.
apply andb_true_iff in H3.
destruct H.
destruct H2.
destruct H3.
apply andb_true_intro.
split.
apply CID_SET.is_empty_1.
apply CID_SET.is_empty_2 in H.
apply CID_SET.is_empty_2 in H2.
apply CID_SET.is_empty_2 in H3.
unfold CID_SET.Empty in *.
unfold CID_SET.Subset in *.
clear H6 H5 H4 H7 H8.
intros.
intuition.
assert (CID_SET.In a cc0).
apply (CID_SET.inter_1) in H4.
exact H4.
assert (CID_SET.In a (CID_SET.union cc2 cc3)).
apply (CID_SET.inter_2) in H4.
exact H4.
apply (CID_SET.union_1) in H6.
destruct H6.
assert (CID_SET.In a cc4).
apply H1.
apply (CID_SET.union_3).
exact H6.
assert (CID_SET.In a cc5).
apply H0.
apply (CID_SET.union_2).
exact H5.
apply (H a).
apply (CID_SET.inter_3).
exact H7.
exact H8.
apply (H2 a).
apply (CID_SET.inter_3).
exact H5.
exact H6.
apply PID_SET.is_empty_1.
apply PID_SET.is_empty_2 in H6.
apply PID_SET.is_empty_2 in H7.
apply PID_SET.is_empty_2 in H8.
unfold PID_SET.Empty in *.
unfold PID_SET.Subset in *.
clear H H0 H1 H2 H3.
intros.
intuition.
assert (PID_SET.In a rp0).
apply (PID_SET.inter_1) in H.
exact H.
assert (PID_SET.In a (PID_SET.union rp2 rp3)).
apply (PID_SET.inter_2) in H.
exact H.
apply (PID_SET.union_1) in H1.
destruct H1.
assert (PID_SET.In a rp4).
apply H4.
apply (PID_SET.union_3).
exact H1.
assert (PID_SET.In a rp5).
apply H5.
apply (PID_SET.union_2).
exact H0.
apply (H6 a).
apply (PID_SET.inter_3).
exact H2.
exact H3.
apply (H7 a).
apply (PID_SET.inter_3).
exact H0.
exact H1.
unfold idAccTDisjoint in *.
unfold_idAccT.
symmetry in H.
apply andb_true_iff in H.
apply andb_true_iff in H2.
apply andb_true_iff in H3.
destruct H.
destruct H2.
destruct H3.
apply andb_true_intro.
split.
apply CID_SET.is_empty_1.
apply CID_SET.is_empty_2 in H.
apply CID_SET.is_empty_2 in H2.
apply CID_SET.is_empty_2 in H3.
unfold CID_SET.Empty in *.
unfold CID_SET.Subset in *.
clear H6 H5 H4 H7 H8.
intros.
intuition.
assert (CID_SET.In a cc1).
apply (CID_SET.inter_1) in H4.
exact H4.
assert (CID_SET.In a (CID_SET.union cc2 cc3)).
apply (CID_SET.inter_2) in H4.
exact H4.
apply (CID_SET.union_1) in H6.
destruct H6.
apply (H3 a).
apply (CID_SET.inter_3).
exact H5.
exact H6.
assert (CID_SET.In a cc5).
apply H0.
apply (CID_SET.union_3).
exact H6.
apply (H a).
apply (CID_SET.inter_3).
apply H1.
apply (CID_SET.union_2).
exact H5.
exact H7.
apply PID_SET.is_empty_1.
apply PID_SET.is_empty_2 in H6.
apply PID_SET.is_empty_2 in H7.
apply PID_SET.is_empty_2 in H8.
unfold PID_SET.Empty in *.
unfold PID_SET.Subset in *.
clear H H0 H1 H2 H3.
intros.
intuition.
assert (PID_SET.In a rp1).
apply (PID_SET.inter_1) in H.
exact H.
assert (PID_SET.In a (PID_SET.union rp2 rp3)).
apply (PID_SET.inter_2) in H.
exact H.
apply (PID_SET.union_1) in H1.
destruct H1.
apply (H8 a).
apply (PID_SET.inter_3); assumption.
assert (PID_SET.In a rp4).
apply H4.
apply (PID_SET.union_2).
exact H0.
assert (PID_SET.In a rp5).
apply H5.
apply (PID_SET.union_3).
exact H1.
apply (H6 a).
apply (PID_SET.inter_3).
exact H2.
exact H3.
destruct H4.
assert (idAccTDisjoint (unionIdAccT x0 x) (unionIdAccT a a0)).
apply union_disjoint_IdAccT; assumption.
case_an (nulldec c1) ifcond1;
try case_an (nulldec c2) ifcond2; assumption.
Defined.

Lemma union_with_empty : forall x, IdAccT_Equal (unionIdAccT x emptyIdAccT) x.
intros.
destruct x.
unfold emptyIdAccT.
unfold emptyCIDSet.
unfold emptyPIDSet.
unfold_idAccT.
apply CID_PROP.empty_union_2.
apply CID_SET.empty_1.
apply PID_PROP.empty_union_2.
apply PID_SET.empty_1.
Defined.

Lemma step_only_actions_if_in_contract : forall inp st c os nst nc nas oid aid,
                                                                 step inp st c os = (nst, nc, nas) -> collectIdentifiersIfUnique c = Some oid ->
                                                                 aid = collect_IdAccT_from_AS nas ->
                                                                 {nid | Some nid = collectIdentifiersIfUnique nc /\
                                                                           idAccTSubset (unionIdAccT nid aid) oid /\
                                                                           areDisjointAccT nid aid = true}.
intros inp st c.
generalize inp.
generalize st.
clear inp st.
induction c; intros.
(* Null *)
simpl in H.
inversion H.
subst.
inversion H0.
subst.
simpl.
exists emptyIdAccT.
split; try split; [ | try split]; try reflexivity.
simpl.
unfold CID_SET.Subset.
unfold PID_SET.Subset.
split; intros.
intuition.
intuition.
(* CommitCash *)
clear IHc1 IHc2.
dup H0 H0'.
simpl in H0.
unfold combineDependent in H0.
unfold addCommitIDifNotThere in H0.
case_an (collectIdentifiersIfUnique c1) Heqo;
try case_an (collectIdentifiersIfUnique c2) Heqo0;
try case_an (areDisjointAccT i0 i1) Heqb;
try case_an (unionIdAccT i0 i1) Heqi2; try inversion H0.
clear H3.
simpl in H.
case_eq (expired (blockNumber os) t || expired (blockNumber os) t0); intros; rewrite H2 in *.
(* CommitCash - Expired *)
rewrite orb_comm in H2.
rewrite H2 in H.
inversion H.
case_an (CID_SET.mem i cc0) Heqb0; try inversion H0.
clear H0.
rewrite H5 in Heqo0.
exists (i1).
rewrite <- Heqo0.
split.
reflexivity.
split.
subst.
destruct i1.
apply (subsetAndUnionWithNil cc0 rp0 cc1 rp1 i0 i).
exact Heqi2.
rewrite <- H6 in H1.
simpl in H1.
rewrite H1.
apply intersection_with_empty_IdAccT.
(* CommitCash - Not expired *)
rewrite orb_comm in H2.
rewrite H2 in H.
case_an (CID_SET.mem i cc0) Heqb0; try inversion H0.
clear H0.
case_an (CC_SET.mem (CC i p (evalMoney st m) t0) (Semantics.cc inp)) Heqb1.
(* CommitCash - Not expired - in input *)
exists i0.
rewrite Heqo.
inversion H.
split.
reflexivity.
rewrite H1.
rewrite <- H6.
split.
simpl.
destruct i0.
unfold unionIdAccT in Heqi2.
destruct i1.
inversion Heqi2.
clear Heqi2.
apply subsetUnionAndAdd.
simpl.
apply (disjointIntersectionWithAlmostEmpty cc0 rp0 i0 i1 i); assumption.
(* CommitCash - Not expired - not in input *)
exists oid.
inversion H.
rewrite H0'.
split.
reflexivity.
rewrite H4.
rewrite H1.
rewrite <- H6.
simpl.
split.
unfold idAccTSubset.
unfold unionIdAccT.
simpl.
rewrite <- H4.
unfold CID_SET.Subset.
unfold PID_SET.Subset.
split; intros.
assert ((CID_SET.In a (CID_SET.add i cc0)) \/ (CID_SET.In a emptyCIDSet)).
apply (CID_SET.union_1).
exact H0.
destruct H7.
exact H7.
apply (CID_SET.empty_1) in H7.
destruct H7.
assert ((PID_SET.In a rp0) \/ (PID_SET.In a emptyPIDSet)).
apply (PID_SET.union_1).
exact H0.
destruct H7.
exact H7.
apply (PID_SET.empty_1) in H7.
destruct H7.
apply intersection_with_empty_IdAccT.
(* RedeemCC *)
clear IHc.
dup H0 H0'.
simpl in H0.
simpl in H.
exists oid.
rewrite <- H0'.
Ltac unchanged sh ah := let a := fresh "a" in let b := fresh "b" in let c := fresh "c" in simpl; [inversion sh as [ (a, b, c) ]; simpl; split; [reflexivity | rewrite ah; rewrite <- c; simpl; split; [ apply subsetOfItselfAndUnionWithNil | apply disjointWithEmpty]] .. ].
destruct SC_MAP.find; [destruct c0; destruct c0; [destruct RC_SET.mem | ] | ] ; unchanged H H1.
(* Pay *)
clear IHc.
dup H0 H0'.
simpl in H0.
simpl in H.
unfold addPaymentIDifNotThere in H0.
case_an (collectIdentifiersIfUnique c) Heqo; [| inversion H0].
destruct i0.
remember (PID_SET.mem (i, p0) rp0).
inversion H0.
clear H3.
destruct b; [ inversion H0 | ].
case_an (expired (blockNumber os) t) Heqb0.
inversion H.
rewrite H1.
rewrite <- H5.
simpl.
rewrite <- H4.
rewrite <- Heqo.
exists {| cc := cc0; rp := rp0 |}.
split.
reflexivity.
inversion H0.
split.
apply paySubsetSlightlySmaller.
apply (disjointIntersectionWithAlmostEmpty2).
exact Heqb.
case_an (RP_MAP.find (elt:=Cash) (i, p0) (Semantics.rp inp)) Heqo0.
case_an (c0 =? evalMoney st m)%Z Heqb1.
case_an (evalMoney st m >=? 0)%Z Heqb2.
case_an (stateUpdate st p p0 (blockNumber os) (evalMoney st m)) Heqo1.
Ltac addIdPay cc0 rp0 hc hcc haid hoid := let a := fresh "a" in let b := fresh "b" in let c := fresh "c" in inversion hc as [(a, b, c)]; rewrite <- b; rewrite <- hcc; exists {| cc := cc0; rp := rp0 |}; rewrite haid; rewrite <- c; inversion hoid; split; [reflexivity | split; [simpl; apply paySubsetSlightlySmaller | apply disjointIntersectionWithAlmostEmpty2; assumption]].
addIdPay cc0 rp0 H Heqo H1 H0.
addIdPay cc0 rp0 H Heqo H1 H0.
addIdPay cc0 rp0 H Heqo H1 H0.
inversion H; rewrite H0'; exists oid; unchanged H H1.
inversion H; rewrite H0'; exists oid; unchanged H H1.
(* Both *)
dup H0 H0'.
simpl in H0.
simpl in H.
unfold combineDependent in H0.
remember (collectIdentifiersIfUnique c1);
destruct o;
try (remember (collectIdentifiersIfUnique c2);
destruct o);
try (remember (areDisjointAccT i i0);
destruct b);
try (remember (unionIdAccT i i0);
destruct i2); try inversion H0.
case_an (step inp st c1 os) Heqp.
destruct p.
assert (forall oid aid,
       Some i = Some oid ->
       aid = collect_IdAccT_from_AS a ->
       {nid : IdAccT |
       Some nid = collectIdentifiersIfUnique c /\
       idAccTSubset (unionIdAccT nid aid) oid /\ areDisjointAccT nid aid = true}) as IHc1'.
intros.
apply (IHc1 st inp os s c a oid0 aid0); try assumption.
symmetry.
assumption.
clear IHc1.
case_an (step inp s c2 os) Heqp0.
destruct p.
assert (forall oid aid,
       Some i0 = Some oid ->
       aid = collect_IdAccT_from_AS a0 ->
       {nid : IdAccT |
       Some nid = collectIdentifiersIfUnique c0 /\
       idAccTSubset (unionIdAccT nid aid) oid /\ areDisjointAccT nid aid = true}) as IHc2'.
intros.
apply (IHc2 s inp os s0 c0 a0); try assumption.
symmetry.
assumption.
inversion H.
rewrite <- H6 in H1.
assert({nid : IdAccT |
            Some nid = collectIdentifiersIfUnique c0 /\
            idAccTSubset (unionIdAccT nid (collect_IdAccT_from_AS a0)) i0 /\ areDisjointAccT nid (collect_IdAccT_from_AS a0) = true}).
apply IHc2'.
reflexivity.
reflexivity.
clear IHc2'.
assert({nid : IdAccT |
            Some nid = collectIdentifiersIfUnique c /\
            idAccTSubset (unionIdAccT nid (collect_IdAccT_from_AS a)) i /\ areDisjointAccT nid (collect_IdAccT_from_AS a) = true}).
apply IHc1'.
reflexivity.
reflexivity.
clear IHc1'.
destruct X.
destruct a1.
destruct H7.
destruct X0.
destruct a1.
destruct H10.
case_an (combineDependent (Some x0) (Some x)) Heqo1.
exists (if nulldec c then x else if nulldec c0 then x0 else i1).
split; [ | split].
inversion H0.
inversion H2.
inversion H9.
destruct (nulldec c); destruct (nulldec c0); try assumption.
rewrite Heqo1.
simpl.
rewrite <- H2.
rewrite <- H9.
simpl.
reflexivity.
simpl in Heqo1.
destruct (areDisjointAccT x0 x); [ | discriminate Heqo1].
inversion Heqo1.
rewrite H1.
rewrite collect_append_dist.
inversion H3.
apply subsets_and_union_Both; try assumption.
rewrite H1.
generalize (reflect_iff (idAccTDisjoint (if nulldec c then x else if nulldec c0 then x0 else i1) (collect_IdAccT_from_AS (a ++ a0)))
                (areDisjointAccT (if nulldec c then x else if nulldec c0 then x0 else i1) (collect_IdAccT_from_AS (a ++ a0)))).
intros.
rewrite <- H12; [ | apply idAccTDisjoint_reflect].
clear H12.
rewrite (collect_append_dist a a0).
unfold combineDependent in Heqo1.
case_an (areDisjointAccT x0 x) ifcond1; [ | discriminate Heqo1].
inversion Heqo1.
apply (disjoint_and_union_Both _ _ _ _ x x0 i0 i); assumption.
simpl in Heqo1.
assert (areDisjointAccT x0 x = true).
assert ({y | Some y = collectIdentifiersIfUnique c /\ idAccTSubset y i}).
apply (sub_contract_is_still_unique c1 i inp c s a st os); assumption.
assert ({y0 | Some y0 = collectIdentifiersIfUnique c0 /\ idAccTSubset y0 i0}).
apply (sub_contract_is_still_unique c2 i0 inp c0 s0 a0 s os); try assumption.
destruct X.
destruct a1.
destruct X0.
destruct a1.
rewrite <- H9 in H12.
rewrite <- H2 in H14.
inversion H12.
inversion H14.
subst.
clear H12 H14.
symmetry in Heqb.
apply (subset_of_disjoint_is_disjoint x0 x i i0); assumption.
rewrite H12 in Heqo1.
discriminate Heqo1.
(* Choice *)
clear IHc1 IHc2.
dup H0 H0'.
simpl in H0.
simpl in H.
unfold combineDependent in H0.
case_an (collectIdentifiersIfUnique c1) match_cond_1;
try case_an (collectIdentifiersIfUnique c2) match_cond_2;
try case_an (areDisjointAccT i i0) if_cond_1; try inversion H0.
case_an (interpretObs st o os) if_cond_2.
inversion H.
subst.
exists i.
rewrite match_cond_1.
split.
reflexivity.
split.
simpl.
apply idAccT_union_s_m_2.
apply subsetOfItselfAndUnionWithNil.
apply disjointWithEmpty.
inversion H.
subst.
exists i0.
rewrite match_cond_2.
split.
reflexivity.
split.
simpl.
apply idAccT_union_s_m_1.
apply subsetOfItselfAndUnionWithNil.
apply disjointWithEmpty.
(* When *)
clear IHc1 IHc2.
dup H0 H0'.
simpl in H0.
simpl in H.
unfold combineDependent in H0.
case_an (collectIdentifiersIfUnique c1) match_cond_1;
try case_an (collectIdentifiersIfUnique c2) match_cond_2;
try case_an (areDisjointAccT i i0) if_cond_1; try inversion H0.
case_an (expired (blockNumber os) t) if_cond_2.
inversion H.
subst.
exists i0.
rewrite match_cond_2.
split.
reflexivity.
split.
simpl.
apply idAccT_union_s_m_1.
apply subsetOfItselfAndUnionWithNil.
apply disjointWithEmpty.
case_an (interpretObs st o os) if_cond_3.
inversion H.
subst.
exists i.
split.
rewrite match_cond_1.
reflexivity.
split.
simpl.
apply idAccT_union_s_m_2.
apply subsetOfItselfAndUnionWithNil.
apply disjointWithEmpty.
inversion H.
subst.
exists (unionIdAccT i i0).
rewrite H0'.
split.
reflexivity.
split.
simpl.
rewrite union_with_empty.
reflexivity.
simpl.
apply disjointWithEmpty.
Defined.

