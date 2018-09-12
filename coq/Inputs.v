Require Import ZArith_base.
Require Import Coq.ZArith.Int.
Require Import FSets.FMapAVL.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Structures.Orders.
Require Import Coq.FSets.FMapList.
Require Import FSets.FSetAVL.
Require Import Lists.List.
Require Import Strings.String.
Require Import OTFromList.
Require Import Coq.Sorting.Mergesort.
Require Import Semantics.
Require Import LogicDefs.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.ZArith.Zorder.
Require Import Coq.Sorting.Permutation.

Open Scope Int_scope.

(* Analysis variable definition *)

Inductive InputIdentifier := CommitID : IdentCCT -> InputIdentifier
                                          | RedeemID : IdentCCT -> InputIdentifier
                                          | PaymentID : IdentPayT -> Person -> InputIdentifier
                                          | ChoiceID : IdentChoiceT -> Person -> InputIdentifier.


Module II_LT <: ListType.
  Definition s := InputIdentifier.
  Definition st (av : InputIdentifier) : list Z.
Ltac label num := let x := fresh "label" in let t := type of num in assert (t) as x; [exact num | apply cons; [exact x | ] ].
Ltac add_num num := apply cons; [exact num | ].
  destruct av; [label 1%Z | label 2%Z | label 3%Z | label 4%Z]; destruct i; add_num z; try add_num p; exact nil; exact nil.
Defined.
End II_LT.
Module II_OT := ListToOT(II_LT).

Inductive InputDetInfo := CommitDI : IdentCCT -> Person -> Timeout -> InputDetInfo
                                       | RedeemDI : IdentCCT -> Person -> InputDetInfo
                                       | PaymentDI : IdentPayT -> Person -> InputDetInfo
                                       | ChoiceDI : IdentChoiceT -> Person -> InputDetInfo.

(* Map InputIdentifier InputDetInfo *)
Module II_MAP := FMapAVL.Make(II_OT).
Definition emptyIIMap := II_MAP.empty InputDetInfo.
Definition II_MAP_TYPE := II_MAP.t InputDetInfo.

Definition getIdentifier (idi : InputDetInfo) : InputIdentifier :=
 match idi with
   | CommitDI i _ _ => CommitID i
   | RedeemDI i _ => RedeemID i
   | PaymentDI i p => PaymentID i p
   | ChoiceDI i p => ChoiceID i p
 end.

Inductive AnalysisVariable := CurrentBlock : AnalysisVariable
                                             | TempVar : Z -> AnalysisVariable
                                             | InputIssued : InputIdentifier -> AnalysisVariable
                                             | InputIssueBlock : InputIdentifier -> AnalysisVariable
                                             | CommitAmount : IdentCCT -> AnalysisVariable
                                             | RedeemAmount : IdentCCT -> AnalysisVariable
                                             | PaymentAmount : IdentPayT -> Person -> AnalysisVariable
                                             | ChoiceValue : IdentChoiceT -> Person -> AnalysisVariable.

Module AV_LT <: ListType.
  Definition s := AnalysisVariable.
  Definition st (av : AnalysisVariable) : list Z.
Ltac label num := let x := fresh "label" in let t := type of num in assert (t) as x; [exact num | apply cons; [exact x | ] ].
Ltac add_num num := apply cons; [exact num | ].
  destruct av; [label 1%Z | label 2%Z | label 3%Z | label 4%Z | label 5%Z | label 6%Z | label 7%Z | label 8%Z ].
  exact nil.
  add_num z; exact nil.
  destruct i; [label 1%Z | label 2%Z | label 3%Z | label 4%Z]; destruct i; add_num z; try add_num p; exact nil; exact nil.
  destruct i; [label 1%Z | label 2%Z | label 3%Z | label 4%Z]; destruct i; add_num z; try add_num p; exact nil; exact nil.
  destruct i; add_num z; exact nil.
  destruct i; add_num z; exact nil.
  destruct i; add_num z; add_num p; exact nil.
  destruct i; add_num z; add_num p; exact nil.
Defined.
End AV_LT.
Module AV_OT := ListToOT(AV_LT).


(** Canonical input lists **)

(* Input handlers *)

Definition addCC (com : CCT) (inp : InputT) : InputT :=
    match inp with
       | {| Semantics.cc := cc0; rc := rc; Semantics.rp := rp0; ic := ic |} =>
           {| Semantics.cc := CC_SET.add com cc0; rc := rc; Semantics.rp := rp0; ic := ic |}
    end.

Definition addRC (red : RCT) (inp : InputT) : InputT :=
     match inp with
       | {| Semantics.cc := cc0; rc := rc; Semantics.rp := rp0; ic := ic |} =>
           {| Semantics.cc := cc0; rc := RC_SET.add red rc; Semantics.rp := rp0; ic := ic |}
     end.

Definition addRP (ide : (IdentPayT * Person)) (cash : Cash) (inp : InputT) : InputT :=
  match inp with
     | {| Semantics.cc := cc0; rc := rc; Semantics.rp := rp0; ic := ic |} =>
          {| Semantics.cc := cc0; rc := rc; Semantics.rp := RP_MAP.add ide cash rp0; ic := ic |}
  end.

Definition addIC (ide : (IdentChoiceT * Person)) (cho : ConcreteChoice) (inp : InputT) : InputT :=
   match inp with
      | {| Semantics.cc := cc0; rc := rc; Semantics.rp := rp0; ic := ic |} =>
          {| Semantics.cc := cc0; rc := rc; Semantics.rp := rp0; ic := IC_MAP.add ide cho ic |}
   end.

Definition CCIn (ide : IdentCCT) (tra : InputT) : Prop :=
       match tra with
       | {| Semantics.cc := cc0 |} =>
           CC_SET.Exists
             (fun X : CC_SET.elt =>
              match X with
              | CC i _ _ _ => match ide with
                              | IdentCC z => match i with
                                             | IdentCC z0 => z = z0
                                             end
                              end
              end) cc0
       end.

Definition RCIn (ide : IdentCCT) (tra : InputT) : Prop :=
       match tra with
       | {| rc := rc |} =>
           RC_SET.Exists
             (fun X : RC_SET.elt =>
              match X with
              | RC i _ _ => match ide with
                            | IdentCC z => match i with
                                           | IdentCC z0 => z = z0
                                           end
                            end
              end) rc
       end.

Definition RPIn (ide : IdentPayT * Person) (tra : InputT) : Prop :=
match tra with
 | {| Semantics.rp := rp0 |} => RP_MAP.mem ide rp0 = true
end.

Definition ICIn (ide : IdentChoiceT * Person) (tra : InputT) : Prop :=
match tra with
 | {| ic := ic |} => IC_MAP.mem (elt:=ConcreteChoice) ide ic = true
end.

Definition InputIdentifierIn (ide : InputIdentifier) (tra : InputT) : Prop :=
 match ide with
   | CommitID i => CCIn i tra
   | RedeemID i => RCIn i tra
   | PaymentID i p => RPIn (i, p) tra
   | ChoiceID i p => ICIn (i, p) tra
 end.

Inductive NCCInL : IdentCCT -> list InputT -> Prop :=
  | NCCInL_nil : forall {x}, NCCInL x nil
  | NCCInL_cons : forall {x h l}, ~ CCIn x h -> NCCInL x l -> NCCInL x (h::l).
Inductive NRCInL : IdentCCT -> list InputT -> Prop :=
  | NRCInL_nil : forall {x}, NRCInL x nil
  | NRCInL_cons : forall {x h l}, ~ RCIn x h -> NRCInL x l -> NRCInL x (h::l).
Inductive NRPInL : (IdentPayT * Person) -> list InputT -> Prop :=
  | NRPInL_nil : forall {x}, NRPInL x nil
  | NRPInL_cons : forall {x h l}, ~ RPIn x h -> NRPInL x l -> NRPInL x (h::l).
Inductive NICInL : (IdentChoiceT * Person) -> list InputT -> Prop :=
  | NICInL_nil : forall {x}, NICInL x nil
  | NICInL_cons : forall {x h l}, ~ ICIn x h -> NICInL x l -> NICInL x (h::l).

Definition eq_Z_InputIdentifier (x : Z * InputIdentifier) (y : Z * InputIdentifier) : Prop :=
  let (_, i) := x in let (_, i0) := y in i = i0.

Inductive Input_list_NoDup : list (Z * InputIdentifier) -> list InputT -> Prop :=
    Input_list_NoDup_nil : Input_list_NoDup nil nil
  | Input_list_NoDup_cons_empty : forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT), Input_list_NoDup l1 l2 -> Input_list_NoDup l1 (emptyInput::l2)
  | Input_list_NoDup_addCC1 : forall {ide z}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z, CommitID ide) l1 ->
                                                  NCCInL ide l2 -> Input_list_NoDup l1 l2 ->
                                                  Input_list_NoDup ((z, CommitID ide) :: l1) l2
  | Input_list_NoDup_addCC2 : forall {ide z per cas tim}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z, CommitID ide) l1 ->
                                                  NCCInL ide (x :: l2) -> Input_list_NoDup l1 (x :: l2) ->
                                                  Input_list_NoDup l1 ((addCC (CC ide per cas tim) x) :: l2)
  | Input_list_NoDup_addRC1 : forall {ide z}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z, RedeemID ide) l1 ->
                                                  NRCInL ide l2 -> Input_list_NoDup l1 l2 ->
                                                  Input_list_NoDup ((z, RedeemID ide) :: l1) l2
  | Input_list_NoDup_addRC2 : forall {ide z per cas}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z, RedeemID ide) l1 ->
                                                  NRCInL ide (x :: l2) -> Input_list_NoDup l1 (x :: l2) ->
                                                  Input_list_NoDup l1 ((addRC (RC ide per cas) x) :: l2)
  | Input_list_NoDup_addRP1 : forall {ide per z}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z, PaymentID ide per) l1 ->
                                                  NRPInL (ide, per) l2 -> Input_list_NoDup l1 l2 ->
                                                  Input_list_NoDup ((z,  PaymentID ide per) :: l1) l2
  | Input_list_NoDup_addRP2 : forall {ide z per cas}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z,  PaymentID ide per) l1 ->
                                                  NRPInL (ide, per) (x :: l2) -> Input_list_NoDup l1 (x :: l2) ->
                                                  Input_list_NoDup l1 ((addRP (ide, per) cas x) :: l2)
  | Input_list_NoDup_addIC1 : forall {ide per z}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z, ChoiceID ide per) l1 ->
                                                  NICInL (ide, per) l2 -> Input_list_NoDup l1 l2 ->
                                                  Input_list_NoDup ((z,  ChoiceID ide per) :: l1) l2
  | Input_list_NoDup_addIC2 : forall {ide z per cas}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                              ~ InA eq_Z_InputIdentifier (z,  ChoiceID ide per) l1 ->
                                                  NICInL (ide, per) (x :: l2) -> Input_list_NoDup l1 (x :: l2) ->
                                                  Input_list_NoDup l1 ((addIC (ide, per) cas x) :: l2).

Inductive CanonicalInput : list InputT -> InputT -> Prop :=
 | EmptyCIL : CanonicalInput nil emptyInput
 | SingletonCI : CanonicalInput (emptyInput::nil) (emptyInput)
 | CloneCI : forall {a b}, CanonicalInput a b -> CanonicalInput (a ++ b::nil) b
 | AddCC : forall {ide per cash tim a b}, CanonicalInput a b -> ~ CCIn ide b -> CanonicalInput a (addCC (CC ide per cash tim) b)
 | AddRC : forall {ide per cash a b}, CanonicalInput a b -> ~ RCIn ide b -> CanonicalInput a (addRC (RC ide per cash) b)
 | AddRP : forall {ide per cash a b}, CanonicalInput a b -> ~ RPIn (ide, per) b -> CanonicalInput a (addRP (ide, per) cash b)
 | AddIC : forall {ide per cho a b}, CanonicalInput a b -> ~ ICIn (ide, per) b -> CanonicalInput a (addIC (ide, per) cho b).

(* Adapted from List.v *)
Lemma rev_list_ind2 : forall {A : Type},
                                  forall P:list A-> Type,
                                  P nil ->	(forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
                                	forall l:list A, P (rev l).
  induction l; auto.
Defined.

Theorem rev_ind2 : forall {A : Type}, forall P:list A -> Type, P nil ->(forall (x:A) (l:list A), P l -> P (l ++ (x::nil))) -> forall l:list A, P l.
  intros.
  generalize (rev_involutive l).
  intros E; rewrite <- E.
  apply (rev_list_ind2 P).
  auto.
  simpl.
  intros.
  apply (X0 a (rev l0)).
  auto.
Defined.
(* END of Adapted from List.v *)

Fixpoint right_decons_list {A : Type} (l : list A) : {d : (A * list A) | l = (snd d) ++ ((fst d)::nil)} + {l = nil}.
destruct l.
right.
reflexivity.
assert ({d : A * list A | l = snd d ++ fst d :: nil} + {l = nil}).
apply right_decons_list.
destruct X.
inversion s.
destruct x.
simpl in H.
rewrite H.
left.
exists (a0, a :: l0).
simpl.
reflexivity.
rewrite e.
left.
exists (a, nil).
simpl.
reflexivity.
Defined.

Module sol := LabelledLogic (AV_OT).

Module InputIdentifierLE <: TotalLeBool'.
Definition t := (Z * InputIdentifier : Type).
Definition leb (a : Z * InputIdentifier) (b : Z * InputIdentifier) : bool.
destruct a.
destruct b.
apply (Z.leb).
apply z.
apply z0.
Defined.

Definition leb_total : forall x y : t, leb x y = true \/ leb y x = true.
intros.
destruct x.
destruct y.
simpl.
assert ({z = z0} + {z <> z0}).
apply (Z.eq_dec).
destruct H.
subst.
left.
apply (Z.leb_refl).
assert (z < z0 \/ z0 < z)%Z.
apply not_Zeq.
exact n.
destruct H.
generalize (Z.leb_spec0 z z0).
intros.
generalize (Bool.reflect_iff).
intros.
apply H1 in H0.
clear H1.
left.
apply H0.
intuition.
right.
generalize (Z.leb_spec0 z0 z).
intros.
generalize (Bool.reflect_iff).
intros.
apply H1 in H0.
clear H1.
apply H0.
intuition.
Defined.

End InputIdentifierLE.

Module SortInputIdentifier := Sort(InputIdentifierLE).

Fixpoint getInputIdentifiers (l : (list (AnalysisVariable * Z))) : list InputIdentifier :=
 match l with
   | nil => nil
   | (InputIssued i, z) :: l0 => if Z_ge_lt_dec z 0 then i :: getInputIdentifiers l0 else getInputIdentifiers l0
   | (CurrentBlock, _) :: l0 | (TempVar _, _) :: l0 | (InputIssueBlock _, _) :: l0 |
     (CommitAmount _, _) :: l0 | (RedeemAmount _, _) :: l0 | (PaymentAmount _ _, _) :: l0 |
     (ChoiceValue _ _, _) :: l0 => getInputIdentifiers l0
 end.

Lemma getInputIdentifiers_NoIn : forall i z l, ~ InA (sol.SOL_MAP.eq_key (elt:=Z)) (InputIssued i, z) l -> ~ In i (getInputIdentifiers l).
intros.
induction l.
simpl.
intuition.
simpl.
destruct a; destruct k; try destruct (Z_ge_lt_dec z0 0); try apply IHl; [intuition | intuition | intuition | intuition | | intuition ..].
assert (~ (sol.SOL_MAP.eq_key (elt:=Z) (InputIssued i, z) (InputIssued i0, z0)) -> ~ In i (i0 :: getInputIdentifiers l)).
intuition.
simpl in H1.
destruct H1.
subst.
apply H0.
compute.
destruct i; destruct i; split; split; split; auto.
apply H2.
apply H1.
apply H0.
intuition.
Defined.

Lemma getInputIdentifiers_NoDup : forall s, NoDup (getInputIdentifiers (sol.SOL_MAP.elements (elt:=Z) s)).
intros.
generalize (sol.SOL_MAP.elements_3w s).
intros.
induction sol.SOL_MAP.elements.
simpl.
apply NoDup_nil.
inversion H.
subst.
simpl.
destruct a.
destruct k; try apply IHl; try apply H3.
destruct (Z_ge_lt_dec z 0); try apply IHl; try apply H3.
apply NoDup_cons; try apply IHl; try apply H3.
apply (getInputIdentifiers_NoIn i z l).
apply H2.
Defined.

Fixpoint addIssueBlock (l : list InputIdentifier) (s : sol.SOL_MAP_TYPE) : (list (Z * InputIdentifier)) :=
  match l with
   | nil => nil
   | i :: l0 =>
       match sol.SOL_MAP.find (InputIssueBlock i) s with
          | Some z => if Z_ge_lt_dec z 0 then (z, i) :: addIssueBlock l0 s else addIssueBlock l0 s
          | None => addIssueBlock l0 s
       end
  end.


Lemma addIssueBlock_NoInA : forall a l z s, ~ In a l -> ~ InA eq_Z_InputIdentifier (z, a) (addIssueBlock l s).
intros.
induction l.
simpl.
intuition.
generalize (InA_nil eq_Z_InputIdentifier).
intros.
destruct (H1 (z, a)).
apply H2.
apply H0.
simpl.
destruct (sol.SOL_MAP.find).
destruct (Z_ge_lt_dec z0 0).
intuition.
simpl in H.
assert (a0 = a \/ InA eq_Z_InputIdentifier (z, a) (addIssueBlock l s) -> False).
intros.
destruct H2.
apply H.
left.
exact H2.
apply H1.
exact H2.
apply H2.
apply InA_cons in H0.
destruct H0.
simpl in H0.
left.
symmetry.
exact H0.
right.
apply H0.
intuition.
intuition.
Defined.

Lemma addIssueBlock_NoDupA : forall l : (list InputIdentifier), forall s : sol.SOL_MAP_TYPE, NoDup l -> NoDupA (eq_Z_InputIdentifier) (addIssueBlock l s).
intros.
induction l.
simpl.
apply NoDupA_nil.
simpl.
destruct (sol.SOL_MAP.find).
destruct (Z_ge_lt_dec z 0).
apply NoDupA_cons.
inversion H.
apply addIssueBlock_NoInA.
exact H2.
apply IHl; apply NoDup_cons_iff in H; destruct H; exact H0.
apply IHl; apply NoDup_cons_iff in H; destruct H; exact H0.
apply IHl; apply NoDup_cons_iff in H; destruct H; exact H0.
Defined.

Theorem InA_perm : forall {A}, forall {a : A}, forall x y : list A, forall p : A -> A -> Prop, ~ InA p a x -> Permutation x y -> ~ InA p a y.
intros.
induction H0.
exact H.
intuition.
apply H2.
inversion H1.
subst.
assert (InA p a (x :: l)).
apply InA_cons_hd.
exact H4.
intuition.
exact H4.
intuition.
apply H.
inversion H0.
subst.
apply InA_cons_tl.
apply InA_cons_hd.
exact H2.
subst.
inversion H2.
subst.
apply InA_cons_hd.
exact H3.
apply InA_cons_tl.
apply InA_cons_tl.
exact H3.
intuition.
Defined.

Theorem NoDupA_perm : forall {A}, forall x y : list A, forall p : A -> A -> Prop, (forall b c, p b c -> p c b) -> NoDupA p x -> Permutation x y -> NoDupA p y.
intros A x y p s H H0.
induction H0.
apply NoDupA_nil.
inversion H.
apply NoDupA_cons.
apply (InA_perm l l').
exact H3.
exact H0.
apply IHPermutation.
exact H4.
apply NoDupA_cons.
inversion H.
intuition.
apply H2.
subst.
inversion H4.
subst.
apply InA_cons_hd.
apply s.
exact H1.
subst.
inversion H3.
intuition.
inversion H.
assert (~ InA p y l).
intuition.
intuition.
apply (NoDupA_cons).
exact H4.
inversion H3.
exact H8.
intuition.
Defined.

Lemma NoDupA_sort : forall x : list (Z * InputIdentifier), NoDupA (eq_Z_InputIdentifier) x -> NoDupA (eq_Z_InputIdentifier) (SortInputIdentifier.sort x).
intros.
assert (Permutation x (SortInputIdentifier.sort x)).
apply SortInputIdentifier.Permuted_sort.
apply (NoDupA_perm x).
intros.
unfold eq_Z_InputIdentifier in H1.
unfold eq_Z_InputIdentifier.
destruct b.
destruct c.
rewrite H1.
reflexivity.
exact H.
exact H0.
Defined.

Definition extractIdentifiers (s : sol.SOL_MAP_TYPE) : list (Z * InputIdentifier) :=
  SortInputIdentifier.sort (addIssueBlock (getInputIdentifiers (sol.SOL_MAP.elements s)) s).

Lemma extractIdentifiers_NoDupA : forall s : sol.SOL_MAP_TYPE, NoDupA eq_Z_InputIdentifier (extractIdentifiers s).
intros.
unfold extractIdentifiers.
apply (NoDupA_sort).
apply (addIssueBlock_NoDupA).
apply (getInputIdentifiers_NoDup).
Defined.

Theorem NoDupA_Input_list_NoDup : forall l : list (Z * InputIdentifier), NoDupA eq_Z_InputIdentifier l -> Input_list_NoDup l nil.
intro l.
induction l; intros.
apply Input_list_NoDup_nil.
destruct a.
destruct i.
inversion H.
apply Input_list_NoDup_addCC1.
exact emptyInput.
exact H2.
apply NCCInL_nil.
apply IHl.
apply H3.
inversion H.
apply Input_list_NoDup_addRC1.
exact emptyInput.
exact H2.
apply NRCInL_nil.
apply IHl.
apply H3.
inversion H.
apply Input_list_NoDup_addRP1.
exact emptyInput.
exact H2.
apply NRPInL_nil.
apply IHl.
apply H3.
inversion H.
apply Input_list_NoDup_addIC1.
exact emptyInput.
exact H2.
apply NICInL_nil.
apply IHl.
apply H3.
Defined.

Definition addInput (z : Z) (i : InputIdentifier) (i0 : InputDetInfo) (s : sol.SOL_MAP_TYPE) (ii : II_MAP_TYPE) (t : InputT) : InputT :=
       match i with
       | CommitID i1 =>
           match i0 with
           | CommitDI _ p t0 =>
               match sol.SOL_MAP.find (CommitAmount i1) s with
               | Some z0 => addCC (CC i1 p z0 t0) t
               | None => t
               end
           | _ => t
           end
       | RedeemID i1 =>
           match i0 with
           | RedeemDI _ p =>
               match sol.SOL_MAP.find (RedeemAmount i1) s with
               | Some z0 => addRC (RC i1 p z0) t
               | None => t
               end
           | _ => t
           end
       | PaymentID i1 p =>
           match i0 with
           | PaymentDI _ _ =>
               match sol.SOL_MAP.find (PaymentAmount i1 p) s with
               | Some z0 => addRP (i1, p) z0 t
               | None => t
               end
           | _ => t
           end
       | ChoiceID i1 p =>
           match i0 with
           | ChoiceDI _ _ =>
               match sol.SOL_MAP.find (ChoiceValue i1 p) s with
               | Some z0 => addIC (i1, p) z0 t
               | None => t
               end
           | _ => t
           end
       end.

Fixpoint instantiateList (cb : Z) (lb : Z) (l : list (Z * InputIdentifier)) (s : sol.SOL_MAP_TYPE) (ii : II_MAP_TYPE) (t : InputT) : list InputT :=
   match l with
    | nil => repeat t (Z.abs_nat (lb + 1 - cb))
    | (z, i) :: l0 =>
        if Z_ge_lt_dec z cb
        then
          if Z_ge_lt_dec z lb
          then instantiateList cb lb l0 s ii t
          else
             match II_MAP.find (elt:=InputDetInfo) i ii with
               | Some i0 => repeat t (Z.abs_nat (z - cb)) ++ instantiateList z lb l0 s ii (addInput z i i0 s ii t)
               | None => instantiateList cb lb l0 s ii t
             end
        else instantiateList cb lb l0 s ii t
   end.

Definition instantiate (s : sol.SOL_MAP_TYPE) (ii : II_MAP_TYPE) : list InputT :=
  match sol.SOL_MAP.find CurrentBlock s with
    | Some z => instantiateList 0 z (extractIdentifiers s) s ii emptyInput
    | None => nil
  end.

Lemma right_repeat_simpl : forall n : nat, forall A, forall a : A, repeat a (S n) = repeat a n ++ a :: nil.
intro n; induction n; intros.
simpl.
reflexivity.
simpl.
rewrite <- IHn.
simpl.
reflexivity.
Defined.

Lemma right_inversion : forall {A}, forall a c : list A, forall b : A, a ++ b :: nil = c -> {d | a ++ b :: nil = d ++ b :: nil}.
intros A a.
induction a; intros.
simpl in H.
simpl.
rewrite H.
exists nil.
reflexivity.
simpl.
exists (a :: a0).
reflexivity.
Defined.

Theorem app_split : forall A, forall b a c : list A, forall de : (list A * list A), a ++ b = c -> {de | a ++ b = (fst de) ++ (snd de) /\ a = (fst de) /\ b = (snd de) /\ (fst de) ++ (snd de) = c}.
intros A b.
destruct b; intros.
rewrite (app_nil_r) in *.
subst.
exists (c, nil).
simpl.
repeat split; rewrite (app_nil_r) in *; reflexivity.
exists (a0, a :: b).
simpl.
repeat split.
rewrite H.
reflexivity.
Defined.

Lemma clone_canonical : forall n r a0, CanonicalInput r a0 -> CanonicalInput (r ++ repeat a0 n) a0.
intros n0.
induction n0; intros.
rewrite app_nil_r.
exact H.
rewrite right_repeat_simpl.
rewrite (app_assoc).
apply (CloneCI).
apply IHn0.
exact H.
Defined.

Fixpoint Input_list_NoDup_size_aux (lp : list InputT) : nat :=
         match lp with
         | nil => 0
         | i :: lp0 =>
             Input_list_NoDup_size_aux lp0 +
             match i with
             | {| cc := cc; rc := rc; rp := rp; ic := ic |} =>
                 1 + (CC_SET.cardinal cc + (RC_SET.cardinal rc + (RP_MAP.cardinal rp + IC_MAP.cardinal ic)))
             end
         end.

Definition Input_list_NoDup_size (lp : (list (Z * InputIdentifier) * list InputT)) : nat :=
   let (l, l0) := lp in Datatypes.length l + Input_list_NoDup_size_aux l0.

Definition Input_list_NoDupOrder (lp1 lp2 : (list (Z * InputIdentifier) * list InputT)) : Prop := Input_list_NoDup_size lp1 < Input_list_NoDup_size lp2.

Lemma Input_list_NoDupOrder_wf' : forall siz, forall sv, Input_list_NoDup_size sv < siz -> Acc Input_list_NoDupOrder sv.
    induction siz.
    intros.
    inversion H.
    intros.
    apply (Acc_intro).
    intros.
    apply IHsiz.
    unfold Input_list_NoDupOrder in H0.
    intuition.
Defined.

Theorem Input_list_NoDupOrder_wf : well_founded Input_list_NoDupOrder.
  red; intro; eapply Input_list_NoDupOrder_wf'; eauto.
Defined.

Lemma Input_list_NoDup_step_order : forall a l x t0, Input_list_NoDupOrder ((a :: l),t0) ((a :: l), (x :: t0)).
intros.
induction t0.
unfold Input_list_NoDupOrder.
simpl.
remember (Datatypes.length l).
apply lt_n_S.
apply plus_lt_compat_l.
destruct x.
intuition.
unfold Input_list_NoDupOrder in *.
simpl.
remember (match a0 with
    | {| cc := cc; rc := rc; rp := rp; ic := ic |} =>
        S
          (CC_SET.cardinal cc +
           (RC_SET.cardinal rc + (RP_MAP.cardinal (elt:=Cash) rp + IC_MAP.cardinal (elt:=ConcreteChoice) ic)))
    end).
remember (match x with
    | {| cc := cc; rc := rc; rp := rp; ic := ic |} =>
        S
          (CC_SET.cardinal cc +
           (RC_SET.cardinal rc + (RP_MAP.cardinal (elt:=Cash) rp + IC_MAP.cardinal (elt:=ConcreteChoice) ic)))
    end).
apply lt_n_S.
apply plus_lt_compat_l.
rewrite <- plus_assoc.
apply plus_lt_compat_l.
destruct x.
intuition.
Defined.

Lemma Input_list_NoDup_step_order2 : forall a l x t0, Input_list_NoDupOrder (l,(x :: t0)) ((a :: l), (x :: t0)).
intros.
unfold Input_list_NoDupOrder.
unfold Input_list_NoDup_size.
simpl.
intuition.
Defined.

Lemma Input_list_NoDup_step_CC2 : forall {ide per cas tim}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                                          forall H2 : NCCInL ide (x :: l2), Input_list_NoDupOrder (l1, (x :: l2)) (l1, ((addCC (CC ide per cas tim) x) :: l2)).
intros.
unfold Input_list_NoDupOrder.
simpl.
destruct x.
unfold addCC.
rewrite CC_P.add_cardinal_2.
intuition.
intuition.
inversion H2.
apply H4.
simpl.
unfold CC_SET.Exists.
exists (CC ide per cas tim).
destruct ide.
split.
exact H.
reflexivity.
Defined.

Lemma Input_list_NoDup_step_RC2 : forall {ide per cas}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                                          forall H2 : NRCInL ide (x :: l2), Input_list_NoDupOrder (l1, (x :: l2)) (l1, ((addRC (RC ide per cas) x) :: l2)).
intros.
unfold Input_list_NoDupOrder.
simpl.
destruct x.
unfold addRC.
rewrite RC_P.add_cardinal_2.
intuition.
intuition.
inversion H2.
apply H4.
simpl.
unfold RC_SET.Exists.
exists (RC ide per cas).
destruct ide.
split.
exact H.
reflexivity.
Defined.

Lemma Input_list_NoDup_step_RP2 : forall {ide per cas}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                                          forall H2 : NRPInL (ide, per) (x :: l2) , Input_list_NoDupOrder (l1, (x :: l2)) (l1, ((addRP (ide, per) cas x) :: l2)).
intros.
unfold Input_list_NoDupOrder.
simpl.
destruct x.
unfold addRP.
rewrite (@RP_P.cardinal_2 Cash rp (RP_MAP.add (ide, per) cas rp) (ide,per) cas).
intuition.
intuition.
inversion H2.
apply H4.
simpl.
apply RP_MAP.mem_1.
exact H.
unfold RP_P.Add.
reflexivity.
Defined.

Lemma Input_list_NoDup_step_IC2 : forall {ide per cas}, forall x : InputT, forall (l1 :  list (Z * InputIdentifier)), forall (l2 : list InputT),
                                                          forall H2 : NICInL (ide, per) (x :: l2) , Input_list_NoDupOrder (l1, (x :: l2)) (l1, ((addIC (ide, per) cas x) :: l2)).
intros.
unfold Input_list_NoDupOrder.
simpl.
destruct x.
unfold addIC.
rewrite (@IC_P.cardinal_2 ConcreteChoice ic (IC_MAP.add (ide, per) cas ic) (ide,per) cas).
intuition.
intuition.
inversion H2.
apply H4.
simpl.
apply IC_MAP.mem_1.
exact H.
unfold IC_P.Add.
reflexivity.
Defined.

Theorem noDupRed2aux : forall y : (list (Z * InputIdentifier) * list InputT), (forall oh1 ot1 ol, (ol, (oh1 :: ot1)) = y -> Input_list_NoDup ol (oh1 :: ot1) -> Input_list_NoDup ol ot1).
apply (Fix Input_list_NoDupOrder_wf (fun y : (list (Z * InputIdentifier) * list InputT) => (forall oh1 ot1 ol, (ol, (oh1 :: ot1)) = y -> Input_list_NoDup ol (oh1 :: ot1) -> Input_list_NoDup ol ot1))).
intros.
destruct x as [tmp l].
inversion H1; try assumption.
apply (H (l1, (oh1 :: ot1))) in H4.
apply Input_list_NoDup_addCC1.
exact x.
apply H2.
inversion H3.
exact H11.
exact H4.
rewrite <- H0.
rewrite <- H5.
apply Input_list_NoDup_step_order2.
reflexivity.
apply (H (ol, (x :: ot1))) in H7.
exact H7.
rewrite <- H0.
rewrite <- H2.
apply Input_list_NoDup_step_CC2; assumption.
reflexivity.

apply (H (l1, (oh1 :: ot1))) in H4.
apply Input_list_NoDup_addRC1.
exact x.
apply H2.
inversion H3.
exact H11.
exact H4.
rewrite <- H0.
rewrite <- H5.
apply Input_list_NoDup_step_order2.
reflexivity.

apply (H (ol, (x :: ot1))) in H7.
exact H7.
rewrite <- H0.
rewrite <- H2.
apply Input_list_NoDup_step_RC2; assumption.
reflexivity.

apply (H (l1, (oh1 :: ot1))) in H4.
apply Input_list_NoDup_addRP1.
exact x.
apply H2.
inversion H3.
exact H11.
exact H4.
rewrite <- H0.
rewrite <- H5.
apply Input_list_NoDup_step_order2.
reflexivity.

apply (H (ol, (x :: ot1))) in H7.
exact H7.
rewrite <- H0.
rewrite <- H2.
apply Input_list_NoDup_step_RP2; assumption.
reflexivity.

apply (H (l1, (oh1 :: ot1))) in H4.
apply Input_list_NoDup_addIC1.
exact x.
apply H2.
inversion H3.
exact H11.
exact H4.
rewrite <- H0.
rewrite <- H5.
apply Input_list_NoDup_step_order2.
reflexivity.

apply (H (ol, (x :: ot1))) in H7.
exact H7.
rewrite <- H0.
rewrite <- H2.
apply Input_list_NoDup_step_IC2; assumption.
reflexivity.
Defined.

Theorem noDupRed2 h1 t1 l : Input_list_NoDup l (h1::t1) -> Input_list_NoDup l t1.
apply (noDupRed2aux (l, (h1 :: t1))).
reflexivity.
Defined.

Theorem noDupRedaux : forall y : (list (Z * InputIdentifier) * list InputT), (forall oh1 ot1 ol, ((oh1 :: ot1), ol) = y -> Input_list_NoDup (oh1 :: ot1) ol -> Input_list_NoDup ot1 ol).
apply (Fix Input_list_NoDupOrder_wf (fun y : (list (Z * InputIdentifier) * list InputT) => (forall oh1 ot1 ol, ((oh1 :: ot1), ol) = y -> Input_list_NoDup (oh1 :: ot1) ol -> Input_list_NoDup ot1 ol))).
intros.
inversion H1; try assumption.
apply Input_list_NoDup_cons_empty.
assert (Input_list_NoDupOrder (oh1 :: ot1, l2) x).
rewrite <- H0.
rewrite <- H4.
apply Input_list_NoDup_step_order.
apply (H (oh1 :: ot1, l2) H5 oh1 ot1 l2).
reflexivity.
exact H2.
apply (@Input_list_NoDup_addCC2 _ z); intuition.
assert (Input_list_NoDupOrder (oh1 :: ot1, x0 :: l2) x).
rewrite <- H0.
rewrite <- H6.
apply Input_list_NoDup_step_CC2.
exact H3.
apply (H (oh1 :: ot1, (x0 :: l2)) H7 oh1 ot1 (x0 :: l2)).
reflexivity.
exact H4.
apply (@Input_list_NoDup_addRC2 _ z); intuition.
assert (Input_list_NoDupOrder (oh1 :: ot1, x0 :: l2) x).
rewrite <- H0.
rewrite <- H6.
apply Input_list_NoDup_step_RC2.
exact H3.
apply (H (oh1 :: ot1, (x0 :: l2)) H7 oh1 ot1 (x0 :: l2)).
reflexivity.
exact H4.
apply (@Input_list_NoDup_addRP2 _ z); intuition.
assert (Input_list_NoDupOrder (oh1 :: ot1, x0 :: l2) x).
rewrite <- H0.
rewrite <- H6.
apply Input_list_NoDup_step_RP2.
exact H3.
apply (H (oh1 :: ot1, (x0 :: l2)) H7 oh1 ot1 (x0 :: l2)).
reflexivity.
exact H4.
apply (@Input_list_NoDup_addIC2 _ z); intuition.
assert (Input_list_NoDupOrder (oh1 :: ot1, x0 :: l2) x).
rewrite <- H0.
rewrite <- H6.
apply Input_list_NoDup_step_IC2.
exact H3.
apply (H (oh1 :: ot1, (x0 :: l2)) H7 oh1 ot1 (x0 :: l2)).
reflexivity.
exact H4.
Defined.

Theorem noDupRed h1 t1 l : Input_list_NoDup (h1::t1) l -> Input_list_NoDup t1 l.
intros.
apply (noDupRedaux ((h1 :: t1), l) h1 t1 l).
reflexivity.
exact H.
Defined.

Theorem Input_list_left_NoDup : forall l1 l2, Input_list_NoDup l1 l2 -> Input_list_NoDup l1 nil.
intros l1 l2.
generalize l1.
induction l2; intros.
exact H.
apply IHl2.
apply (noDupRed2 a).
exact H.
Defined.

Theorem Input_list_NoDup_NotInA : forall z1 i l b, (Input_list_NoDup ((z1, i) :: l) b -> ~ InA eq_Z_InputIdentifier (z1, i) l).
intros.
intuition.
apply Input_list_left_NoDup in H.
inversion H; subst; contradiction.
Defined.

Lemma CCIn_dist : forall i ide per cas tim x, ~ CCIn i (addCC (CC ide per cas tim) x) -> ~ CCIn i x.
intros.
intuition.
apply H.
unfold CCIn in H0.
unfold CC_SET.Exists in H0.
destruct x.
destruct H0.
destruct H0.
clear H.
unfold CCIn.
unfold addCC.
unfold CC_SET.Exists.
exists x.
split.
apply CC_SET.add_2.
exact H0.
exact H1.
Defined.

Theorem Input_list_NoDup_CCnotIn_aux : forall y : (list (Z * InputIdentifier) * list InputT), forall z1 i l a0, y = (((z1, CommitID i) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, CommitID i) :: l) (a0 :: nil) -> ~ CCIn i a0).
apply (Fix Input_list_NoDupOrder_wf (fun y : (list (Z * InputIdentifier) * list InputT) => forall z1 i l a0, y = (((z1, CommitID i) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, CommitID i) :: l) (a0 :: nil) -> ~ CCIn i a0))).
intros xp Input_list_NoDup_CCnotIn z i l a0 x_def H.
inversion H; try assumption.
intuition.
inversion H4.
destruct H5.
inversion H5.
inversion H5.
exact H10.

assert ({i = ide} + {i <> ide}).
decide equality.
apply (Z.eq_dec).
destruct H6.

intuition.
apply H2.
rewrite e.
apply InA_cons_hd.
reflexivity.
assert (~CCIn i x -> ~ CCIn i (addCC (CC ide per cas tim) x)).
intuition.
apply H6.
clear H6.
unfold addCC.
unfold CCIn.
unfold CCIn in H7.
unfold CC_SET.Exists.
unfold CC_SET.Exists in H7.
destruct x.
destruct H7.
exists x.
destruct x.
destruct i.
destruct i0.
destruct H6.
split.
generalize (CC_SET.add_3).
intros.
apply (H8 cc (CC ide per cas tim) (CC (IdentCC z2) p c t)).
intuition.
apply n.
rewrite H7.
destruct ide.
inversion H9.
reflexivity.
exact H6.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, CommitID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_CC2.
exact H4.
apply (Input_list_NoDup_CCnotIn ((z, CommitID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.

assert (~CCIn i x -> ~ CCIn i (addRC (RC ide per cas) x)).
intuition.
apply H6.
clear H6.
unfold addRC in H7.
destruct x.
unfold CCIn.
unfold CCIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, CommitID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RC2.
exact H4.
apply (Input_list_NoDup_CCnotIn ((z, CommitID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.

assert (~CCIn i x -> ~ CCIn i (addRP (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addRP in H7.
destruct x.
unfold CCIn.
unfold CCIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, CommitID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RP2.
exact H4.
apply (Input_list_NoDup_CCnotIn ((z, CommitID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.

assert (~CCIn i x -> ~ CCIn i (addIC (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addIC in H7.
destruct x.
unfold CCIn.
unfold CCIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, CommitID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_IC2.
exact H4.
apply (Input_list_NoDup_CCnotIn ((z, CommitID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.
Defined.

Theorem Input_list_NoDup_CCnotIn : forall {z1 i l a0}, (Input_list_NoDup ((z1, CommitID i) :: l) (a0 :: nil) -> ~ CCIn i a0).
intros z1 i l a0.
remember ((((z1, CommitID i) :: l), (a0 :: nil))) as y.
apply (Input_list_NoDup_CCnotIn_aux y).
assumption.
Defined.

Theorem Input_list_NoDup_RCnotIn_aux : forall y : (list (Z * InputIdentifier) * list InputT), forall z1 i l a0, y = (((z1, RedeemID i) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, RedeemID i) :: l) (a0 :: nil) -> ~ RCIn i a0).
apply (Fix Input_list_NoDupOrder_wf (fun y : (list (Z * InputIdentifier) * list InputT) => forall z1 i l a0, y = (((z1, RedeemID i) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, RedeemID i) :: l) (a0 :: nil) -> ~ RCIn i a0))).
intros xp Input_list_NoDup_RCnotIn z i l a0 x_def H.
inversion H; try assumption.
intuition.
inversion H4.
destruct H5.
inversion H5.

assert (~RCIn i x -> ~ RCIn i (addCC (CC ide per cas tim) x)).
intuition.
apply H6.
clear H6.
unfold addRC in H7.
destruct x.
unfold RCIn.
unfold RCIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, RedeemID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_CC2.
exact H4.
apply (Input_list_NoDup_RCnotIn ((z, RedeemID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.

intuition.
inversion H5.
contradiction.

assert ({i = ide} + {i <> ide}).
decide equality.
apply (Z.eq_dec).
destruct H6.

intuition.
apply H2.
rewrite e.
apply InA_cons_hd.
reflexivity.
assert (~RCIn i x -> ~ RCIn i (addRC (RC ide per cas) x)).
intuition.
apply H6.
clear H6.
unfold addRC.
unfold RCIn.
unfold RCIn in H7.
unfold RC_SET.Exists.
unfold RC_SET.Exists in H7.
destruct x.
destruct H7.
exists x.
destruct x.
destruct i.
destruct i0.
destruct H6.
split.
generalize (RC_SET.add_3).
intros.
apply (H8 rc (RC ide per cas) (RC (IdentCC z2) p c)).
intuition.
apply n.
rewrite H7.
destruct ide.
inversion H9.
reflexivity.
exact H6.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, RedeemID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RC2.
exact H4.
apply (Input_list_NoDup_RCnotIn ((z, RedeemID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.

assert (~RCIn i x -> ~ RCIn i (addRP (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addRP in H7.
destruct x.
unfold RCIn.
unfold RCIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, RedeemID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RP2.
exact H4.
apply (Input_list_NoDup_RCnotIn ((z, RedeemID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.

assert (~RCIn i x -> ~ RCIn i (addIC (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addIC in H7.
destruct x.
unfold RCIn.
unfold RCIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, RedeemID i) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_IC2.
exact H4.
apply (Input_list_NoDup_RCnotIn ((z, RedeemID i) :: l, x :: nil) H7 z i l x).
reflexivity.
exact H5.
Defined.

Theorem Input_list_NoDup_RCnotIn : forall {z1 i l a0}, (Input_list_NoDup ((z1, RedeemID i) :: l) (a0 :: nil) -> ~ RCIn i a0).
intros z1 i l a0.
remember ((((z1, RedeemID i) :: l), (a0 :: nil))) as y.
apply (Input_list_NoDup_RCnotIn_aux y).
assumption.
Defined.


Theorem Input_list_NoDup_RPnotIn_aux : forall y : (list (Z * InputIdentifier) * list InputT), forall z1 i p l a0, y = (((z1, PaymentID i p) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, PaymentID i p) :: l) (a0 :: nil) -> ~ RPIn (i, p) a0).
apply (Fix Input_list_NoDupOrder_wf (fun y : (list (Z * InputIdentifier) * list InputT) => forall z1 i p l a0, y = (((z1, PaymentID i p) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, PaymentID i p) :: l) (a0 :: nil) -> ~ RPIn (i, p) a0))).
intros xp Input_list_NoDup_RPnotIn z i p l a0 x_def H.
inversion H; try assumption.
intuition.

assert (~RPIn (i, p) x -> ~ RPIn (i, p) (addCC (CC ide per cas tim) x)).
intuition.
apply H6.
clear H6.
unfold addRP in H7.
destruct x.
unfold RPIn.
unfold RPIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, PaymentID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_CC2.
exact H4.
apply (Input_list_NoDup_RPnotIn ((z, PaymentID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.

assert (~RPIn (i, p) x -> ~ RPIn (i, p) (addRC (RC ide per cas) x)).
intuition.
apply H6.
clear H6.
unfold addRC in H7.
destruct x.
unfold RPIn.
unfold RPIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, PaymentID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RC2.
exact H4.
apply (Input_list_NoDup_RPnotIn ((z, PaymentID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.

intuition.
inversion H6.
contradiction.

generalize (PC_OT.eq_dec (ide, per) (i, p)).
intros H6.
destruct H6.

intuition.
apply H2.
apply InA_cons_hd.
unfold eq_Z_InputIdentifier.
unfold PC_OT.eq in e.
destruct ide.
destruct i.
compute in e.
inversion e.
destruct H8.
clear H9.
clear e.
reflexivity.
assert (~RPIn (i, p) x -> ~ RPIn (i, p) (addRP (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addRP in H7.
unfold RPIn.
unfold RPIn in H7.
destruct x.
generalize (@RP_F.add_b Cash rp (ide, per) (i, p) cas).
intros.
rewrite H6 in H7.
clear H6.
assert (RP_F.eqb (ide, per) (i, p) = false).
unfold RP_F.eqb.
destruct (RP_F.eq_dec); intuition.
rewrite H6 in H7.
simpl in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, PaymentID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RP2.
exact H4.
apply (Input_list_NoDup_RPnotIn ((z, PaymentID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.


assert (~RPIn (i, p) x -> ~ RPIn (i, p) (addIC (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addIC in H7.
destruct x.
unfold RPIn.
unfold RPIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, PaymentID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_IC2.
exact H4.
apply (Input_list_NoDup_RPnotIn ((z, PaymentID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.
Defined.

Theorem Input_list_NoDup_RPnotIn : forall {z1 i p l a0}, (Input_list_NoDup ((z1, PaymentID i p) :: l) (a0 :: nil) -> ~ RPIn (i, p) a0).
intros z1 i p l a0.
remember ((((z1, PaymentID i p) :: l), (a0 :: nil))) as y.
apply (Input_list_NoDup_RPnotIn_aux y).
assumption.
Defined.

Theorem Input_list_NoDup_ICnotIn_aux : forall y : (list (Z * InputIdentifier) * list InputT), forall z1 i p l a0, y = (((z1, ChoiceID i p) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, ChoiceID i p) :: l) (a0 :: nil) -> ~ ICIn (i, p) a0).
apply (Fix Input_list_NoDupOrder_wf (fun y : (list (Z * InputIdentifier) * list InputT) => forall z1 i p l a0, y = (((z1, ChoiceID i p) :: l), (a0 :: nil)) -> (Input_list_NoDup ((z1, ChoiceID i p) :: l) (a0 :: nil) -> ~ ICIn (i, p) a0))).
intros xp Input_list_NoDup_ICnotIn z i p l a0 x_def H.
inversion H; try assumption.
intuition.

assert (~ICIn (i, p) x -> ~ ICIn (i, p) (addCC (CC ide per cas tim) x)).
intuition.
apply H6.
clear H6.
unfold addRP in H7.
destruct x.
unfold ICIn.
unfold ICIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, ChoiceID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_CC2.
exact H4.
apply (Input_list_NoDup_ICnotIn ((z, ChoiceID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.

assert (~ICIn (i, p) x -> ~ ICIn (i, p) (addRC (RC ide per cas) x)).
intuition.
apply H6.
clear H6.
unfold addRC in H7.
destruct x.
unfold ICIn.
unfold ICIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, ChoiceID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RC2.
exact H4.
apply (Input_list_NoDup_ICnotIn ((z, ChoiceID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.

assert (~ICIn (i, p) x -> ~ ICIn (i, p) (addRP (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addIC in H7.
destruct x.
unfold ICIn.
unfold ICIn in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, ChoiceID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_RP2.
exact H4.
apply (Input_list_NoDup_ICnotIn ((z, ChoiceID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.


intuition.
inversion H6.
contradiction.

generalize (IC_OT.eq_dec (ide, per) (i, p)).
intros H6.
destruct H6.

intuition.
apply H2.
apply InA_cons_hd.
unfold eq_Z_InputIdentifier.
unfold PC_OT.eq in e.
destruct ide.
destruct i.
compute in e.
inversion e.
destruct H8.
clear H9.
clear e.
reflexivity.
assert (~ICIn (i, p) x -> ~ ICIn (i, p) (addIC (ide, per) cas x)).
intuition.
apply H6.
clear H6.
unfold addIC in H7.
unfold ICIn.
unfold ICIn in H7.
destruct x.
generalize (@IC_F.add_b ConcreteChoice ic (ide, per) (i, p) cas).
intros.
rewrite H6 in H7.
clear H6.
assert (IC_F.eqb (ide, per) (i, p) = false).
unfold IC_F.eqb.
destruct (IC_F.eq_dec); intuition.
rewrite H6 in H7.
simpl in H7.
exact H7.
apply H6.
assert (Input_list_NoDupOrder ((z, ChoiceID i p) :: l, x :: nil) xp).
rewrite x_def.
rewrite <- H0.
apply Input_list_NoDup_step_IC2.
exact H4.
apply (Input_list_NoDup_ICnotIn ((z, ChoiceID i p) :: l, x :: nil) H7 z i p l x).
reflexivity.
exact H5.
Defined.

Theorem Input_list_NoDup_ICnotIn : forall {z1 i p l a0}, (Input_list_NoDup ((z1, ChoiceID i p) :: l) (a0 :: nil) -> ~ ICIn (i, p) a0).
intros z1 i p l a0.
remember ((((z1, ChoiceID i p) :: l), (a0 :: nil))) as y.
apply (Input_list_NoDup_ICnotIn_aux y).
assumption.
Defined.

Theorem Input_list_addInput : forall z1 i i0 l a0 s0 ii0, Input_list_NoDup ((z1, i) :: l) (a0 :: nil) ->
                                                                                Input_list_NoDup l (addInput z1 i i0 s0 ii0 a0 :: nil).
intros.
destruct i.
destruct i0; try (simpl; apply (noDupRed (z1, CommitID i)); exact H).
simpl.
destruct sol.SOL_MAP.find; try (simpl; apply (noDupRed (z1, CommitID i)); exact H).
apply (@Input_list_NoDup_addCC2 _ z1).
apply (Input_list_NoDup_NotInA _ _ _ (a0 :: nil)).
exact H.
apply NCCInL_cons.
apply (@Input_list_NoDup_CCnotIn z1 i l a0).
exact H.
apply NCCInL_nil.
apply (noDupRed (z1, CommitID i)).
exact H.
destruct i0; try (simpl; apply (noDupRed (z1, RedeemID i)); exact H).
simpl.
destruct sol.SOL_MAP.find; try (simpl; apply (noDupRed (z1, RedeemID i)); exact H).
apply (@Input_list_NoDup_addRC2 _ z1).
apply (Input_list_NoDup_NotInA _ _ _ (a0 :: nil)).
exact H.
apply NRCInL_cons.
apply (@Input_list_NoDup_RCnotIn z1 i l a0).
exact H.
apply NRCInL_nil.
apply (noDupRed (z1, RedeemID i)).
exact H.
destruct i0; try (simpl; apply (noDupRed (z1, PaymentID i p)); exact H).
simpl.
destruct (@sol.SOL_MAP.find); try (simpl; apply (noDupRed (z1, PaymentID i p)); exact H).
apply (@Input_list_NoDup_addRP2 _ z1).
apply (Input_list_NoDup_NotInA _ _ _ (a0 :: nil)).
exact H.
apply NRPInL_cons.
apply (@Input_list_NoDup_RPnotIn z1 i p l a0).
exact H.
apply NRPInL_nil.
apply (noDupRed (z1, PaymentID i p)).
exact H.
destruct i0; try (simpl; apply (noDupRed (z1, ChoiceID i p)); exact H).
simpl.
destruct (@sol.SOL_MAP.find); try (simpl; apply (noDupRed (z1, ChoiceID i p)); exact H).
apply (@Input_list_NoDup_addIC2 _ z1).
apply (Input_list_NoDup_NotInA _ _ _ (a0 :: nil)).
exact H.
apply NICInL_cons.
apply (@Input_list_NoDup_ICnotIn z1 i p l a0).
exact H.
apply NICInL_nil.
apply (noDupRed (z1, ChoiceID i p)).
exact H.
Defined.

Theorem instantiate_canonical : forall s : sol.SOL_MAP_TYPE, forall ii : II_MAP_TYPE, {t | CanonicalInput (instantiate s ii) t}.
intros.
unfold instantiate.
destruct (sol.SOL_MAP.find CurrentBlock s).
assert (forall l r a n z s ii, CanonicalInput r a -> Input_list_NoDup l (a::nil) -> {b : InputT | CanonicalInput (r ++ (instantiateList n z l s ii a)) b /\ Input_list_NoDup l (a::nil)}).
intro l.
induction l; intros.
(* base step *)
simpl.
exists a.
split.
apply clone_canonical.
exact H.
exact H0.
(* inductive step *)
simpl.
destruct a.
destruct (Z_ge_lt_dec z1 n).
destruct (Z_ge_lt_dec z1 z0).
destruct (IHl r a0 n z0 s0 ii0).
apply H.
apply (noDupRed (z1, i)).
exact H0.
exists x.
destruct a.
split.
exact H1.
exact H0.
destruct (II_MAP.find i ii0).
destruct (IHl (r ++ repeat a0 (Z.abs_nat (z1 -  n))) (addInput z1 i i0 s0 ii0 a0) z1 z0 s0 ii0).
destruct i.
simpl.
destruct i0; (try (apply clone_canonical; exact H)).
destruct sol.SOL_MAP.find; [try apply AddCC; try apply AddRC; try apply AddRP; try apply AddIC;
                                                                           [apply clone_canonical; exact H | apply (Input_list_NoDup_CCnotIn H0) ] | apply clone_canonical; exact H].
simpl.
destruct i0; (try (apply clone_canonical; exact H)).
destruct sol.SOL_MAP.find; [try apply AddCC; try apply AddRC; try apply AddRP; try apply AddIC;
                                                                           [apply clone_canonical; exact H | apply (Input_list_NoDup_RCnotIn H0) ] | apply clone_canonical; exact H].
simpl.
destruct i0; (try (apply clone_canonical; exact H)).
destruct sol.SOL_MAP.find; [try apply AddCC; try apply AddRC; try apply AddRP; try apply AddIC;
                                                                           [apply clone_canonical; exact H | apply (Input_list_NoDup_RPnotIn H0) ] | apply clone_canonical; exact H].
simpl.
destruct i0; (try (apply clone_canonical; exact H)).
destruct sol.SOL_MAP.find; [try apply AddCC; try apply AddRC; try apply AddRP; try apply AddIC;
                                                                           [apply clone_canonical; exact H | apply (Input_list_NoDup_ICnotIn H0) ] | apply clone_canonical; exact H].
apply Input_list_addInput.
exact H0.
exists x.
rewrite (app_assoc).
destruct a.
split.
exact H1.
exact H0.
destruct (IHl r a0 n z0 s0 ii0).
exact H.
apply (noDupRed (z1, i)).
exact H0.
exists x.
destruct a.
split.
exact H1.
exact H0.
destruct (IHl r a0 n z0 s0 ii0).
exact H.
apply (noDupRed (z1, i)).
exact H0.
exists x.
destruct a.
split.
exact H1.
exact H0.
(* last 2 goals *)
destruct (X (extractIdentifiers s) nil emptyInput 0%Z z s ii).
apply EmptyCIL.
apply (Input_list_NoDup_cons_empty).
apply NoDupA_Input_list_NoDup.
apply extractIdentifiers_NoDupA.
exists x.
destruct a.
exact H.
exists emptyInput.
apply EmptyCIL.
Defined.

