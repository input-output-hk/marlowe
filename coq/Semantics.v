Require Import ZArith_base.
Require Import FSets.FSetAVL.
Require Import Coq.Structures.Orders.
Require Import OTFromList.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.FSets.FMapList.

Open Scope Int_scope.

Definition Person := Z.

Definition BlockNumber := Z.

Record OST := OS { blockNumber : BlockNumber }.
Definition emptyOS : OST := {| blockNumber := 0%Z |}.

Definition Cash := Z.
Definition ConcreteChoice := Z.

Definition Timeout := Z.

Inductive IdentCCT := IdentCC : Z -> IdentCCT.
Inductive IdentChoiceT := IdentChoice : Z -> IdentChoiceT.
Inductive IdentPayT := IdentPay : Z -> IdentPayT.

Inductive CCT := CC : IdentCCT -> Person -> Cash -> Timeout -> CCT.

Inductive RCT := RC : IdentCCT -> Person -> Cash -> RCT.


Require Import Coq.FSets.FSetProperties.
(* CC Set def *)
Module CC_LT <: ListType.
  Definition s := CCT.
  Definition st (cct : CCT) :=
    match cct with
       | CC (IdentCC iz) p c t0 => iz :: p :: c :: t0 :: nil
    end.
End CC_LT.
Module CC_OT := ListToOT(CC_LT).
Module CC_SET := FSetAVL.Make (CC_OT).
Definition emptyCCSet := CC_SET.empty.
Module CC_P := WProperties_fun CC_OT CC_SET.
Module CC_F := CC_P.FM.

(* RC Set def *)
Module RC_LT <: ListType.
  Definition s := RCT.
  Definition st (rct : RCT) :=
    match rct with
       | RC (IdentCC iz) p c => iz :: p :: c :: nil
    end.
End RC_LT.
Module RC_OT := ListToOT(RC_LT).
Module RC_SET := FSetAVL.Make (RC_OT).
Definition emptyRCSet := RC_SET.empty.
Module RC_P := WProperties_fun RC_OT RC_SET.
Module RC_F := RC_P.FM.

Require Import Coq.FSets.FMapFacts.
(* Map (IdentPay, Person) Cash *)
Module PC_LT <: ListType.
  Definition s := (IdentPayT * Person) : Type.
  Definition st (x : s) := let (i, p) := x in
       match i with
       | IdentPay iz => iz :: p :: nil
       end.
End PC_LT.
Module PC_OT := ListToOT(PC_LT).
Module RP_MAP := FMapAVL.Make(PC_OT).
Definition emptyRPMap := RP_MAP.empty Cash.
Definition RP_MAP_TYPE := RP_MAP.t Cash.
Module RP_P := WProperties_fun PC_OT RP_MAP.
Module RP_F := RP_P.F.


(* Map (IdentPay, Person) ConcreteChoice *)
Module IC_LT <: ListType.
  Definition s := (IdentChoiceT * Person) : Type.
  Definition st (x : s) := let (i, p) := x in
       match i with
       | IdentChoice iz => iz :: p :: nil
       end.
End IC_LT.
Module IC_OT := ListToOT(IC_LT).
Module IC_MAP := FMapAVL.Make(IC_OT).
Definition emptyICMap := IC_MAP.empty ConcreteChoice.
Definition IC_MAP_TYPE := IC_MAP.t ConcreteChoice.
Module IC_P := WProperties_fun IC_OT IC_MAP.
Module IC_F := IC_P.F.

Record InputT := Input {
                               cc : CC_SET.t;
                               rc : RC_SET.t;
                               rp : RP_MAP.t Cash;
                               ic : IC_MAP.t ConcreteChoice
                            }.

Definition emptyInput := Input emptyCCSet emptyRCSet emptyRPMap emptyICMap.

Inductive Action := SuccessfulPay : IdentPayT -> Person -> Person -> Cash -> Action
                              | ExpiredPay : IdentPayT -> Person -> Person -> Cash -> Action
                              | FailedPay : IdentPayT -> Person -> Person -> Cash -> Action
                              | SuccessfulCommit : IdentCCT -> Person -> Cash -> Timeout -> Action
                              | CommitRedeemed : IdentCCT -> Person -> Cash -> Action
                              | ExpiredCommitRedeemed : IdentCCT -> Person -> Cash -> Action
                              | DuplicateRedeem : IdentCCT -> Person -> Action
                              | ChoiceMade : IdentChoiceT -> Person -> ConcreteChoice -> Action.

Definition AS := list Action.

Inductive CCRedeemStatus := NotRedeemed : Cash -> Timeout -> CCRedeemStatus
                                              | ExpiredAndRedeemed : CCRedeemStatus
                                              | ManuallyRedeemed : CCRedeemStatus.

Definition CCStatus := (Person * CCRedeemStatus) : Type.

(* Map IdentCC CCStatus *)
Module SC_LT <: ListType.
  Definition s := IdentCCT : Type.
  Definition st (x : s) :=
     match x with
      | IdentCC iz => iz :: nil
     end.
End SC_LT.
Module SC_OT := ListToOT(SC_LT).
Module SC_MAP := FMapAVL.Make(SC_OT).
Definition emptySCMap := SC_MAP.empty CCStatus.
Definition SC_MAP_TYPE := SC_MAP.t CCStatus.
Module SC_MAP_P := WProperties_fun SC_OT SC_MAP.
Module SC_MAP_F := SC_MAP_P.F.

(* Map (IdentChoice, Person) ConcreteChoice *)
Module SCH_LT <: ListType.
  Definition s := (IdentChoiceT * Person) : Type.
  Definition st (x : s) := let (i, p) := x in
       match i with
       | IdentChoice iz => iz :: p :: nil
       end.
End SCH_LT.
Module SCH_OT := ListToOT(SCH_LT).
Module SCH_MAP := FMapAVL.Make(SCH_OT).
Definition emptySCHMap := SCH_MAP.empty ConcreteChoice.
Definition SCH_MAP_TYPE := SCH_MAP.t ConcreteChoice.
Module SCH_MAP_P := WProperties_fun SCH_OT SCH_MAP.
Module SCH_MAP_F := SCH_MAP_P.F.

Record StateT := State {
                                   sc : SC_MAP_TYPE;
                                   sch : SCH_MAP_TYPE
                             }.

Definition emptyState := State emptySCMap emptySCHMap.

Inductive Money := AvailableMoney : IdentCCT -> Money
                               | AddMoney : Money -> Money -> Money
                               | ConstMoney : Cash -> Money
                               | MoneyFromChoice : IdentChoiceT -> Person -> Money -> Money.

Fixpoint evalMoney (sta : StateT) (mon : Money) : Cash :=
        match mon with
         | AvailableMoney i =>
             match SC_MAP.find i (sc sta) with
             | Some (_, NotRedeemed c _) => c
             | _ => 0%Z
             end
         | AddMoney mon1 mon2 => (evalMoney sta mon1 + evalMoney sta mon2)%Z
         | ConstMoney c => c
         | MoneyFromChoice i p mon0 =>
             match SCH_MAP.find (i, p) (sch sta) with
             | Some c => c
             | None => evalMoney sta mon0
             end
         end.

Inductive Observation := BelowTimeout : Timeout -> Observation
                                       | AndObs : Observation -> Observation -> Observation
                                       | OrObs : Observation -> Observation -> Observation
                                       | NotObs : Observation -> Observation
                                       | PersonChoseThis : IdentChoiceT -> Person -> ConcreteChoice -> Observation
                                       | PersonChoseSomething : IdentChoiceT -> Person -> Observation
                                       | ValueGE : Money -> Money -> Observation
                                       | TrueObs : Observation
                                       | FalseObs : Observation.

Definition expired (e : Timeout) (ee : Timeout) : bool := (ee <=? e)%Z.

Fixpoint interpretObs (sta : StateT) (obs : Observation) (os : OST) : bool :=
         match obs with
         | BelowTimeout n => negb (expired (blockNumber os) n)
         | AndObs obs1 obs2 =>
             interpretObs sta obs1 os && interpretObs sta obs2 os
         | OrObs obs1 obs2 =>
             interpretObs sta obs1 os || interpretObs sta obs2 os
         | NotObs obs0 => negb (interpretObs sta obs0 os)
         | PersonChoseThis choice_id person reference_choice =>
             match SCH_MAP.find (choice_id, person) (sch sta) with
             | Some actual_choice =>
                 (actual_choice =? reference_choice)%Z
             | None => false
             end
         | PersonChoseSomething choice_id person =>
             SCH_MAP.mem (choice_id, person) (sch sta)
         | ValueGE a b => (evalMoney sta a >=? evalMoney sta b)%Z
         | TrueObs => true
         | FalseObs => false
         end.

Inductive Contract := Null
                                 | CommitCash : IdentCCT -> Person -> Money -> Timeout -> Timeout -> Contract -> Contract -> Contract
                                 | RedeemCC : IdentCCT -> Contract -> Contract
                                 | Pay : IdentPayT -> Person -> Person -> Money -> Timeout -> Contract -> Contract
                                 | Both : Contract -> Contract -> Contract
                                 | Choice : Observation -> Contract -> Contract -> Contract
                                 | When : Observation -> Timeout -> Contract -> Contract -> Contract.


Module CommitLE <: TotalLeBool'.
Definition t : Type := (IdentCCT * CCStatus).
Fixpoint leb (a1 : IdentCCT * CCStatus) (b2 : IdentCCT * CCStatus) :=
    let (ia1, ba1) := a1 in
         let (ib2, bb2) := b2 in
         match ia1 with
         | IdentCC iza1 =>
             match ib2 with
             | IdentCC izb2 =>
                 let (_, ca1) := ba1 in
                 let (_, cb2) := bb2 in
                 match ca1 with
                 | NotRedeemed _ ea1 =>
                     match cb2 with
                     | NotRedeemed _ eb2 =>
                         if (ea1 <? eb2)%Z
                         then true
                         else if (ea1 >? eb2)%Z then false else (iza1 <=? izb2)%Z
                     | ManuallyRedeemed => true
                     | ExpiredAndRedeemed => true
                     end
                 | ManuallyRedeemed =>
                     match cb2 with
                     | NotRedeemed _ _ => false
                     | ManuallyRedeemed => true
                     | ExpiredAndRedeemed => true
                     end
                 | ExpiredAndRedeemed =>
                     match cb2 with
                     | NotRedeemed _ _ => false
                     | ManuallyRedeemed => false
                     | ExpiredAndRedeemed => true
                     end
                 end
             end
         end.
Definition leb_total : forall a1 b2, leb a1 b2 = true \/ leb b2 a1 = true.
intros.
unfold leb.
destruct a1 as [ia1 ba1].
destruct b2 as [ib2 bb2].
destruct ia1 as [iza1].
destruct ib2 as [izb2].
destruct ba1 as [pa1 ca1].
destruct bb2 as [pb2 cb2].
destruct ca1 as [ca1 ea1 | | ].
destruct cb2 as [cb2 eb2 | | ].
assert ({ea1 <? eb2 = true} + {ea1 <? eb2 = false})%Z as firstCompareLT.
destruct (ea1 <? eb2)%Z.
left.
reflexivity.
right.
reflexivity.
case_eq firstCompareLT.
intros.
clear H firstCompareLT.
rewrite e.
left.
reflexivity.
intros.
rewrite e.
clear H.
rewrite <- Z.gtb_ltb in e.
rewrite e.
case_eq ((ea1 >? eb2)%Z); intros.
rewrite Z.gtb_ltb in H.
rewrite H.
right.
reflexivity.
rewrite Z.gtb_ltb in H.
rewrite H.
assert ({(iza1 <=? izb2)%Z = true} + {(iza1 <=? izb2)%Z = false}).
destruct ((iza1 <=? izb2)%Z).
left.
reflexivity.
right.
reflexivity.
destruct H0.
rewrite e0.
left.
reflexivity.
right.
clear firstCompareLT.
apply Zle_imp_le_bool.
apply Z.leb_nle in e0.
intuition.
left.
reflexivity.
left.
reflexivity.
destruct cb2; right; reflexivity.
destruct cb2; [right | left | left]; reflexivity.
Defined.
End CommitLE.

Module CommitSort := Sort(CommitLE). 

Definition sortByExpirationDate : list (IdentCCT * CCStatus) -> list (IdentCCT * CCStatus) := CommitSort.sort.

Fixpoint discountFromPairList (v : Cash) (l : list (IdentCCT * CCStatus)) : option (list (IdentCCT * CCStatus)) :=
        match l with
         | (ident, (p, NotRedeemed ve e)) :: t =>
             if Z_le_gt_dec v ve
             then Some ((ident, (p, NotRedeemed (ve - v)%Z e)) :: nil)
             else match discountFromPairList (v - ve)%Z t with
                     | Some dt => Some ((ident, (p, NotRedeemed 0%Z e)) :: dt)
                     | None => None
                    end
         | (ident, (p, ManuallyRedeemed)) :: t => Some t
         | (ident, (p, ExpiredAndRedeemed)) :: t => Some t
         | nil => if Z.eq_dec v 0 then Some nil else None
        end.

Definition discountFromValid (f : CCStatus -> bool) (v : Cash) (m : SC_MAP_TYPE) : option SC_MAP_TYPE :=
    match
         discountFromPairList v
           (sortByExpirationDate
              (filter (fun k_va : IdentCCT * CCStatus => let (_, va) := k_va in f va)
                 (SC_MAP.elements m)))
    with
       | Some changes_to_map =>
           Some (fold_left (fun (mi : SC_MAP_TYPE) (el : IdentCCT * CCStatus) =>
                                    let (k, va) := el in SC_MAP.add k va mi) changes_to_map m)
       | None => None
    end.

Definition isRedeemable (p : Person) (e : Timeout) (ccs : CCStatus) : bool :=
       let (ep, css) := ccs in
       match css with
         | NotRedeemed _ ee => (ep =? p)%Z && negb (expired e ee)
         | ManuallyRedeemed => false
         | ExpiredAndRedeemed => false
       end.

Definition updateMap (mx : SC_MAP_TYPE) (p : Person) (e : Timeout) (v : Cash) : option SC_MAP_TYPE :=
  discountFromValid (isRedeemable p e) v mx.

Definition stateUpdate (st : StateT) (from : Person) (to : Person) (bn : Timeout) (val : Cash) : option StateT :=
      match st with
       | {| sc := sc; sch := sch |} =>
           match updateMap sc from bn val with
           | Some newccs => Some {| sc := newccs; sch := sch |}
           | None => None
           end
      end.

Definition nulldec : (forall con : Contract, {con = Null} + {con <> Null}).
destruct con; try (left; reflexivity); right; intuition; inversion H.
Defined.

Fixpoint step (inp : InputT) (st : StateT) (c : Contract) (os : OST) : StateT * Contract * AS :=
    let bn := blockNumber os in
    match c with
         | Null => (st, Null, nil)
         | CommitCash ident person val start_timeout end_timeout con1 con2 =>
              let cexs := expired bn end_timeout in
              let cexe := expired bn start_timeout in
              let ccs := sc st in
              let cval := evalMoney st val in
              let cns := (person, if cexs || cexe
                                           then ManuallyRedeemed
                                           else NotRedeemed cval end_timeout) in
              let ust := SC_MAP.add ident cns ccs in
              let nst := {| sc := ust;
                                 sch := sch st |} in
              if cexe || cexs
              then (nst, con2, nil)
              else if CC_SET.mem (CC ident person cval end_timeout) (cc inp)
                     then (nst, con1, SuccessfulCommit ident person (evalMoney st val) end_timeout :: nil)
                     else (st, CommitCash ident person val start_timeout end_timeout con1 con2, nil)
         | RedeemCC ident con =>
             match SC_MAP.find ident (sc st) with
               | Some (person, NotRedeemed val ee) =>
                   if (expired bn ee) then (st, con, nil)
                   else (if RC_SET.mem (RC ident person val) (rc inp)
                           then ({| sc := SC_MAP.add ident (person, ManuallyRedeemed) (sc st);
                                       sch := sch st |}, con, CommitRedeemed ident person val :: nil)
                           else (st, RedeemCC ident con, nil))
               | Some (person, ManuallyRedeemed) => (st, con, DuplicateRedeem ident person :: nil)
               | Some (person, ExpiredAndRedeemed) => (st, con, nil)
               | None => (st, RedeemCC ident con, nil)
            end
         | Pay idpay from to val expi con =>
             let cval := evalMoney st val in
             if (expired (blockNumber os) expi)
             then (st, con, (ExpiredPay idpay from to cval :: nil))
             else (if (match RP_MAP.find (idpay, to) (rp inp) with
                          | Some claimed_val => (claimed_val =? cval)%Z
                          | None => false
                         end)
                     then (if (cval >=? 0)%Z
                              then (match stateUpdate st from to bn cval with
                                        | Some newstate => (newstate, con, SuccessfulPay idpay from to cval :: nil)
                                        | None => (st, con, FailedPay idpay from to cval :: nil)
                                       end)
                              else (st, con, FailedPay idpay from to cval :: nil))
                     else (st, Pay idpay from to val expi con, nil))
         | Both con1 con2 =>
             let (res1, ac1) := step inp st con1 os in
             let (st1, ncon1) := res1 in
             let (res2, ac2) := step inp st1 con2 os in
             let (st2, ncon2) := res2 in
             (st2, if nulldec ncon1
                     then ncon2
                     else if nulldec ncon2
                            then ncon1
                            else Both ncon1 ncon2,
             ac1 ++ ac2)
         | Choice obs conT conF =>
             if interpretObs st obs os
             then (st, conT, nil)
             else (st, conF, nil)
         | When obs expi con con2 =>
             if expired (blockNumber os) expi
             then (st, con2, nil)
             else if interpretObs st obs os
                    then (st, con, nil)
                    else (st, When obs expi con con2, nil)
    end.

Definition sc_kv_eqb (a: (SC_MAP.key * CCStatus)) (b: (SC_MAP.key * CCStatus)) : bool :=
       let (k1, c1) := a in
       let (k2, c2) := b in
       (if SC_OT.eq_dec k1 k2 then true else false) &&
       (let (p, c) := c1 in
        let (p0, c0) := c2 in
        match c with
        | NotRedeemed c3 t =>
            match c0 with
            | NotRedeemed c4 t0 =>
                (p =? p0)%Z && (c3 =? c4)%Z && (t =? t0)%Z
            | ManuallyRedeemed => false
            | ExpiredAndRedeemed => false
            end
        | ManuallyRedeemed =>
            match c0 with
            | NotRedeemed _ _ => false
            | ManuallyRedeemed => (p =? p0)%Z
            | ExpiredAndRedeemed => false
            end
        | ExpiredAndRedeemed =>
            match c0 with
            | NotRedeemed _ _ => false
            | ManuallyRedeemed => false
            | ExpiredAndRedeemed => (p =? p0)%Z
            end
        end).

Definition sch_kv_eqb (a: (SCH_MAP.key * ConcreteChoice)) (b: (SCH_MAP.key * ConcreteChoice)) : bool :=
       let (k, c) := a in
       let (k0, c0) := b in
       (if SCH_OT.eq_dec k k0 then true else false) && (c =? c0)%Z.

Fixpoint list_eqb {a : Type} {b : Type} (f : (a -> b -> bool)) (x : list a) (y : list b) : bool :=
          match x with
          | nil =>
              match y with
              | nil => true
              | _ :: _ => false
              end
          | a0 :: x0 =>
              match y with
              | nil => false
              | b0 :: y0 => f a0 b0 && list_eqb f x0 y0
              end
          end.

Definition StateT_eqb (a : StateT) (b : StateT) : bool :=
    list_eqb sc_kv_eqb (SC_MAP.elements (sc a)) (SC_MAP.elements (sc b))
                  &&
    list_eqb sch_kv_eqb (SCH_MAP.elements (sch a)) (SCH_MAP.elements (sch b)).

Fixpoint Money_eqb (a : Money) (b : Money) : bool :=
     match a with 
         | AvailableMoney i => match b with
                                             | AvailableMoney i0 =>
                                                      match i with | IdentCC z => match i0 with | IdentCC z0 =>
                                                      (z =? z0)%Z
                                                      end end
                                             | _ => false
                                           end
         | AddMoney a1 a2 => match b with
                                            | AddMoney b1 b2 => Money_eqb a1 b1 && Money_eqb a2 b2
                                            | _ => false
                                          end
         | ConstMoney c => match b with
                                         | ConstMoney c0 => (c =? c0)%Z
                                         | _ => false
                                       end
         | MoneyFromChoice i p a0 => match b with
                                                        | MoneyFromChoice i0 p0 b0 =>
                                                              match i with | IdentChoice z =>
                                                              match i0 with | IdentChoice z0 =>
                                                              (z =? z0)%Z && (p =? p0)%Z && Money_eqb a0 b0
                                                              end end
                                                        | _ => false
                                                        end
     end.

Fixpoint Obs_eqb (a : Observation) (b : Observation) : bool :=
         match a with
         | BelowTimeout t =>
             match b with
             | BelowTimeout t0 => (t =? t0)%Z
             | _ => false
             end
         | AndObs a1 a2 =>
             match b with
             | AndObs b1 b2 => Obs_eqb a1 b1 && Obs_eqb a2 b2
             | _ => false
             end
         | OrObs a1 a2 =>
             match b with
             | OrObs b1 b2 => Obs_eqb a1 b1 && Obs_eqb a2 b2
             | _ => false
             end
         | NotObs a0 => match b with
                        | NotObs b0 => Obs_eqb a0 b0
                        | _ => false
                        end
         | PersonChoseThis i p c =>
             match b with
             | PersonChoseThis i0 p0 c0 =>
                 match i with
                 | IdentChoice z =>
                     match i0 with
                     | IdentChoice z0 =>
                         list_eqb Z.eqb (z :: p :: c :: nil) (z0 :: p0 :: c0 :: nil)
                     end
                 end
             | _ => false
             end
         | PersonChoseSomething i c =>
             match b with
             | PersonChoseSomething i0 c0 =>
                 match i with
                 | IdentChoice z =>
                     match i0 with
                     | IdentChoice z0 => (z =? z0)%Z && (c =? c0)%Z
                     end
                 end
             | _ => false
             end
         | ValueGE m1 m2 =>
             match b with
             | ValueGE n1 n2 => Money_eqb m1 n1 && Money_eqb m2 n2
             | _ => false
             end
         | TrueObs => match b with
                      | TrueObs => true
                      | _ => false
                      end
         | FalseObs => match b with
                       | FalseObs => true
                       | _ => false
                       end
         end.

Fixpoint Contract_eqb (a : Contract) (b : Contract) : bool :=
         match a with
         | Null => match b with
                   | Null => true
                   | _ => false
                   end
         | CommitCash i p m t t0 a1 a2 =>
             match b with
             | CommitCash i0 p0 m0 t1 t2 b1 b2 =>
                 list_eqb Z.eqb (match i with | IdentCC z => z :: p :: t :: t0 :: nil end)
                                        (match i0 with | IdentCC z => z :: p0 :: t1 :: t2 :: nil end)
                      && (Money_eqb m m0 && Contract_eqb a1 b1 && Contract_eqb a2 b2)
             | _ => false
             end
         | RedeemCC i a0 =>
             match b with
             | RedeemCC i0 b0 =>
                 (match i with | IdentCC z => (match i0 with | IdentCC z0 => (z =? z0)%Z end) end)
                       && Contract_eqb a0 b0
             | _ => false
             end
         | Pay i p p0 m t a0 =>
             match b with
             | Pay i0 p1 p2 m0 t0 b0 =>
                 Money_eqb m m0 &&
                 match i with
                 | IdentPay z =>
                     match i0 with
                     | IdentPay z0 => list_eqb Z.eqb (z :: p :: p0 :: t :: nil) (z0 :: p1 :: p2 :: t0 :: nil)
                     end
                 end && Contract_eqb a0 b0
             | _ => false
             end
         | Both a1 a2 => match b with
                         | Both b1 b2 => Contract_eqb a1 b1 && Contract_eqb a2 b2
                         | _ => false
                         end
         | Choice o a1 a2 =>
             match b with
             | Choice o0 b1 b2 => Obs_eqb o o0 && Contract_eqb a1 b1 && Contract_eqb a2 b2
             | _ => false
             end
         | When o t a1 a2 =>
             match b with
             | When o0 t0 b1 b2 => (t =? t0)%Z && Obs_eqb o o0 && (Contract_eqb a1 b1 && Contract_eqb a2 b2)
             | _ => false
             end
         end.

Fixpoint Contract_size (a : Contract) : nat :=
    match a with
      | Null => 1
      | RedeemCC _ a0 | Pay _ _ _ _ _ a0 => 1 + Contract_size a0
      | CommitCash _ _ _ _ _ a1 a2 | Both a1 a2 |
        Choice _ a1 a2 | When _ _ a1 a2 => 1 + Contract_size a1 + Contract_size a2
    end.

Definition ContractOrder (c1 c2 : Contract) := Contract_size c1 < Contract_size c2.

  Lemma contractOrder_wf' : forall siz, forall con, Contract_size con <= siz -> Acc ContractOrder con.
    destruct siz.
    intros.
    destruct con; inversion H.
    unfold ContractOrder.
    induction siz.
    intros.
    assert ((forall y : Contract, (fun c1 c2 : Contract => Contract_size c1 < Contract_size c2) y con -> Acc (fun c1 c2 : Contract => Contract_size c1 < Contract_size c2) y) -> Acc (fun c1 c2 : Contract => Contract_size c1 < Contract_size c2) con).
    intros.
    apply (Acc_intro).
    apply H0.
    apply H0.
    intros.
    assert (Contract_size con = 1).
    intuition.
    rewrite H2 in H1.
    destruct y; simpl in H1; inversion H1; inversion H4.
    intros.
    destruct con; apply Acc_intro; intros; apply IHsiz; intuition; simpl in H.
  Defined.

  Theorem contractOrder_wf : well_founded ContractOrder.
    red; intro; eapply contractOrder_wf'; eauto.
  Defined.

Definition StepVal_size (sv1 : (StateT * Contract * AS)) : nat := let (p, _) := sv1 in let (_, c) := p in Contract_size c.

Definition StepValOrder (sv1 sv2 : (StateT * Contract * AS)) : Prop := StepVal_size sv1 < StepVal_size sv2.

Lemma stepValOrder_wf' : forall siz, forall sv, StepVal_size sv <= siz -> Acc StepValOrder sv.
    destruct siz.
    intros.
    destruct sv; destruct p; destruct c; simpl in H; inversion H.
    unfold StepValOrder.
    induction siz.
    intros.
    assert ((forall y :  StateT * Contract * AS, (fun c1 c2 :  StateT * Contract * AS => StepVal_size c1 < StepVal_size c2) y sv -> Acc (fun c1 c2 : StateT * Contract * AS => StepVal_size c1 < StepVal_size c2) y) -> Acc (fun c1 c2 : StateT * Contract * AS => StepVal_size c1 < StepVal_size c2) sv).
    intros.
    apply (Acc_intro).
    apply H0.
    apply H0.
    intros.
    assert (StepVal_size sv = 1).
    intuition.
    rewrite H2 in H1.
    destruct y; destruct p; destruct c; simpl in H1; inversion H1; inversion H4.
    intros.
    destruct sv.
    destruct p.
    destruct c; apply Acc_intro; intros; apply IHsiz; intuition; simpl in H.
Defined.


  Theorem stepValOrder_wf : well_founded StepValOrder.
    red; intro; eapply stepValOrder_wf'; eauto.
  Defined.

Theorem SC_KV_EQB_refl : forall a : SC_MAP.key * CCStatus, sc_kv_eqb a a = true.
intros.
destruct a.
unfold sc_kv_eqb.
destruct c.
destruct c.
rewrite (Z.eqb_refl).
rewrite (Z.eqb_refl).
rewrite (Z.eqb_refl).
destruct SC_OT.eq_dec.
simpl.
reflexivity.
absurd (SC_OT.eq k k).
exact n.
apply (SC_OT.eq_refl).
rewrite (Z.eqb_refl).
destruct SC_OT.eq_dec.
simpl.
reflexivity.
absurd (SC_OT.eq k k).
exact n.
apply (SC_OT.eq_refl).
rewrite (Z.eqb_refl).
destruct SC_OT.eq_dec.
simpl.
reflexivity.
absurd (SC_OT.eq k k).
exact n.
apply (SC_OT.eq_refl).
Defined.

Lemma eqb_to_eq : forall a b : Z, Z.eqb a b = true -> a = b.
intros.
assert (a = b <-> Z.eqb a b = true).
apply (Bool.reflect_iff).
apply (Z.eqb_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Theorem SC_KV_EQB_spec : forall a b : SC_MAP.key * CCStatus, Bool.reflect (a = b) (sc_kv_eqb a b).
intros.
apply Bool.iff_reflect.
split.
intros.
rewrite H.
rewrite SC_KV_EQB_refl.
reflexivity.
intros.
destruct a.
destruct b.
simpl in H.
destruct (SC_OT.eq_dec k k0).
destruct c.
destruct c.
destruct c0.
destruct c0.
simpl in H.
assert ((p =? p0)%Z = true /\ (c =? c0)%Z && (t =? t0)%Z = true).
apply (andb_prop).
rewrite (Bool.andb_assoc).
exact H.
destruct H0.
assert ((c =? c0)%Z = true /\ (t =? t0)%Z = true).
apply (andb_prop).
exact H1.
destruct H2.
destruct k.
destruct k0.
unfold SC_OT.eq in e.
inversion e.
rewrite <- H5.
rewrite (eqb_to_eq p p0).
rewrite (eqb_to_eq c c0).
rewrite (eqb_to_eq t t0).
reflexivity.
simpl in H.
exact H3.
exact H2.
exact H0.
discriminate H.
discriminate H.
destruct c0.
destruct c.
inversion H.
unfold SC_OT.eq in e.
destruct k.
destruct k0.
inversion e.
rewrite <- H1.
simpl in H.
rewrite (eqb_to_eq p p0 H).
reflexivity.
discriminate H.
destruct c0.
destruct c.
discriminate H.
discriminate H.
inversion H.
apply Z.eqb_eq in H.
rewrite H.
unfold SC_OT.eq in e.
destruct k.
destruct k0.
inversion e.
reflexivity.
simpl in H.
discriminate H.
Defined.

Lemma sc_kv_eqb_to_eq : forall a b : SC_MAP.key * CCStatus, sc_kv_eqb a b = true -> a = b.
intros.
assert (a = b <-> sc_kv_eqb a b = true).
apply (Bool.reflect_iff).
apply (SC_KV_EQB_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Theorem SC_MAP_elements_refl : forall x : SC_MAP.t CCStatus, list_eqb sc_kv_eqb (SC_MAP.elements x) (SC_MAP.elements x) = true.
intros.
induction SC_MAP.elements.
simpl.
reflexivity.
simpl.
rewrite IHl.
rewrite SC_KV_EQB_refl.
reflexivity.
Defined.

Theorem SCH_KV_EQB_refl : forall a : SCH_MAP.key * ConcreteChoice, sch_kv_eqb a a = true.
intros.
destruct a.
unfold sc_kv_eqb.
destruct k.
destruct i.
simpl.
rewrite (Z.eqb_refl).
destruct SCH_OT.eq_dec.
simpl.
reflexivity.
absurd (SCH_OT.eq (IdentChoice z, p) (IdentChoice z, p)).
exact n.
apply (SCH_OT.eq_refl).
Defined.


Theorem SCH_KV_EQB_spec : forall a b : SCH_MAP.key * ConcreteChoice, Bool.reflect (a = b) (sch_kv_eqb a b).
intros.
apply Bool.iff_reflect.
split.
intros.
rewrite H.
rewrite SCH_KV_EQB_refl.
reflexivity.
intros.
destruct a.
destruct b.
simpl in H.
destruct (SCH_OT.eq_dec k k0).
simpl in H.
destruct k.
destruct i.
destruct k0.
destruct i.
assert ((p =? p0)%Z = true /\ (z =? z0)%Z = true).
inversion e.
subst.
rewrite (Z.eqb_refl).
rewrite (Z.eqb_refl).
split; reflexivity.
destruct H0.
apply (eqb_to_eq) in H.
apply (eqb_to_eq) in H0.
apply (eqb_to_eq) in H1.
subst.
reflexivity.
inversion H.
Defined.

Lemma sch_kv_eqb_to_eq : forall a b : SCH_MAP.key * ConcreteChoice, sch_kv_eqb a b = true -> a = b.
intros.
assert (a = b <-> sch_kv_eqb a b = true).
apply (Bool.reflect_iff).
apply (SCH_KV_EQB_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Theorem SCH_MAP_elements_refl : forall x, list_eqb sch_kv_eqb (SCH_MAP.elements x) (SCH_MAP.elements x) = true.
intros.
induction SCH_MAP.elements.
simpl.
reflexivity.
simpl.
rewrite IHl.
rewrite SCH_KV_EQB_refl.
reflexivity.
Defined.

Theorem list_eqb_spec : forall {a : Type},forall f : a -> a -> bool, (forall x y : a, Bool.reflect (x = y) (f x y)) -> (forall x y : list a, Bool.reflect (x = y) (list_eqb f x y)).
intros a f X x y.
apply Bool.iff_reflect.
split.
apply (@doubleInduction a (fun x y : list a => x = y -> list_eqb f x y = true)).
intros.
destruct y0.
reflexivity.
inversion H.
intros.
destruct x0.
reflexivity.
inversion H.
intros.
simpl.
assert (Bool.reflect (x0 = y0) (f x0 y0)).
apply X.
apply (Bool.reflect_iff) in H1.
assert (x0 = y0).
inversion H0.
reflexivity.
apply H1 in H2.
apply (andb_true_intro).
split.
exact H2.
apply H.
inversion H0.
reflexivity.
apply (@doubleInduction a (fun x y : list a => list_eqb f x y = true -> x = y)).
intros.
destruct y0.
reflexivity.
inversion H.
intros.
destruct x0.
reflexivity.
inversion H.
intros.
simpl in H0.
apply (andb_prop) in H0.
destruct H0.
assert (Bool.reflect (x0 = y0) (f x0 y0)).
apply X.
apply (Bool.reflect_iff) in H2.
apply H2 in H0.
rewrite H0.
apply H in H1.
rewrite H1.
reflexivity.
Defined.

Theorem StateT_eqb_refl : forall a : StateT, StateT_eqb a a = true.
intros.
unfold StateT_eqb.
rewrite SC_MAP_elements_refl.
rewrite SCH_MAP_elements_refl.
reflexivity.
Defined.

Lemma list_sc_eqb_to_eq : forall x y, list_eqb sc_kv_eqb x y = true -> x = y.
intros.
assert (x = y <-> list_eqb sc_kv_eqb x y = true).
apply (Bool.reflect_iff).
apply (list_eqb_spec).
apply (SC_KV_EQB_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Lemma list_sch_eqb_to_eq : forall x y, list_eqb sch_kv_eqb x y = true -> x = y.
intros.
assert (x = y <-> list_eqb sch_kv_eqb x y = true).
apply (Bool.reflect_iff).
apply (list_eqb_spec).
apply (SCH_KV_EQB_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Theorem StateT_eqb_assoc : forall a b c : StateT, StateT_eqb a b = true -> StateT_eqb b c = true -> StateT_eqb a c = true.
intros.
unfold StateT_eqb in *.
apply (andb_prop) in H.
apply (andb_prop) in H0.
destruct H.
destruct H0.
apply (andb_true_intro).
split.
rewrite (list_sc_eqb_to_eq (SC_MAP.elements (sc a)) (SC_MAP.elements (sc b))); auto.
rewrite (list_sch_eqb_to_eq (SCH_MAP.elements (sch a)) (SCH_MAP.elements (sch b))); auto.
Defined.

Theorem Money_eqb_refl : forall a: Money, Money_eqb a a = true.
intro a.
induction a;
simpl;
try rewrite Z.eqb_refl;
try destruct i;
try rewrite Z.eqb_refl;
simpl;
intuition.
Defined.

Theorem Money_eqb_spec : forall x y : Money, Bool.reflect (x = y) (Money_eqb x y).
intros x y.
apply (Bool.iff_reflect).
split.
intros.
subst.
apply (Money_eqb_refl).
intros.
assert (forall a b : Money, Money_eqb a b = true -> a = b).
intro a.
induction a; intros.
simpl in H.
destruct b; destruct i; try destruct i0; try simpl in H; try inversion H0.
rewrite (eqb_to_eq z z0).
reflexivity.
exact H2.
simpl in H0.
destruct b; try inversion H0.
apply (andb_prop) in H0.
destruct H0.
rewrite (IHa1 b1).
rewrite (IHa2 b2).
reflexivity.
exact H1.
exact H0.
destruct b; try inversion H0.
apply (eqb_to_eq) in H2.
rewrite H2.
reflexivity.
destruct b; try inversion H0.
destruct i.
destruct i0.
apply (andb_prop) in H2.
destruct H2.
apply (andb_prop) in H1.
destruct H1.
apply (eqb_to_eq) in H1.
apply (eqb_to_eq) in H3.
rewrite (IHa b).
subst.
reflexivity.
exact H2.
apply H0.
apply H.
Defined.

Lemma Money_eqb_to_eq : forall a b : Money, Money_eqb a b = true -> a = b.
intros.
assert (a = b <-> Money_eqb a b = true).
apply (Bool.reflect_iff).
apply (Money_eqb_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Theorem Obs_eqb_refl : forall a : Observation, Obs_eqb a a = true.
intro a.
induction a;
simpl;
try rewrite Z.eqb_refl;
try destruct i;
try rewrite Z.eqb_refl;
try rewrite Z.eqb_refl;
simpl;
try rewrite IHa1;
try rewrite IHa2;
intuition.
rewrite Money_eqb_refl.
rewrite Money_eqb_refl.
reflexivity.
Defined.

Lemma andb_idemp : forall x : bool, x && true = true -> x = true.
intros.
destruct x.
reflexivity.
inversion H.
Defined.

Theorem Obs_eqb_spec : forall x y : Observation, Bool.reflect (x = y) (Obs_eqb x y).
intros.
apply (Bool.iff_reflect).
split.
intros.
subst.
apply (Obs_eqb_refl).
assert (forall a b : Observation, Obs_eqb a b = true -> a = b).
intro a.
induction a; intros; destruct b; try inversion H.
apply (eqb_to_eq) in H1.
rewrite H1.
reflexivity.
apply (andb_prop) in H1.
destruct H1.
rewrite (IHa1 b1).
rewrite (IHa2 b2).
reflexivity.
exact H1.
exact H0.
apply (andb_prop) in H1.
destruct H1.
rewrite (IHa1 b1).
rewrite (IHa2 b2).
reflexivity.
exact H1.
exact H0.
destruct H1.
rewrite (IHa b).
reflexivity.
exact H.
destruct i.
destruct i0.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H1.
destruct H1.
apply andb_idemp in H2.
apply (eqb_to_eq) in H0.
apply (eqb_to_eq) in H1.
apply (eqb_to_eq) in H2.
rewrite H0.
rewrite H1.
rewrite H2.
reflexivity.
destruct i.
destruct i0.
apply (andb_prop) in H1.
destruct H1.
apply (eqb_to_eq) in H0.
apply (eqb_to_eq) in H1.
rewrite H0.
rewrite H1.
reflexivity.
apply (andb_prop) in H1.
destruct H1.
apply (Money_eqb_to_eq) in H0.
apply (Money_eqb_to_eq) in H1.
rewrite H0.
rewrite H1.
reflexivity.
reflexivity.
reflexivity.
apply H.
Defined.

Lemma Obs_eqb_to_eq : forall a b : Observation, Obs_eqb a b = true -> a = b.
intros.
assert (a = b <-> Obs_eqb a b = true).
apply (Bool.reflect_iff).
apply (Obs_eqb_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Theorem Contract_eqb_refl : forall a : Contract, Contract_eqb a a = true.
intro a.
induction a;
try destruct i;
simpl;
try rewrite Obs_eqb_refl;
try rewrite Money_eqb_refl;
try rewrite IHa1;
try rewrite IHa2;
try rewrite IHa;
try rewrite Z.eqb_refl;
try rewrite Z.eqb_refl;
simpl;
try rewrite Z.eqb_refl;
try rewrite Z.eqb_refl;
reflexivity.
Defined.

Theorem Contract_eqb_spec : forall x y : Contract, Bool.reflect (x = y) (Contract_eqb x y).
intros.
apply (Bool.iff_reflect).
split.
intros.
subst.
apply (Contract_eqb_refl).
assert (forall a b : Contract, Contract_eqb a b = true -> a = b).
intro a.
induction a; intros; destruct b; try inversion H.
reflexivity.
destruct i.
destruct i0.
simpl in H1.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H0.
destruct H0.
apply (andb_prop) in H4.
destruct H4.
apply (andb_prop) in H5.
destruct H5.
apply andb_idemp in H6.
apply (eqb_to_eq) in H0.
apply (eqb_to_eq) in H4.
apply (eqb_to_eq) in H5.
apply (eqb_to_eq) in H6.
apply (Money_eqb_to_eq) in H1.
rewrite (IHa1 b1); auto.
rewrite (IHa2 b2); auto.
rewrite H0.
rewrite H1.
rewrite H4.
rewrite H5.
rewrite H6.
reflexivity.
destruct i.
destruct i0.
apply (andb_prop) in H1.
destruct H1.
apply (eqb_to_eq) in H0.
rewrite (IHa b); auto.
rewrite H0.
reflexivity.
destruct i.
destruct i0.
simpl in H1.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H0.
destruct H0.
apply (andb_prop) in H2.
destruct H2.
apply (andb_prop) in H3.
destruct H3.
apply (andb_prop) in H4.
destruct H4.
apply (andb_prop) in H5.
destruct H5.
clear H6.
apply (eqb_to_eq) in H2.
apply (eqb_to_eq) in H3.
apply (eqb_to_eq) in H4.
apply (eqb_to_eq) in H5.
apply (Money_eqb_to_eq) in H0.
rewrite (IHa b); auto.
rewrite H0.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite H5.
reflexivity.
apply (andb_prop) in H1.
destruct H1.
rewrite (IHa1 b1); auto.
rewrite (IHa2 b2); auto.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H0.
destruct H0.
apply (Obs_eqb_to_eq) in H0.
rewrite H0.
rewrite (IHa1 b1); auto.
rewrite (IHa2 b2); auto.
apply (andb_prop) in H1.
destruct H1.
apply (andb_prop) in H0.
destruct H0.
apply (andb_prop) in H1.
destruct H1.
apply (eqb_to_eq) in H0.
apply (Obs_eqb_to_eq) in H2.
rewrite H0.
rewrite H2.
rewrite (IHa1 b1); auto.
rewrite (IHa2 b2); auto.
apply H.
Defined.

Lemma Contract_eqb_to_eq : forall a b : Contract, Contract_eqb a b = true -> a = b.
intros.
assert (a = b <-> Contract_eqb a b = true).
apply (Bool.reflect_iff).
apply (Contract_eqb_spec).
destruct H0.
rewrite H1.
reflexivity.
apply H.
Defined.

Lemma Contract_eqb_size : forall a b : Contract, Contract_eqb a b = true -> Contract_size a = Contract_size b.
intros.
apply Contract_eqb_to_eq in H.
rewrite H.
reflexivity.
Defined.

Theorem step_order : forall (c nc : Contract) (inp : InputT) (st nst : StateT) (os : OST) (ac nac : AS), (nst, nc, nac) = step inp st c os -> ({StepValOrder (nst, nc, ac ++ nac) (st, c, ac)} + {(StateT_eqb st nst && Contract_eqb c nc && (match nac with | nil => true | _ :: _ => false end)) = true}).
intro c.
induction c; intros.
unfold step in H.
inversion H.
rewrite StateT_eqb_refl.
right.
reflexivity.
unfold step in H.
destruct (expired (blockNumber os) t || expired (blockNumber os) t0).
inversion H.
rewrite <- H2.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
destruct (CC_SET.mem (CC i p (evalMoney st m) t0) (cc inp)).
inversion H.
rewrite <- H2.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
inversion H.
right.
rewrite StateT_eqb_refl.
rewrite Contract_eqb_refl.
reflexivity.
unfold step in H.
destruct (SC_MAP.find (elt:=CCStatus) i (sc st)).
destruct c0.
destruct c0.
destruct (RC_SET.mem (RC i p c0) (rc inp)).
destruct (expired (blockNumber os) t).
inversion H.
rewrite <- H1.
rewrite <- H2.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
inversion H.
rewrite <- H1.
rewrite <- H2.
left.
unfold StepValOrder.
simpl.
intuition.
destruct (expired (blockNumber os) t).
inversion H.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
inversion H.
right.
rewrite StateT_eqb_refl.
rewrite Contract_eqb_refl.
reflexivity.
inversion H.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
inversion H.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
inversion H.
right.
rewrite StateT_eqb_refl.
rewrite Contract_eqb_refl.
reflexivity.
unfold step in H.
destruct expired.
left.
inversion H.
unfold StepValOrder.
simpl.
intuition.
destruct (match RP_MAP.find (elt:=Cash) (i, p0) (rp inp) with
               | Some claimed_val => (claimed_val =? evalMoney st m)%Z
               | None => false end).
destruct (stateUpdate st p p0 (blockNumber os) (evalMoney st m)).
destruct ((evalMoney st m) >=? 0)%Z.
inversion H.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
left.
inversion H.
unfold StepValOrder.
subst.
intuition.
destruct ((evalMoney st m) >=? 0)%Z.
inversion H.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
left.
inversion H.
unfold StepValOrder.
subst.
intuition.
inversion H.
right.
rewrite StateT_eqb_refl.
rewrite Contract_eqb_refl.
reflexivity.
simpl in H.
assert (forall (nst : StateT) (nc : Contract) (ac nac : AS),
       (nst, nc, nac) = step inp st c1 os ->
       {StepValOrder (nst, nc, ac ++ nac) (st, c1, ac)} +
       {StateT_eqb st nst && Contract_eqb c1 nc &&
        match nac with
        | nil => true
        | _ :: _ => false
        end = true}).
intros.
apply (IHc1 nc0 inp st nst0 os ac0 nac0).
exact H0.
destruct (step inp st c1 os).
destruct p.
assert (forall (ac : AS),
    {StepValOrder (s, c, ac ++ a) (st, c1, ac)} +
    {StateT_eqb st s && Contract_eqb c1 c &&
     match a with
     | nil => true
     | _ :: _ => false
     end = true}).
intros.
apply X.
reflexivity.
clear X.
assert (forall (nc : Contract) (nst : StateT) (ac nac : AS),
       (nst, nc, nac) = step inp s c2 os ->
       {StepValOrder (nst, nc, ac ++ nac) (s, c2, ac)} +
       {StateT_eqb s nst && Contract_eqb c2 nc &&
        match nac with
        | nil => true
        | _ :: _ => false
        end = true}).
intros.
apply (IHc2 nc0 inp s nst0 os ac0 nac0).
exact H1.
destruct (step inp s c2 os).
destruct (p).
assert (forall (ac : AS),
       {StepValOrder (s0, c0, ac ++ a0) (st, c2, ac)} +
       {StateT_eqb s s0 && Contract_eqb c2 c0 &&
        match a0 with
        | nil => true
        | _ :: _ => false
        end = true}).
intros.
apply X.
reflexivity.
clear X.
destruct (nulldec c); [ | destruct (nulldec c0)].
inversion H.
unfold StepValOrder in *.
simpl in *.
subst.
destruct (H0 nil).
destruct (H1 a).
left.
simpl in *.
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H2.
destruct H2.
apply (Contract_eqb_to_eq) in H4.
rewrite H4.
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H2.
destruct H2.
apply (Contract_eqb_to_eq) in H4.
rewrite H4.
destruct (H1 a).
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H5.
destruct H5.
apply (Contract_eqb_to_eq) in H7.
rewrite H7.
left.
intuition.

inversion H.
unfold StepValOrder in *.
simpl in *.
subst.
destruct (H0 nil).
destruct (H1 a).
left.
simpl in *.
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H2.
destruct H2.
apply (Contract_eqb_to_eq) in H4.
rewrite H4.
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H2.
destruct H2.
apply (Contract_eqb_to_eq) in H4.
rewrite H4.
destruct (H1 a).
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H5.
destruct H5.
apply (Contract_eqb_to_eq) in H7.
rewrite H7.
left.
intuition.

inversion H.
unfold StepValOrder in *.
simpl in *.
subst.
destruct (H0 nil).
destruct (H1 a).
left.
simpl in *.
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H2.
destruct H2.
apply (Contract_eqb_to_eq) in H4.
rewrite H4.
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H2.
destruct H2.
apply (Contract_eqb_to_eq) in H4.
rewrite H4.
destruct (H1 a).
intuition.
apply (andb_prop) in e.
destruct e.
apply (andb_prop) in H5.
destruct H5.
apply (Contract_eqb_to_eq) in H7.
rewrite H7.
right.
apply (andb_true_intro).
split.
apply (andb_true_intro).
split.
apply (StateT_eqb_assoc _ s _ ); auto.
apply (andb_true_intro).
split.
apply (Contract_eqb_refl).
apply (Contract_eqb_refl).
inversion H6.
inversion H3.
destruct a; destruct a0; auto.
simpl in H.
destruct (interpretObs st o os).
inversion H.
subst.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
inversion H.
subst.
left.
unfold StepValOrder.
unfold ContractOrder.
simpl.
intuition.
simpl in H.
destruct (expired (blockNumber os) t).
left.
unfold StepValOrder.
unfold ContractOrder.
inversion H.
rewrite <- H2.
simpl.
intuition.
destruct interpretObs.
left.
unfold StepValOrder.
unfold ContractOrder.
inversion H.
rewrite <- H2.
simpl.
intuition.
right.
inversion H.
subst.
rewrite (Contract_eqb_refl).
rewrite (StateT_eqb_refl).
reflexivity.
Defined.

Definition stepAllaux4 (com : InputT) (os : OST) (st : StateT) (con : Contract) (ac : AS)
      (f : forall y : StateT * Contract * AS, StepValOrder y (st, con, ac) -> StateT * Contract * AS)
      (nst : StateT) (ncon : Contract) (nac : AS) (Heqp : (nst, ncon, nac) = step com st con os) : StateT * Contract * AS :=
   match step_order con ncon com st nst os ac nac Heqp with
     | left s => f (nst, ncon, ac ++ nac) s
     | right _ => (st, con, ac)
   end.

(* Definition stepAllaux3 (com : InputT) (os : OST) (st : StateT) (con : Contract) (ac : AS)
      (f : forall y : StateT * Contract * AS, StepValOrder y (st, con, ac) -> StateT * Contract * AS) : StateT * Contract * AS :=
    match (step com st con os) with
           (nst, ncon, nac) => stepAllaux4 com os st con ac f nst ncon nac
    end eq_refl. *)

Lemma alt_refl : forall com st con os, (fst (fst (step com st con os)), snd (fst (step com st con os)), snd (step com st con os)) = step com st con os.
intros.
destruct (step).
destruct p.
reflexivity.
Defined.

Definition stepAllaux3 (com : InputT) (os : OST) (st : StateT) (con : Contract) (ac : AS)
      (f : forall y : StateT * Contract * AS, StepValOrder y (st, con, ac) -> StateT * Contract * AS) : StateT * Contract * AS :=
  stepAllaux4 com os st con ac f (fst (fst ((step com st con os)))) (snd (fst ((step com st con os)))) (snd ((step com st con os))) (alt_refl com st con os).

Definition stepAllaux2 (com : InputT) (os : OST) (x : StateT * Contract * AS) (f : forall y : StateT * Contract * AS, StepValOrder y x -> StateT * Contract * AS) : StateT * Contract * AS :=
  match x with
             (st, con, ac) as p => stepAllaux3 com os st con ac
  end f.

Definition stepAllaux (com : InputT) (st : StateT) (con : Contract) (os : OST) (ac : AS) : (StateT * Contract * AS) :=
  Fix stepValOrder_wf (fun _ => (StateT * Contract * AS)%type) (stepAllaux2 com os) (st, con, ac).

Definition stepAll (com : InputT) (st : StateT) (con : Contract) (os : OST) : (StateT * Contract * AS) :=
  stepAllaux com st con os nil.

Definition addNewChoices (acc : SCH_MAP_TYPE * AS) (cp : (IdentChoiceT * Person)) (choice_int : ConcreteChoice) : (SCH_MAP_TYPE * AS) := 
       let (recorded_choices, action_list) := acc in
       let (choice_id, person) := cp in
       if SCH_MAP.mem (choice_id, person) recorded_choices
       then (recorded_choices, action_list)
       else (SCH_MAP.add (choice_id, person) choice_int recorded_choices,
               ChoiceMade choice_id person choice_int :: action_list).

Definition recordChoices (input : InputT) (recorded_choices : SCH_MAP_TYPE) : (SCH_MAP_TYPE * AS) := 
      match input with | {| ic := ic0 |} =>
           fold_left (fun (X : SCH_MAP_TYPE * AS) (H : IdentChoiceT * Person * ConcreteChoice) =>
                              let (p, c) := H in addNewChoices X p c)
             (IC_MAP.elements ic0)
             (recorded_choices, nil)
      end.

Definition isExpiredNotRedeemed (e : Timeout) (ccs : CCStatus) : bool :=
   let (_, c) := ccs in
       match c with
       | NotRedeemed _ ee => expired e ee
       | ManuallyRedeemed => false
       | ExpiredAndRedeemed => false
       end.

Definition isClaimed (inp : InputT) (ident : IdentCCT) (status : CCStatus) : bool := 
       let (p, c) := status in
       match c with
       | NotRedeemed val _ => RC_SET.mem (RC ident p val) (rc inp)
       | ManuallyRedeemed => false
       | ExpiredAndRedeemed => false
       end.

Definition expiredAndClaimed (inp : InputT) (et : Timeout) (k : IdentCCT) (v : CCStatus) : bool :=
       isExpiredNotRedeemed et v && isClaimed inp k v.

Definition extractFromSCMap (f : IdentCCT -> CCStatus -> bool) (scmap : SC_MAP_TYPE) : list (IdentCCT * CCStatus) * SC_MAP_TYPE :=
       fold_left (fun (acc : list (IdentCCT * CCStatus) * SC_MAP_TYPE)
                           (el : IdentCCT * CCStatus) =>
                       let (t, m) := acc in
                       let (ident, status) := el in
                       if f ident status
                       then ((ident, status) :: t, SC_MAP.remove (elt:=CCStatus) ident m)
                       else (t, m))
                    (SC_MAP.elements scmap) 
                    (nil, scmap).

Definition markRedeemed (status : CCStatus) : CCStatus :=
  let (p, c) := status in
       match c with
         | NotRedeemed _ _
         | _ => (p, ExpiredAndRedeemed)
       end.

Definition expireCommits (inp : InputT) (scf : SC_MAP_TYPE) (os : OST) : (SC_MAP_TYPE * AS) :=
       let (expi, nsc) := extractFromSCMap (expiredAndClaimed inp (blockNumber os)) scf in
       (fold_left (fun (acc : SC_MAP_TYPE) (el : IdentCCT * CCStatus) =>
                         let (key, val) := el in SC_MAP.add key val acc)
                     (map (fun el : IdentCCT * CCStatus =>
                                  let (ident, status) := el in (ident, markRedeemed status))
                               expi)
                     nsc,
        fold_left (fun (acc : AS) (el : IdentCCT * CCStatus) =>
                         let (ident, status) := el in
                         let (p, crstatus) := status in
                         match crstatus with
                           | NotRedeemed val _ => ExpiredCommitRedeemed ident p val :: acc
                           | ManuallyRedeemed => acc
                           | ExpiredAndRedeemed => acc
                         end) expi nil).

Definition stepBlock (inp : InputT) (st : StateT) (con : Contract) (os : OST) : (StateT * Contract * AS) :=
       let (nsch, chas) := recordChoices inp (sch st) in
       let (nsc, pas) := expireCommits inp (sc st) os in
       let (res, ras) := stepAll inp {| sc := nsc; sch := nsch |} con os in
       let (rs, rcon) := res in
       (rs, rcon, chas ++ pas ++ ras).

Definition foldableStepBlock (acc : StateT * Contract * OST * AS) (inp : InputT) : (StateT * Contract *  OST * AS) :=
     let (p, a) := acc in
     let (p0, o) := p in
     let (s, c) := p0 in
     let (p1, a0) := stepBlock inp s c o in
       (p1, match o with {| blockNumber := bn |} => {| blockNumber := (bn + 1)%Z |} end, a ++ a0).

Definition emptyFSBAcc (c : Contract) : StateT * Contract * OST * AS.
repeat apply pair.
apply emptyState.
apply c.
apply emptyOS.
apply nil.
Defined.

Definition executeConcreteTrace (c : Contract) (inp : list InputT) : (StateT * Contract * OST * AS) :=
  fold_left foldableStepBlock inp (emptyFSBAcc c).

Definition composeInput (cc : list CCT) (rc : list RCT) (rp : list ((IdentPayT * Person) * Cash)) (ic : list ((IdentChoiceT * Person) * ConcreteChoice)) : InputT :=
       {| cc := fold_left (fun (m : CC_SET.t) (e : CCT) => CC_SET.add e m) cc emptyCCSet;
           rc := fold_left (fun (m : RC_SET.t) (e : RCT) => RC_SET.add e m) rc emptyRCSet;
           rp := fold_left (fun (m : RP_MAP_TYPE) (e : IdentPayT * Person * Cash) => let (k, v) := e in RP_MAP.add k v m) rp
                                emptyRPMap;
           ic := fold_left (fun (m : IC_MAP_TYPE) (e : IdentChoiceT * Person * ConcreteChoice) =>
                                        let (k, v) := e in IC_MAP.add k v m)
                                ic emptyICMap |}.

