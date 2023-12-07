
Fixpoint read {X: Type} (l: list (option X)) (i: nat) : option X :=
  match l with
  | nil => None 
  | cons h t =>
    match i with
    | 0 => h
    | S i' => read t i'
    end
  end.

Fixpoint insert {X: Type} (l: list (option X)) (i: nat) (x: X) : list (option X) :=
  match i with
  | 0 => cons (Some x) l
  | S i' => 
    match l with
    | nil => cons None (insert l i' x)
    | cons h t => cons h (insert t i' x)
    end
  end.

Fixpoint pop {X: Type} (l: list (option X)) (i: nat) : list (option X) :=
  match l with
  | nil => nil
  | cons h t => 
    match i with 
    | 0 => t
    | S i' => cons h (pop t i')
    end
  end.

Compute (insert (insert nil 5 9) 3 2)
.

Inductive BT (X: Type) : Type :=
| K (x: X)
| C (A: BT X) (B: BT X).

Arguments K {X}.
Arguments C {X}. 

Notation "x || y" := (C x y) (at level 50, left associativity).

Fixpoint proj' {X} (l: list (option bool)) (A: BT X) : BT X :=
  match A with
  | K x => K x
  | C L R => 
    match l with
    | nil => A
    | cons h t =>
      match h with
      | None => C (proj' t L) (proj' t R)
      | Some b => proj' t (if b then R else L)
      end
    end
  end.

Definition A := (( K 1 || K 2 ) || (K 3 || K 4) || K 5) || K 3.
(* Compute (proj' [None;Some false] A). *)

Fixpoint proj {X: Type} (n: nat) (b: bool) (t: BT X) :=
  match t with
  | K x => K x
  | C L R => 
    match n with
    | 0 => if b then R else L
    | S n' => C (proj n' b L) (proj n' b R)
    end
  end.

Compute (proj 0 false (( K 1 || K 2 ) || (K 3 || K 4))).

(* Fixpoint list'proj {X: Type} (l: list (option bool)) (n: nat) : (BT X)->(BT X) :=
  match l with
  | nil => (fun x => x)
  | cons h t =>
    match h with
    | None => list'proj t (S n)
    | Some b => (fun x => ((list'proj t n) (proj n b x)))
    end
  end

Compute ((list'proj [Some false; None; Some false] 0) A).
Compute (proj 1 false (proj 0 false A)). *)
  
Notation "x # b" := (proj 0 b x) (at level 50, left associativity).
Notation "x # [ b1 ; .. ; bn ]" := (proj 0 bn .. (proj 0 b1 x) .. ) 
  (at level 50, left associativity).
  
Fixpoint cat {X: Type} (n: nat) (A B : BT X):= 
  match n with
  | 0 => C A B
  | S n' => C (cat n' A B) (cat n' A B)
  end.

Compute proj 1 false (cat 2 (K 1) (K 2)).



Fixpoint u_map {X Y: Type} (uop: X->Y) (A: BT X) : BT Y :=
  match A with
  | K x => K (uop x)
  | C L R => C (u_map uop L) (u_map uop R)
  end.

Fixpoint bi_map {X Y Z: Type} (bop: X->Y->Z) (A: BT X) (B: BT Y) : BT Z :=
  match A, B with
  | K x, K y => K (bop x y)
  | K x, C L R => C (u_map (bop x) L) (u_map (bop x) R)
  | C L R, K y => C (u_map (fun x => bop x y) L) (u_map (fun x => bop x y) R)
  | C L R, C L' R' => C (bi_map bop L L') (bi_map bop R R')
  end.

Axiom eq_BT: forall X (A B: BT X),
  A = B <-> A # false = B # false /\ A # true = B # true.

Lemma aaa: forall X n b (A B: BT X),
  A = proj' nil B -> proj n b A = proj' (insert nil n b) B.
Proof.
  induction n as [|n' IHn].
  - intros.
    apply eq_BT in H as [H0 H1].
    destruct b.
    + rewrite H1. 
      induction B as [c|L R IHB].
      -- reflexivity.
      -- 
    destruct B; simpl in *.
    + apply H.
    + destruct b; simpl in *.

Theorem proj'pop: forall (X:Type) (l:list (option bool))(n:nat) (b:bool) (A B:BT X),
  A = proj' l B -> proj n b A = proj' (insert l n b) B.
Proof.
  induction l as [|h t IHl]; intros n b A B H.
  - induction n as [|n' IHn].
    + apply eq_BT.
  
  rewrite -> H.
Theorem cat_K: forall (X: Type) n (x: X),
  cat n (K x) (K x) = K x.
Proof.
  induction n as [|n' IHn]; intro x; apply eq_BT.
  + split; reflexivity.
  + split; apply IHn.
Qed.

Theorem eq_BT_n: forall X n (A B: BT X),
  A = B <-> proj n false A = proj n false B /\ proj n true A = proj n true B.
Proof.
  induction n as [|n' IHn]; intros A B; split.
  - split; apply f_equal, H.
  - apply eq_BT.
  - intro H. split; destruct A; apply f_equal, H.
  - induction A [|c ]. 
    + split. 
Qed.


Theorem cp_inv: forall X n (A: BT X),
  cat n (proj n false A) (proj n true A) = A.
Proof.
  induction n as [|n' IHn]; intro A.
  - apply eq_BT.
    split; reflexivity.
  - apply eq_BT.
    split.
    + simpl. destruct A.
      apply cat_K.
      apply eq_BT.
      split. simpl. apply IHn.
  
Qed.
