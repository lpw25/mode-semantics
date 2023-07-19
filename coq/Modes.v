Require Import Coq.Arith.Peano_dec.

Inductive result {A : Type} :=
  | ok (v : A)
  | out_of_gas
  | wrong.

Definition bind {A B : Type} (x : @result A) (f : A -> @result B) : @result B :=
  match x with
  | ok v => f v
  | out_of_gas => out_of_gas
  | wrong => wrong
  end.

Definition bindP {A : Type} (x : @result A) (f : A -> Prop) : Prop :=
  match x with
  | ok v => f v
  | out_of_gas => True
  | wrong => False
  end.

Definition bindP' {A : Type} (x : @result A) (f : A -> Prop) : Prop :=
  match x with
  | ok v => f v
  | out_of_gas => True
  | wrong => True
  end.

Declare Scope monad_scope.
Notation "x <- c1 ;; c2" := (@bind _ _ c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (@bind _ _ c1 (fun pat => c2))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (@bindP _ c1 (fun x => c2%type))
  (at level 61, c1 at next level, right associativity) : type_scope.

Notation "' pat <- c1 ;; c2" :=
  (@bindP _ c1 (fun pat => c2%type))
  (at level 61, pat pattern, c1 at next level, right associativity) : type_scope.

Notation "x <-? c1 ;; c2" := (@bindP' _ c1 (fun x => c2%type))
  (at level 61, c1 at next level, right associativity) : type_scope.

Notation "' pat <-? c1 ;; c2" :=
  (@bindP' _ c1 (fun pat => c2%type))
  (at level 61, pat pattern, c1 at next level, right associativity) : type_scope.


Open Scope monad_scope.
Delimit Scope monad_scope with monad.

Inductive sub_result {A : Type} : @result A -> @result A -> Prop :=
| sub_result_ok {v} : sub_result (ok v) (ok v)
| sub_result_wrong : sub_result wrong wrong
| sub_result_later {r} : sub_result out_of_gas r.

Lemma sub_result_refl {A : Type} {x : @result A} : sub_result x x.
destruct x as [v| |]; constructor. Qed.
Lemma sub_result_trans {A : Type} {x y z : @result A} :
  sub_result x y -> sub_result y z -> sub_result x z.
Proof. destruct 1; inversion 1; constructor. Qed.

Lemma bind_assoc {A B C : Type}
  {e1 : @result A}
  {e2 : A -> @result B}
  {e3 : B -> @result C} :
  (x <- (y <- e1 ;; e2 y) ;; e3 x)
  =
  (y <- e1 ;; x <- e2 y ;; e3 x).
Proof. destruct e1; easy. Qed.

Lemma bindP_assoc {A B : Type}
  {e1 : @result A}
  {e2 : A -> @result B}
  {e3 : B -> Prop} :
  (x <- (y <- e1 ;; e2 y)%monad ;; e3 x)%type
  =
  (y <- e1 ;; x <- e2 y ;; e3 x)%type.
Proof. destruct e1; easy. Qed.

Lemma bindP_monotone {A : Type}
  {e : @result A}
  {P Q : A -> Prop} :
  (x <- e ;; P x) ->
  (forall x, P x -> Q x) ->
  (x <- e ;; Q x).
Proof. destruct e; cbn; auto. Qed.

Lemma bindP'_assoc {A B : Type}
  {e1 : @result A}
  {e2 : A -> @result B}
  {e3 : B -> Prop} :
  (x <-? (y <- e1 ;; e2 y)%monad ;; e3 x)%type
  =
  (y <-? e1 ;; x <-? e2 y ;; e3 x)%type.
Proof. destruct e1; easy. Qed.

Lemma bindP'_monotone {A : Type}
  {e : @result A}
  {P Q : A -> Prop} :
  (x <-? e ;; P x) ->
  (forall x, P x -> Q x) ->
  (x <-? e ;; Q x).
Proof. destruct e; cbn; auto. Qed.

Lemma bind_sub_result_monotone {A B : Type}
  {e1 e2 : @result A}
  {f g : A -> @result B} :
  sub_result e1 e2 ->
  (forall x, sub_result (f x) (g x)) ->
  sub_result (x <- e1 ;; f x) (x <- e2 ;; g x).
Proof. destruct 1; cbn; auto; constructor. Qed.

Lemma bindP_antimonotone_left {A : Type}
  {e1 e2 : @result A}
  {P : A -> Prop} :
  (sub_result e2 e1) ->
  (x <- e1 ;; P x) ->
  (x <- e2 ;; P x).
Proof. destruct 1; cbn; auto. Qed.

Lemma bindP_and {A : Type}
  {e : @result A}
  {P Q : A -> Prop} :
  (x <- e ;; P x) ->
  (x <- e ;; Q x) ->
  (x <- e ;; (P x /\ Q x)).
Proof. destruct e; cbn; auto. Qed.

Lemma bindP_or {A : Type}
  {e : @result A}
  {P Q : A -> Prop} :
  (x <- e ;; P x) \/ (x <- e ;; Q x) ->
  (x <- e ;; (P x \/ Q x)).
Proof. destruct e; cbn; intros [p|q]; auto. Qed.

Lemma bindP_remember {A : Type}
  {e : @result A}
  {P : A -> Prop} :
  (x <- e ;; P x) ->
  (x <- e ;; (e = ok x /\ P x)).
Proof. destruct e; cbn; auto. Qed.

(* Length-indexed lists, again *)

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons {n} : vector A n -> A -> vector A (S n).

Notation "xs  ,, x" := (@vcons _ _ xs x)
  (at level 90, left associativity).

Inductive v0_vS {A : Set} := v0 | vS (v : A).
Fixpoint vref (n : nat) : Set :=
  match n with
  | 0 => Empty_set
  | S n => @v0_vS (vref n)
  end.
Arguments vref !n.

Fixpoint vlookup {A : Type} {n} (vec : vector A n) : vref n -> A :=
  match vec in vector _ n return vref n -> A with
  | vnil _ => Empty_set_rect _
  | vcons _ xs x =>
    fun var => match var with
    | v0 => x
    | vS var => vlookup xs var
    end
  end.

Fixpoint vupdate {A : Type} {n} (vec : vector A n) : vref n -> A -> vector A n :=
  match vec in vector _ n return vref n -> A -> vector A n with
  | vnil _ => Empty_set_rect _
  | vcons _ xs x =>
    fun var val => match var with
    | v0 => vcons _ xs val
    | vS var => vcons _ (vupdate xs var val) x
    end
  end.

Definition vhead {A : Type} {n} (vec : vector A (S n)) : A :=
  match vec in vector _ n return match n with 0 => unit | S n => A end with
  | vnil _ => tt
  | vcons _ xs x => x
  end.
Definition vtail {A : Type} {n} (vec : vector A (S n)) : vector A n :=
  match vec in vector _ n return match n with 0 => unit | S n => vector A n end with
  | vnil _ => tt
  | vcons _ xs x => xs
  end.
(*
Definition vuncons {A : Type} {n} (vec : vector A (S n)) : vector A n * A :=
  match vec in vector _ n return match n with 0 => unit | S n => vector A n * A end with
  | vnil _ => tt
  | vcons _ xs x => (xs , x)
  end.
*)


Fixpoint eta_vec {A : Type} {n} : vector A n -> vector A n :=
  match n with
  | 0 => fun vec => vnil _
  | S n => fun vec =>
    vcons _ (eta_vec (vtail vec)) (vhead vec)
  end.

Lemma eta_vec_eq {A : Type} {n} (v : vector A n) : v = eta_vec v.
Proof. induction v; cbn; congruence. Qed.

Lemma vec_extensional {A n} {v w : vector A n} :
  (forall x, vlookup v x = vlookup w x) -> v = w.
Proof.
  rewrite (eta_vec_eq v). rewrite (eta_vec_eq w).
  induction n; [easy | intro H; cbn].
  f_equal.
  - apply IHn. intros x. apply (H (vS x)).
  - apply (H v0).
Qed.


Fixpoint zip {A B C : Type} (f : A -> B -> C) {n} : forall (v : vector A n) (w : vector B n), vector C n :=
  match n with
  | 0 => fun _ _ => vnil _
  | S n => fun v w =>
    vcons _ (zip f (vtail v) (vtail w)) (f (vhead v) (vhead w))
  end.

Arguments zip A B C f !n !v !w.

(*
Fixpoint zipP {A B : Type} (P : A -> B -> Prop) {n} : forall (v : vector A n) (w : vector B n), Prop :=
  match n with
  | 0 => fun _ _ => True
  | S n => fun v w =>
     zipP P (vtail v) (vtail w) /\ P (vhead v) (vhead w)
  end.

Arguments zipP A B P !n !v !w.


Lemma vlookup_zip {A B C} {f : A -> B -> C} {n} {v w} {k : vref n} :
  vlookup (zip f v w) k = f (vlookup v k) (vlookup w k).
Proof.
  rewrite (eta_vec_eq v). rewrite (eta_vec_eq w).
  induction n; [ easy | ].
  destruct k as [| k]; cbn.
  - easy.
  - auto.
Qed.

Lemma vlookup_zipP {A B} {P : A -> B -> Prop} {n} {v w} {k : vref n} :
  zipP P v w -> P (vlookup v k) (vlookup w k).
Proof.
  rewrite (eta_vec_eq v). rewrite (eta_vec_eq w).
  induction n; [ easy | ].
  destruct k as [| k]; cbn; firstorder.
Qed.
*)

Definition vec_related {A B n} (R : A -> B -> Prop) (v : vector A n) (w : vector B n) :=
  forall x, R (vlookup v x) (vlookup w x).

Lemma vec_related_nil {A B} {R : A -> B -> Prop} : vec_related R (vnil _) (vnil _). easy. Qed.
Lemma vec_related_cons {A B n} {R : A -> B -> Prop} {xs : vector A n} {x ys y} :
  vec_related R xs ys -> R x y -> vec_related R (xs ,, x) (ys ,, y).
Proof. intros Hvecs HR [|var]; cbn; easy. Qed.



Definition result_of_option {A : Type} (x : option A) :=
  match x with
  | None => wrong
  | Some x => ok x
  end.

Fixpoint lookup {A : Type} (env : list A) (v : nat) {struct v} : @result A :=
  match v, env with
  | 0, cons e _ => ok e
  | S n, cons _ xs => lookup xs n
  | _, nil => wrong
  end.

Fixpoint update {A : Type} (env : list A) (ix : nat) (v : A) {struct ix} : @result (list A) :=
  match ix, env with
  | 0, cons _ env => ok (cons v env)
  | 0, nil => wrong
  | S n, nil => wrong
  | S n, cons x xs => bind (update xs n v) (fun xs => ok (cons x xs))
  end.

Fixpoint fresh_ix {A : Type} (env : list A) (ix : nat) {struct env} :=
  match env, ix with
  | nil, _ => True
  | cons _ _, 0 => False
  | cons _ env, S n => fresh_ix env n
  end.

Fixpoint extend {A : Type} (env : list A) (el : A) :=
  match env with
  | nil => cons el nil
  | cons x env => cons x (extend env el)
  end.

Fixpoint truncate {A : Type} (env : list A) (len : nat) {struct env} :=
  match env, len with
  | _, 0 => nil
  | nil, _ => nil
  | cons x env, S n => cons x (truncate env n)
  end.


Lemma length_is_fresh {A : Type} (env : list A) : fresh_ix env (length env).
induction env; cbn; easy. Qed.

(*
Lemma lookup_nil {A : Type} {v : nat}: @lookup A nil v = wrong.
Proof. induction v; try easy. Qed.

Lemma update_nil {A : Type} {v x} : @update_opt A nil v x = wrong.
Proof. induction v; try easy. Qed.

Notation update env ix v := (update_opt env ix (Some v)).
Notation remove env ix := (update_opt env ix None).
*)

(*
Lemma update_spec :
  forall v w env a,
    bind (update_opt env v a) (fun env => lookup env w) =
    if Nat.eqb v w then result_of_option a else lookup env w.
Proof.
  induction v.
  - cbn; intros [|w] [|hd env] a; cbn; try easy. apply lookup_nil.
  - intros [|w] [|hd env] a; try (cbn; easy).
    cbn. rewrite IHv. rewrite lookup_nil. easy.
Qed.
*)


Inductive two : Set := two_left | two_right.

Inductive linearity_mode := Once | Many.
Inductive uniqueness_mode := Unique | Shared.
Inductive locality_mode := Global | Local.


Definition sub_linearity (a b : linearity_mode) :=
  match a, b with
  | Many, Once => False
  | _, _ => True
  end.

Definition sub_uniqueness (a b : uniqueness_mode) :=
  match a, b with
  | Shared, Unique => False
  | _, _ => True
  end.

Definition sub_locality (a b : locality_mode) :=
  match a, b with
  | Local, Global => False
  | _, _ => True
  end.


Inductive term {vars : nat} : Set :=
| var (mode : linearity_mode) (v : vref vars)
| app (lin : linearity_mode) (f e : term)
| abs (loc : locality_mode) (e : @term (S vars))

| letv (e : term) (e : @term (S vars))

| pair (l r : term)
| unpair (p : term) (body : @term (S (S vars)))

| inj (ix : two) (e : term)
| case (e : term) (l : @term (S vars)) (r : @term (S vars))

| unit
| seq (e : term) (e : term)

| region (e : term)
| ref (m : locality_mode) (e : term)
| getref (mode : linearity_mode) (e : term)
| setref (e : term) (e : term).


Fixpoint has_free_var {vars} (vf : vref vars) (t : @term vars) : Prop :=
  match t with
  | var _mode v => v = vf
  | app _lin f e => has_free_var vf f \/ has_free_var vf e
  | abs _loc body => @has_free_var (S vars) (vS vf) body
  | letv e body => has_free_var vf e \/ @has_free_var (S _) (vS vf) body
  | pair l r => has_free_var vf l \/ has_free_var vf r
  | unpair e body => has_free_var vf e \/ @has_free_var (S (S _)) (vS (vS vf)) body
  | inj ix e => has_free_var vf e
  | case e l r => has_free_var vf e \/ @has_free_var (S _) (vS vf) l \/ @has_free_var (S _) (vS vf) r
  | unit => False
  | seq e1 e2 => has_free_var vf e1 \/ has_free_var vf e2
  | region e => has_free_var vf e
  | ref _ e => has_free_var vf e
  | getref _ e => has_free_var vf e
  | setref e x => has_free_var vf e \/ has_free_var vf x
  end.

Notation decision P := ({P} + {~ P}).

Lemma eq_decidable {vars} : forall (v w : vref vars), decision (v = w). induction vars; decide equality. Qed.
Lemma or_decidable {P Q} : decision P -> decision Q -> decision (P \/ Q). firstorder. Qed.
Lemma nat_eq_decidable : forall (n m : nat), decision (n = m). induction n; decide equality. Qed.

Lemma decide_free_var {vars} (t : @term vars) : forall v, decision (has_free_var v t).
Proof. induction t; cbn; auto using or_decidable, eq_decidable. Qed.


Record Address := { addr_loc: locality_mode; addr_pos: nat }.


Inductive value : Type :=
| v_closure {vars} (env : Address) (body : @term (S vars))
| v_pair (l r : value)
| v_inj (ix : two) (v : value)
| v_unit
| v_address (addr : Address).

Notation Field := (option (uniqueness_mode * value)).

Inductive Block := block (len : nat) (fields : vector Field len).

Notation Environment := (vector Field).

Record Memory := mkMemory { mem_stack : list Block; mem_heap : list Block }.

Definition update_mem (mem : Memory) (addr : Address) (v : Block) :=
  let (stack, heap) := mem in
  match addr_loc addr with
  | Local =>
    stack <- update stack (addr_pos addr) v ;;
    ok {| mem_stack := stack; mem_heap := heap |}
  | Global =>
    heap <- update heap (addr_pos addr) v ;;
    ok {| mem_stack := stack; mem_heap := heap |}
  end.

Definition lookup_mem (len : nat) (mem : Memory) (addr : Address) : @result (vector Field len) :=
  let mem :=
      match addr_loc addr with
      | Local => mem_stack mem
      | Global => mem_heap mem
      end
  in
  '(block len' body) <- lookup mem (addr_pos addr) ;;
  match nat_eq_decidable len len' with
  | left equ =>
    match equ in _ = len' return vector _ len' -> @result (vector _ len) with
    | eq_refl => ok
    end body
  | right _ => wrong
  end.

Fixpoint empty_vec {len} : vector Field len :=
  match len with
  | 0 => vnil _
  | S n => empty_vec ,, None
  end.

Print lookup_mem.
Definition extend_mem (mem : Memory) (len : nat) (mode : locality_mode) :=
  let (stack, heap) := mem in
  match mode with
  | Local => {| mem_stack := extend stack (block len empty_vec); mem_heap := heap |}
  | Global => {| mem_stack := stack; mem_heap := extend heap (block len empty_vec) |}
  end.

Definition next_addr (mem : Memory) (mode : locality_mode) :=
  let pos :=
      match mode with
      | Local => length (mem_stack mem)
      | Global => length (mem_heap mem)
      end
  in
  {| addr_loc := mode; addr_pos := pos |}.

Definition alloc_mem mem mode len :=
  (next_addr mem mode, extend_mem mem len mode).

Definition fresh_in_mem (mem : Memory) (addr : Address) :=
  match addr_loc addr with
  | Local => fresh_ix (mem_stack mem) (addr_pos addr)
  | Global => fresh_ix (mem_heap mem) (addr_pos addr)
  end.

Lemma sub_uniqueness_trans {a b c} :
  sub_uniqueness a b -> sub_uniqueness b c -> sub_uniqueness a c.
Proof. destruct a, b, c; easy. Qed.


Inductive has_free_addr (addr : Address) : value -> Prop :=
| free_closure_env {vars} {body : @term (S vars)} : has_free_addr addr (v_closure addr body)
| free_pair_l {l r} : has_free_addr addr l -> has_free_addr addr (v_pair l r)
| free_pair_r {l r} : has_free_addr addr r -> has_free_addr addr (v_pair l r)
| free_inj {ix v} : has_free_addr addr v -> has_free_addr addr (v_inj ix v)
| free_addr : has_free_addr addr (v_address addr).

Definition has_free_addr_field (addr : Address) (uq : uniqueness_mode) (f : Field) : Prop :=
  match f with
  | None => False
  | Some (uq', v') =>
    sub_uniqueness uq' uq /\
    has_free_addr addr v'
  end.

Inductive has_free_addr_a (mem : Memory) (addr : Address) (uq : uniqueness_mode) (a : Address) : Prop :=
| free_contents {len ix block} :
   lookup_mem len mem a = ok block ->
   has_free_addr_field addr uq (vlookup block ix) ->
   has_free_addr_a mem addr uq a.

Inductive has_reachable_addr_field (mem : Memory) (uq : uniqueness_mode) (addr : Address) (fd : Field) : Prop :=
| reachable_one :
   has_free_addr_field addr uq fd ->
   has_reachable_addr_field mem uq addr fd
| reachable_step {addr' uq' len' block'} :
   has_free_addr_field addr' uq' fd ->
   lookup_mem len' mem addr' = ok block' ->
   (exists ix, has_reachable_addr_field mem uq addr (vlookup block' ix)) ->
   has_reachable_addr_field mem uq addr fd.

Notation has_reachable_addr_block mem uq addr block :=
  (exists ix, has_reachable_addr_field mem uq addr (vlookup block ix)).


(*

v holds l uniquely
Some (Unique, v) holds l uniquely

v holds l shared
Some (Unique, v) holds l shared

v holds l uniquely
Some (Shared, v) holds l shared???

v holds l shared
Some (Shared, v) holds l shared

not:
v holds l uniquely
Some (Shared, v) holds l uniquely

*)

(* FIXME golf *)
(*
Fixpoint has_free_addr_monotone {mem uq uq' addr v}
  (H : has_free_addr mem uq addr v) { struct H } :
  sub_uniqueness uq uq' ->
  has_free_addr mem uq' addr v.
Proof.
  destruct H; intros Hsub;
    try (econstructor; solve [eassumption | eauto using sub_uniqueness_trans]).
Admitted.
*)



(*
Inductive well_sep (mem : Memory) : forall {vars} (env : Environment vars) (uq : uniqueness_mode), value -> Prop :=
| sep_closure {vars} {env : Environment vars} {uq}
    {clvars} {clenv : Environment clvars} {body : @term (S clvars)} :
   well_sep_env mem clenv ->
   (* FIXME: separation between environments? *)
   well_sep mem env uq (v_closure clenv body)
| sep_pair {vars} {env : Environment vars} {l r uq} : well_sep mem env uq l -> @well_sep mem _ (env ,, Some (uq, l)) uq r -> well_sep mem env uq (v_pair l r)
| sep_inj {vars} {env : Environment vars} {uq} {ix v} : well_sep mem env uq v -> well_sep mem env uq (v_inj ix v)
| sep_unit {vars} {env : Environment vars} {uq} : well_sep mem env uq v_unit
(*| sep_address : (*FIXME*)
    lookup_mem mem a = ok (Some (uq', v)) ->*)

with well_sep_env (mem : Memory) : forall {vars}, Environment vars -> Prop :=
| sep_empty : well_sep_env mem (vnil _)
| sep_cons_none {vars} {env : Environment vars} : well_sep_env mem env -> well_sep_env mem (env ,, None)
| sep_cons_some {vars} {env : Environment vars} {uq v} :
  well_sep_env mem env -> well_sep mem env uq v -> well_sep_env mem (env ,, Some (uq , v)).
*)


(*

Locations & refs & mutation

Ref containing shared/many/global A

Location containing unique A:
  can only be used once because taking it kills it

Location containing an A with inherited uniqueness (???)
  x : ref A
if you hold x uniquely, its contents are unique
if you share x, its contents are shared

You can deref x to get the contents, but x must be once if this is unique (?)
You can strong-update x

Consider ops on the inplace-updatable singleton:
  x.contents
  { contents = e }
  { unique x with contents = e }

Looking like I should have mutable uniqueness markers here?
Put them in the store, like the environment?
And share them like VAR?

What does 'unique' on a location actually mean,
 if the reference itself is shared?

It means that the reference holds the unique copy of its contents,
 which is possible for a shared reference that's only used once.
(Guaranteeing that it's only used once sounds hard, though?)

Similarly, what does 'unique' on a captured variable actually mean?
 - Unique on a captured variable implies the closure is once
 - Might want to change variables to 'shared' before capture

Hmm, when capturing variables we need to update unique -> shared sometimes.
Should I annotate lambdas somehow?

Is there necessarily a best way to do so?
Lambda annotations:
 If there's a unique var in Γ, we could
    (a) capture it uniquely, making a lambda callable only once
    (b) capture it shared, making a reusable lambda
    (c) borrow it
I think there's a principal choice between a/b, since it's a simple constraint:
  if capture is Unique then lambda is Once
  if var_mode ≤ Unique then clos_mode ≥ Once (???)
Is this monotone in some sense?

*)



Set Primitive Projections.

Definition Machine_state (vars : nat) : Type :=
  (Environment vars * Memory).

Definition environment {vars} : Machine_state vars -> Environment vars := fst.
Definition smemory {vars} : Machine_state vars -> Memory := snd.


Lemma bind_exten {A B : Type} {x y : @result A} {f g : A -> @result B} :
  x = y -> (forall a, f a = g a) -> bind x f = bind y g.
Proof. intros <- H. destruct x; cbn; try easy. Qed.

Lemma bindP_exten {A : Type} {x y : @result A} {f g : A -> Prop} :
  x = y -> (forall a, f a = g a) -> bindP x f = bindP y g.
Proof. intros <- H. destruct x; cbn; try easy. Qed.

Definition meet_uniqueness l r :=
  match l, r with
  | Unique, Unique => Unique
  | Shared, _
  | _, Shared => Shared
  end.

Definition access (f : Field) (lin : linearity_mode) : @result (Field * uniqueness_mode * value) :=
  match f with
  | None => wrong
  | Some (uq, x) =>
    match lin, uq with
    | Many, Shared => ok (f, Shared, x)
    | Many, Unique => ok (Some (Shared, x), Shared, x)
    | Once, Shared => ok (None, Shared, x)
    | Once, Unique => ok (None, Unique, x)
    end
  end.

Fixpoint eval {vars} (steps : nat) (state : Machine_state vars) (e : @term vars) {struct steps} : @result (Machine_state vars * uniqueness_mode * value) :=
  match steps with
  | 0 => out_of_gas
  | S steps =>
    match e with
    | var lin v =>
      let (env, mem) := state in
      '(slot, uq, r) <- access (vlookup env v) lin ;;
      ok ((vupdate env v slot, mem), uq, r)

    | app lin f e =>
      '(state, uqf, f) <- eval steps state f ;;
      '(state, uqe, e) <- eval steps state e ;;
      match f with
      | @v_closure vars env_addr body =>
        let (senv, mem) := state in
        env <- lookup_mem vars mem env_addr ;;
        '(state, uqr, res) <- eval steps (env ,, Some (uqe, e), mem) body ;;
        let (env', mem) := state in
        ok ((senv, mem), uqr, res)
      | _ => wrong
      end

    | abs loc body =>
      (* FIXME split environment properly *)
      let (env, mem) := state in
      let (env_addr, mem) := alloc_mem mem loc vars in
      mem <- update_mem mem env_addr (block vars env) ;;
      ok (state, Unique, v_closure env_addr body)

    | letv e body =>
      '(state, uqe, e) <- eval steps state e ;;
      let (env, mem) := state in
      '(state, uqr, r) <- eval steps (env ,, Some (uqe, e), mem) body ;;
      let (env, mem) := state in
      ok ((vtail env, mem), uqr, r)
      
    | pair l r =>
      '(state, uql, l) <- eval steps state l ;;
      '(state, uqr, r) <- eval steps state r ;;
      ok (state, meet_uniqueness uql uqr, v_pair l r)

    | unpair e body =>
      '(state, uqe, e) <- eval steps state e ;;
      match e with
      | v_pair l r =>
        let (env, mem) := state in
        '(state, uqr, r) <- eval steps (env ,, Some (uqe, l) ,, Some (uqe, r), mem) body ;;
        let (env, mem) := state in
        ok ((vtail (vtail env), mem), uqr, r)
      | _ => wrong
      end

    | inj ix e =>
      '(state, uqe, e) <- eval steps state e ;;
      ok (state, uqe, v_inj ix e)

    | case e l r =>
      '(state, uqe, e) <- eval steps state e ;;
      match e with
      | v_inj ix e =>
        let body := match ix with two_left => l | two_right => r end in
        let (env, mem) := state in
        '(state, uqr, r) <- eval steps (env ,, Some (uqe, e), mem) body ;;
        let (env, mem) := state in
        ok ((vtail env, mem), uqr, r)
      | _ => wrong
      end
    
    | unit =>
      ok (state, Unique, v_unit)

    | seq e1 e2 =>
      '(state, _uqe, e) <- eval steps state e1 ;;
      match e with
      | v_unit =>
        eval steps state e2
      | _ => wrong
      end

    | region e =>
      let sp := length (mem_stack (smemory state)) in
      '((env, mem), uq, e) <- eval steps state e ;;
      let mem := {| mem_heap := mem_heap mem;
                    mem_stack := truncate (mem_stack mem) sp |} in
      ok ((env, mem), uq, e)
      
    | ref mode e =>
      let (env, mem) := state in
      let (addr, mem) := alloc_mem mem mode 1 in
      ok ((env, mem), Unique, v_address addr)

    | getref lin r =>
      '(state, uq, r) <- eval steps state r ;;
      match r with
      | v_address addr =>
        let (env, mem) := state in
        slot <- lookup_mem 1 mem addr ;;
        '(v, uq, r) <- access (vlookup slot v0) lin ;;
        mem <- update_mem mem addr (block 1 (vupdate slot v0 v)) ;;
        ok ((env, mem), uq, r)
      | _ => wrong
      end

    | setref r e =>
      (* FIXME: does uqr matter? *)
      '(state, _uqr, r) <- eval steps state r ;;
      '((env, mem), uqe, e) <- eval steps state e ;;
      match r with
      | v_address addr =>
        mem <- update_mem mem addr (block 1 (vcons _ (vnil _) (Some (uqe, e)))) ;;
        ok ((env, mem), Unique, v_unit)
      | _ => wrong
      end
    end
  end.

Arguments eval vars !steps state !e.


Inductive MARKER : Prop := TAC_MARKER.

Ltac revert_to_marker :=
  match goal with
  | [ H : _ |- _ ] =>
    revert H;
    match goal with
    | [ |- MARKER -> _ ] => intros []
    | _ => revert_to_marker
    end
  end.

Ltac split_hyp :=
  match goal with
  | [ |- forall H, _ ] =>
    let n := numgoals in
    let H := fresh H in intro H; progress (elim H); clear H;
    let m := numgoals in guard m <= n
  end.

Ltac split_cases := 
  match goal with
    | |- context C [match ?x with _ => _ end] =>
      match x with 
        | context C [match _ with _ => _ end] => fail 1
        | _ => pose proof TAC_MARKER; idtac "splitting" x; destruct x; revert_to_marker; simpl in *
      end
  end.

Lemma eval_monotone {vars steps} {state : Machine_state vars} {e : @term vars} :
  sub_result (eval steps state e) (eval (S steps) state e).
Proof.
  revert vars state e; induction steps; [ constructor | ]; intros vars state e.
  destruct e; cbn; repeat first [
    easy
  | apply sub_result_refl
  | apply bind_sub_result_monotone; [(easy || apply sub_result_refl)|]
  | progress (repeat split_hyp; intros)
  | split_cases
  ].
Qed.

Notation not_wrong e := (x <- e ;; True)%type.

Lemma access_no_thin_air {f lin} :
  '(_newf, uq, v) <-? access f lin ;;
  forall addr, has_free_addr addr v ->
  has_free_addr_field addr uq f.
Proof.
  destruct f as [[uq vf] | ].
  - destruct lin, uq; cbn; auto.
  - easy.
Qed.

Lemma eval_no_thin_air :
  forall {steps vars} {state : Machine_state vars} {e : @term vars},
    '((env, mem), uq, v) <-? eval steps state e ;;
    forall addr, has_free_addr addr v ->
    has_reachable_addr_block (smemory state) uq addr (environment state)
    \/
    fresh_in_mem (smemory state) addr.
Proof.
  induction steps; [ cbv; easy | destruct state as [env mem]; destruct e; cbn ].
  - rewrite bindP'_assoc.
    eapply bindP'_monotone. apply access_no_thin_air.
    intros [[fd uq] vl] Hvl.
    cbn.
    left.
    econstructor.
Admitted.
  

Record mode := mkMode {
  linearity : linearity_mode;
  uniqueness : uniqueness_mode;
  locality : locality_mode
}.

Definition sub_mode (a b : mode) :=
  let (lin, uq, loc) := a in
  let (lin', uq', loc') := b in
  sub_linearity lin lin'
  /\
  sub_uniqueness uq uq'
  /\
  sub_locality loc loc'.

Lemma sub_mode_refl : forall a, sub_mode a a.
Proof. intros [[|] [|] [|]]; easy. Qed.

Lemma sub_mode_trans :
  forall a b c, sub_mode a b -> sub_mode b c -> sub_mode a c.
Proof. repeat intros [[|] [|] [|]]; cbv; easy. Qed.


Inductive type :=
| FN (marg : mode) (arg : type) (mres : mode) (res : type)
| PROD (l r : type)
| SUM (l r : type)
| UNIT
| REF (a : type).

Definition Field_type := option (mode * type).
Definition Context vars := vector Field_type vars.

Record Store_context := mkStoreContext {
  stack_ctx : list type;
  heap_ctx : list type
}.

Definition stype := Store_context -> Memory -> mode -> value -> Prop.

(*
used as global, used as local -> used as global

used as once, used as once -> used as many

used as unique, used as unique -> ???
*)

(* Filters the fields to the ones expected to still be present after evaluation*)
Definition binding_after (b : Field_type) (v : Field) : Field. Admitted.
(*
  match b, v with
  | None, v => v
  | Some (mode, _), v =>
    match linearity mode with
    | Once => None
    | Many =>
      match uniqueness mode with
      | Shared => v
  end.
*)

Definition evaluates {vars} (state : Machine_state vars) Σ mode (A : stype) e :=
  forall steps,
    '((env, mem), uq, x) <- eval steps state e ;;
    A Σ mem mode x.

Fixpoint ok_value (Ty : type) (Σ : Store_context) mem loc val : Prop :=
  match Ty, val with
  | FN marg A mres B,
    v_closure env body =>
    forall v,
      ok_value A Σ mem (locality marg) v ->
      evaluates ((env ,, Some (uniqueness marg, v)), mem) Σ (ok_value B) (locality mres) body
    
  | _, _ => False
  end.

Record OK_state {vars} (steps : nat) (Γ : context vars) (Σ : store_context) (state : machine_state vars) := mkOK_state {
  ok_env : forall v,
     let (env, mem) := state in
     match vlookup Γ v, vlookup env v with
     | None, _ => True
     | Some _, None => False
     | Some (mode, A), Some v => ty_mem A steps mem mode v
     end;

  (* FIXME *)
  ok_env_uniqueness : True;

  (* FIXME *)
  ok_stack : True;

  (* FIXME *)
  ok_heap : True
}.

Inductive sub_option {A : Type} : option A -> option A -> Prop :=
| sub_option_none {a} : sub_option None (Some a)
| sub_option_some {a} : sub_option (Some a) (Some a).

Definition filter_option {A : Type} (P : A -> bool) (x : option A) :=
  match x with
  | None => None
  | Some x => if P x then Some x else None
  end.

Definition sub_vector {A : Type} {n} (a b : vector (option A) n) : Prop :=
  forall v, sub_option (vlookup a v) (vlookup b v).

Fixpoint filter_vec {A : Type} (P : A -> bool) {n} (v : vector (option A) n) : vector (option A) n :=
  match v with
  | vnil _ => vnil _
  | vcons _ xs x =>
    vcons _ (filter_vec P xs) (filter_option P x)
  end.

Lemma sub_vector_nil {A : Type} : sub_vector (vnil (option A)) (vnil (option A)). intros []. Qed.
Lemma sub_vector_cons {A : Type} {x y n} {xs ys : vector (option A) n} :
  sub_vector xs ys -> sub_option x y -> sub_vector (vcons _ xs x) (vcons _ ys y).
intros Hxs Hx [|v]; cbn; auto. Qed.


Definition is_many (mA : mode * type) :=
  let (m, A) := mA in
  match linearity m with
  | Once => false
  | Many => true
  end.

Record OK_result {vars}
  (Γ : context vars)
  (A : type)
  (before after : machine_state vars)
  (m : mode)
  (v : value)
  (steps : nat) : Prop :=
mkOK_result {
  Σ_after : store_context;
  ok_env_sub : sub_vector (environment after) (environment before);
  ok_after : OK_state steps (filter_vec is_many Γ) Σ_after after;
  ok_value : ty_mem A steps (smemory after) m v
}.

Notation "' pat <-* c1 ;; c2" :=
  (@bindPC _ c1 (fun pat => c2%type))
  (at level 61, pat pattern, c1 at next level, right associativity) : type_scope.


Definition OK_term {vars} (steps : nat) (Γ : context vars) (e : @term vars) (m : mode) (A : type) :=
  forall
    (Σ : store_context)
    (s : machine_state vars)
    (Σ_s_ok : OK_state steps Γ Σ s),
    ('(s', v) <-* eval s e ;;
    OK_result Γ A s s' m v) steps.
(*
    '(s', v) <-* eval s e ;;
    OK_result steps Γ A s s' m v.
*)

Lemma VAR {vars steps}
  (Γ : context vars)
  (m : mode)
  (v : vref vars)
  (A : type) :
  vlookup Γ v = Some (m , A) ->
  OK_term steps Γ (var (linearity m) v) m A.
Proof.
  intros H_Γv Σ [env mem] H_Σs.
  assert (Hv := ok_env _ _ _ _ H_Σs v). rewrite H_Γv in Hv.
  unfold bindPC. rewrite interp_spec at 1; unfold interp'; cbn.
  destruct (vlookup env v) as [ val | ]; [ cbn | easy ].
  remember (linearity m) as lin; destruct lin; cbn;
    exists Σ.
Admitted.


Inductive PROD_mem (A B : type) steps mem mode : value -> Prop :=
| prod_mem {a b} : A steps mem mode a -> B steps mem mode b -> PROD_mem A B steps mem mode (v_pair a b).

Definition PROD (A B : type) : type.
  refine (mkType (PROD_mem A B) _).
  intros steps mem v mode [a b Ha Hb].
  constructor; auto using ty_decreasing.
Defined.

Lemma bindPC_step {n} : forall {A : Type}
  {e1 : now_or_later A}
  {P : A -> iProp},
  bindPC e1 P (S n)
  =
  match e1 with
  | ret _ x => P x (S n)
  | c_wrong _ => False
  | bindC _ x f =>
    ('x <-* x ;;
     'r <-* f x ;;
     P r)%type n
  end.
Proof.
  intros.
  unfold bindPC.
  destruct e1; cbn; try easy.
  rewrite interp_spec; cbn. rewrite bindP_assoc.
  apply bindP_exten; try easy.
  intros [a steps].
  rewrite bindP_assoc.
  apply bindP_exten; try easy.
  intros [r steps'].
  cbn.
  easy.
Qed.

Lemma PAIR {vars steps}
  (Γ : context vars)
  (m : mode)
  (A B : type)
  (a b : @term vars) :
  OK_term steps Γ a m A ->
  OK_term steps Γ b m B ->
  OK_term steps Γ (pair a b) m (PROD A B).
Proof.
  intros Ha Hb Σ [env mem] H_Σs.
  destruct steps as [ | steps ]; [ easy | ].
  specialize (Ha Σ (env , mem) H_Σs).

  rewrite bindPC_step; cbn.
  destruct steps as [ | steps ]


 unfold bindPC.
  rewrite interp_spec at 1; unfold interp'; cbn.
  d


  destruct steps as [ | steps ]; [ easy | ].
  cbn.
  rewrite bindP_assoc.
  specialize (Ha Σ (env , mem) H_Σs).
  apply (bindP_antimonotone_left eval_monotone) in Ha.
  apply (bindP_monotone Ha).
  intros [[env' mem'] va] [Σ' OK_va].
  rewrite bindP_assoc.
  specialize (Hb Σ' (env' , mem')).

Admitted.

Lemma UNPAIR {vars steps}
  (Γ : context vars)
  (m n : mode)
  (A B R : type)
  (ab : @term vars)
  (body : @term (S (S vars))) :
  OK_term steps Γ ab m (PROD A B) ->
  OK_term steps (vcons _ (vcons _ Γ (Some (m , A))) (Some (m , B))) body n R ->
  OK_term steps Γ (unpair ab body) n R.
Proof.
  intros Hab Hbody Σ [env mem] H_Σs.
  destruct steps as [ | steps]; [ easy | ].
  cbn.
  rewrite bindP_assoc.
  specialize (Hab Σ (env , mem) H_Σs).
  apply (bindP_antimonotone_left eval_monotone) in Hab.
  apply (bindP_monotone Hab).
  intros [[env' mem'] vab] [Σ' OK_vab_sub OK_vab_after [va vb H_A_va H_B_vb]].
  rewrite bindP_assoc.
  cbn.
  specialize (Hbody Σ').
  replace (S steps) with steps in Hbody by admit.
  eapply bindP_monotone. 

apply Hbody.

  apply Hbody.
