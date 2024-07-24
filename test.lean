inductive Nat1 where
 | Z : Nat1
 | S : Nat1 → Nat1

@[simp]
def plus (a b : Nat1) : Nat1 :=
  match a, b with
  | Nat1.Z, b => b
  | Nat1.S a, b => Nat1.S (plus a b)

@[simp]
theorem plus_n (n : Nat1) : plus Nat1.Z n = n := 
 by 
 cases n; simp[plus];
 simp[plus]

@[simp]
theorem plus_Z (a : Nat1) : plus a Nat1.Z = a :=
by cases a; simp[plus]; simp[plus]; apply plus_Z

@[simp]
theorem nat1_cong (a b : Nat1) (h: a = b) : Nat1.S a = Nat1.S b :=  by simp[h]

@[simp]
theorem cong_nat1 (a b : Nat1) (h: Nat1.S a = Nat1.S b) : a = b := by cases h; rfl

@[simp]
theorem plus_assoc (a b c : Nat1) : plus (plus a b) c = plus a (plus b c) :=
 by
 cases a; simp[plus]; simp[plus]
 apply plus_assoc               --this is the induction hypothesis

@[simp]
theorem succ_plus : ∀ a b: Nat1, plus a (Nat1.S b) = Nat1.S (plus a b) :=
  by
  intros a b;
  induction a;
  case Z => simp[plus]
  case S ih => simp[plus]; exact ih;

@[simp]
theorem plus_comm : ∀ a b : Nat1, (plus a b) = (plus b a) :=
  by
  intros a b;
  cases a; simp[plus];
  simp[plus];
  apply plus_comm

@[simp]
theorem plus_cancel : ∀ (a b c : Nat1), (plus a b) = (plus a c) → b = c :=
  by
  intro a b c p;
  induction a;
  case _ => cases p; rfl;
  case _ a ih => simp [-plus_comm] at p; apply ih; assumption

-- Just an example of propositional proof
theorem orr_comm: ∀ (a b : Prop), a ∨ b → b ∨ a := 
  by
  intros a b h;
  cases h;
  case inl h => right; exact h;
  case inr h => left; exact h;

theorem ex1: ∀ (a b c: Prop) (_: a), (a → b) → (b → c) → c :=
  by
  intros _ _ _ j h g;
  exact g (h j);

theorem ex2: ∀ (a b: Prop), (a ∧ b) → (a ∨ b) :=
  by
  intros _ _ h;
  cases h with
  | intro u j => left; exact u;

theorem ex3: ∀ (p q r: Prop), p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  by
  intros p q r;
  constructor;
  {
   intro h;
   cases h.right
   case mp.inl y => left; constructor; exact h.left; exact y; 
   case mp.inr y => right; constructor; exact h.left; exact y;
  }
  {
    intros a; constructor; cases a
    case left.inl t => obtain ⟨lr, _⟩ := t; exact lr;
    case left.inr t => obtain ⟨lr, _⟩ := t; exact lr;
    case right => cases a
                  case inl j => left; obtain ⟨_, rr⟩ := j; exact rr;
                  case inr j => right; obtain ⟨_, rr⟩ := j; exact rr;}


-- These are example of extensional and intensional equality rewrites!
example : ∀ (a b: Prop), (a = b) → (a ↔ b) := by intros _ _ a; rw[a]
example : ∀ (a b : Prop), (a ↔ b) → (a = b) := by intros _ _ h; rw[h];

-- What is an even number in relations?
inductive Even : Nat → Prop where
  | EZ : Even 0
  | EN : (n : Nat) → (p : Even n) → Even (Nat.succ (Nat.succ n))

-- What is an odd number?
inductive Odd : Nat → Prop where
  | O1: Odd 1
  | ON: (n: Nat) → (p : Odd n) → Odd (Nat.succ (Nat.succ n))

-- Addition of two evens is even?
@[simp]
theorem even_plus_even_is_even : ∀ (a b: Nat), Even a → Even b → (Even (a + b)) :=
  by
  intros a b p1 p2;
  cases p1 with
  | EZ => simp[*]
  | EN a p1 => simp[*]; rw[Nat.add_comm, Nat.add_assoc, <- Nat.add_assoc]; simp;
               apply Even.EN; rw[Nat.add_comm]; apply even_plus_even_is_even a b p1 p2

-- Addition of 1 to odd gives an even number
@[simp]
theorem even_plus_1_is_odd : ∀ (a: Nat), (Even a) → (Odd (1 + a)) :=
  by
  intro a p;
  cases p;
  case EZ => simp; apply Odd.O1;
  case EN b h => simp; apply Odd.ON; apply even_plus_1_is_odd b h

-- Addition of 1 to even is an odd number
@[simp]
theorem odd_plus_1_is_even : ∀ (a : Nat), (Odd a) → (Even (a + 1)) :=
  by
  intro a p;
  cases p;
  case O1 => simp; apply Even.EN; apply Even.EZ;
  case ON a p => simp; apply Even.EN; apply odd_plus_1_is_even a p

-- Addition of two odds is even
@[simp]
theorem odd_plus_odd_is_even : ∀ (a b : Nat), (Odd a) → Odd b → Even (a + b) :=
  by
  intros a b p1 p2;
  cases p2;
  case O1 => apply odd_plus_1_is_even; assumption;
  case ON b p2 => simp; apply Even.EN; simp; apply odd_plus_odd_is_even a b p1 p2

-- Addition of even and odd is odd
@[simp]
theorem odd_plus_even_is_odd : ∀ (a b : Nat), (Odd a) → (Even b) → Odd (a + b) :=
  by
  intro a b p1 p2;
  cases p1;
  case O1 => apply even_plus_1_is_odd b p2;
  case ON a p1 => simp;
                  rw[Nat.add_assoc, Nat.add_assoc, Nat.add_comm, <- Nat.add_assoc];
                  simp;
                  have e2 := Even.EN 0 (Even.EZ);
                  have y := even_plus_even_is_even 2 b e2 p2;
                  rw[Nat.add_comm];
                  apply odd_plus_even_is_odd; exact p1; exact y;

-- Leq
inductive Leq : Nat → Nat → Prop where
  | zleqn : (n: Nat) → Leq 0 n
  | nleqm : (n m : Nat) → (p : Leq n m) → Leq (Nat.succ n) (Nat.succ m)

-- Geq
inductive Geq : Nat → Nat → Prop where
  | geq : (n m : Nat) → (Leq n m) → Geq m n

@[simp]
theorem Leq_refl : ∀ (a : Nat), Leq a a :=
  by
  intro a;
  induction a;
  case zero => constructor;
  case succ a => constructor; assumption;

@[simp]
theorem Leq_succ_0_false : ∀ (m: Nat), Leq (Nat.succ m) 0 → False :=
  by
  intro m p;
  cases p

@[simp]
theorem Leq1 : ∀ (m n : Nat), (Leq m n) → Leq m (Nat.succ n) :=
  by
  intro m n p;
  cases p;
  {constructor}
  case nleqm m n p => simp; constructor; apply Leq1; exact p;

theorem Leq2: ∀(m n: Nat), Leq (Nat.succ m) n → Leq m n :=
  by
  intro m n p;
  cases p;
  case nleqm n p => simp; apply Leq1; exact p;

@[simp]
theorem Leq_trans : ∀(m n p: Nat), (Leq m n) → (Leq n p) → (Leq m p) :=
  by
  intro m n p h1 h2;
  cases h1;
  {constructor}
  case nleqm m n h1 =>
  cases h2;
  case nleqm p h2 => simp; constructor; apply Leq_trans m n p h1 h2;

@[simp]
theorem Leq_antisym (a b : Nat) (p1: Leq a b) (p2: Leq b a) : a = b :=
  by
  cases p1;
  cases p2;
  {rfl}
  case nleqm a b p => 
  simp; simp at p2;
  cases p2;
  apply Leq_antisym; assumption; assumption

@[simp]
theorem Leq_eq_leq (a b: Nat) (p: a = b) : (Leq a b) ∧ (Leq b a) :=
  by cases p; simp;

-- This the strict order <
inductive Lt : Nat → Nat → Prop where
  | ltz : (n : Nat) → Lt 0 n.succ
  | ltnm : (n m : Nat) → (Lt n m) → Lt (n + 1) (m + 1)

-- irreflexivity of Lt
@[simp]
theorem Lt_irreflexive : ∀ (a : Nat), ¬ (Lt a a) :=
  by
  intro a h;
  induction a;
  cases h; 
  case succ =>
  cases h;
  case ltnm a p h => apply p; assumption

@[simp]
theorem Lt_succ : ∀ (a b : Nat), (Lt a b) → Lt a (b + 1) :=
  by
  intro a b p;
  cases p;
    case _ a => constructor;
  case _ a b p => constructor; apply Lt_succ;  assumption;


@[simp]
theorem Lt_assymetry : ∀ (a b : Nat), (Lt a b) → ¬ (Lt b a) :=
  by
  intro a b p h;
  induction a;
  case _ => cases h;
  case _ a ih => 
    apply ih;
    case _ => 
      cases p;
      case _ b p => apply Lt_succ; assumption
    case _ => 
      clear ih;
      cases p; cases h;
      case _ b p h => exfalso; apply Lt_assymetry a b p h;

@[simp]
theorem Lt_trans: ∀ (a b c : Nat), (Lt a b) → (Lt b c) → (Lt a c) :=
  by
  intro a b c p1 p2;
  cases p1; cases p2;
  case _ a p1 c => 
    constructor;
  case _ a b p1 =>
    have h := Lt_succ a b p1;
    have g := Lt_trans a (b+1) c h p2;
    cases c; cases g;
    case _ c => constructor; cases p2; apply Lt_trans a b c p1; assumption

-- This is the definition of greater than
inductive Gt : Nat → Nat → Prop where
  | gt : (n m : Nat) → (Lt n m) → Gt m n

@[simp]
theorem Gt_trans : ∀ (a b c : Nat), Gt a b → Gt b c → Gt a c :=
  by
  intro a b c p1 p2;
  constructor; cases p1; cases p2; apply Lt_trans c b a; assumption; assumption;

@[simp]
theorem Gt_asymmetry : ∀ (a b : Nat), Gt a b → ¬ (Gt b a) :=
  by
  intro a b p h;
  cases p; cases h; apply Lt_assymetry b a; assumption; assumption

@[simp]
theorem Gt_irrreflexive (a: Nat) (_: Gt a a) : ¬ (Gt a a) :=
  by
  intro h;
  cases h; apply Lt_irreflexive a; assumption

@[simp]
theorem Geq_trans : ∀ (a b c: Nat), Geq a b → Geq b c → Geq a c :=
  by
  intro a b c p1 p2;
  cases p1; cases p2;
  constructor; apply Leq_trans c b a; assumption; assumption;

@[simp]
theorem Geq_antisym : ∀ (a b : Nat), Geq a b → Geq b a → a = b :=
  by
  intro a b p1 p2;
  cases p1; cases p2;
  apply Leq_antisym; assumption; assumption

@[simp]
theorem Geq_refl : ∀ (a: Nat), Geq a a := by intro a; constructor; apply Leq_refl

example : ∀ (P Q: Prop), ¬(P ∨ Q) → ((¬ P) ∧ (¬ Q)) :=
  by
  intro P Q j;
  simp at j; assumption;

example : ∀ (P Q: Prop), (¬ P ∧ ¬ Q) → ¬ (P ∨ Q) :=
  by
  intro P Q j h;
  obtain ⟨lr, rr⟩ := j;
  cases h; contradiction; contradiction

theorem ex_l_congr : ∀ (A: Type), ∀ (m n : List A), ∀ (h: A), m = n → h :: m = h :: n :=
  by
  intro A m n h p;
  cases p; rfl

example : ∀ {A: Type}, (l : List A) → l ++ [] = l :=
  by 
  intro A l;
  induction l; simp
  case cons h l ih =>
    apply ex_l_congr; assumption

example : ∀ {A: Type}, ∀ (m n: List A), (m ++ n).length = m.length + n.length :=
  by
  intro A m n;
  induction m;
  case nil => simp
  case cons h m _ => simp; rw[Nat.add_right_comm]

-- The syntax of a simple language

inductive Term (A : Type) where
  | C : (n: A) → Term A      --A constant of type A
  | Plus : (n1 n2: Term A) → Term A  -- A plus operator on type A
  | Mult : (n1 n2: Term A) → Term A -- A minus operator on type A
  deriving Repr

-- Now we define a evaluation function on these terms
@[simp]
def compute (t : Term Nat): Nat :=
  match t with
  | Term.C (n) => n
  | Term.Plus n1 n2 => (compute n1) + (compute n2)
  | Term.Mult n1 n2 => (compute n1) * (compute n2)

-- Now the same thing as above but with const propagation
@[simp]
def compute' (t: Term Nat) : Nat :=
  match t with
  | Term.C (n) => n
  | Term.Plus n1 n2 =>
    match n1, n2 with
    | Term.C l, Term.C r => l + r
    | l, r => compute' l + compute' r
  | Term.Mult n1 n2 => 
    match n1, n2 with
    | Term.C l, Term.C r => l * r
    | l,r => compute' l * compute' r

theorem compute'_plus_compute' : ∀ (a b : Term Nat), 
  compute' a + compute' b = compute' (a.Plus b)
:= by
   intro a b;
   induction a <;> simp
   case _ a =>
     cases b <;> simp


theorem compute'_mult_compute' : ∀ (a b : Term Nat), 
  compute' a * compute' b = compute' (a.Mult b)
:= by
   intro a b;
   induction a <;> simp
   case _ a =>
     cases b <;> simp

theorem compute_eq_compute' : ∀ (a : Term Nat), compute a = compute' a :=
  by
  intro a;
  induction a <;> simp
  case _ a b j k => 
    rw[j, k, compute'_plus_compute'];
  case _ a b j k =>
    rw[j, k, compute'_mult_compute']

-- Another example showing that relations semantics of this very small
-- language is the same as the computation semantics

inductive Eval : Term Nat → Nat → Prop where
  | CEval : (n : Nat) → Eval (Term.C n) n
  | AddEval : (n1 n2: Term Nat) → (j k : Nat) → 
              (Eval n1 j) → (Eval n2 k) → Eval (Term.Plus n1 n2) (j + k)
  | MulEval : (n1 n2: Term Nat) → (j k : Nat) → Eval n1 j → 
              Eval n2 k → Eval (Term.Mult n1 n2) (j * k)

theorem rel_com : ∀ (b: Term Nat), ∀ (k: Nat), Eval b k → compute b = k :=
  by
  intro b k p;
  cases p; simp;
  simp;
  case _ n1 n2 j k p1 p2 =>
    have w := rel_com n1 j p1;
    have q := rel_com n2 k p2;
    rw[w, q];
  case _ n1 n2 j k p1 p2 => 
    simp;
    have w := rel_com n1 j p1;
    have q := rel_com n2 k p2;
    rw[w,q]

theorem com_rel : ∀ (b: Term Nat), ∀ (k: Nat), compute b = k → Eval b k :=
  by
  intro b k p;
  rw[<- p];
  cases b;
  simp <;> constructor; simp; constructor; apply com_rel; rfl;apply com_rel; rfl;
  simp; constructor; apply com_rel; rfl; apply com_rel; rfl

theorem rel_iff_com : ∀ (b: Term Nat), ∀ (k: Nat), compute b = k ↔ Eval b k :=
  by
  intro b k;
  constructor; apply com_rel; apply rel_com

theorem rel_add_eq_com : ∀ (b : Term Nat), ∀(n m : Nat), (Eval b n) → compute b = m → n = m :=
  by
  intro b n m r c;
  have p1 := rel_com b n r
  rw[<- p1, c]

-- Now we do a compilation proof
inductive Slang (A:Type): Type where    -- these are just bytecode
  | Push : A → Slang A
  | Add  : Slang A
  | Mult : Slang A
  deriving Repr

-- Now the semantics of Slang as relations
inductive SEval : List Nat → (Slang Nat) → List Nat → Prop where
  | EvalPush : ∀(n: Nat), ∀ (s : List Nat), SEval s (Slang.Push n) (n :: s)
    -- this means that the stack will keep on growing.
  | EvalAdd : ∀(n1 n2 : Nat), ∀ (s : List Nat), 
              SEval (n1 :: n2 :: s) Slang.Add ((n1 + n2) :: n1 :: n2 :: s) 
  | EvalMult : ∀(n1 n2 : Nat), ∀ (s : List Nat), 
              SEval (n1 :: n2 :: s) Slang.Mult ((n1 * n2) :: n1 :: n2 :: s)

-- The semantics as a computational function
@[simp]
def CSEval (i: Slang Nat) (s : List Nat) (_ : 2 ≤ s.length): List Nat :=
  by cases i;
     case Push x => exact x :: s
     case Add =>
       match s with
       | x :: y :: s => exact (x + y) :: x :: y :: s -- this means that
                                                     -- stack keeps on
                                                     -- growing
     case Mult => 
       match s with
       | x :: y :: s => exact (x * y) :: x :: y :: s

@[simp]
theorem SEval_to_CSEval : ∀ (s s' : List Nat), ∀ (i: Slang Nat), 
                         SEval s i s' → (p : 2 ≤ s.length)
                         → CSEval i s p = s' := by intro s s' i p; cases p<;> simp


-- This is the equivalence theorem
@[simp]
theorem SEval_eq_CSEval : ∀ (s s' s'' : List Nat), ∀ (i: Slang Nat), 
                          (p: 2 ≤ s.length) → CSEval i s p = s'
                          → SEval s i s'' → s' = s'' :=
  by
  intro s s' s'' i p h1 h2;
  have y := SEval_to_CSEval s s'' i h2 p;
  rw[<- y, h1]


@[simp]
theorem CEval_to_SEval : ∀ (s s' : List Nat), ∀ (i : Slang Nat), 
                         (p: 2 ≤ s.length) → CSEval i s p = s' 
                          → SEval s i s' :=
  by
  intro s s' i p' p;
  cases i; rw[<- p]; simp; constructor
  case Add => rw[<- p]; simp;
              match s with
              | x :: y :: s => simp; constructor
  case Mult => rw[<-p]; simp;
               match s with
               | x :: y :: s => simp; constructor

@[simp]
theorem CSEval_len : ∀ (i : Slang Nat), ∀ (s : List Nat), (p: 2 ≤ s.length)
                     → 2 ≤ (CSEval i s p).length :=
by 
  intro i s p;
  cases i; simp; apply Nat.le_of_succ_le p
  case Add => 
    simp;
    match s with
    | _ :: _ :: s => simp;
  case _ =>
    simp;
    match s with
    | _ :: _ :: s => simp;

-- This is the evaluator for the whole program memory
@[simp]
def PEval (stack: List Nat) (p: 2 ≤ stack.length) (pm: List (Slang Nat)): List Nat :=
  match pm with
  | x :: s => CSEval x (PEval stack p s) (by sorry)
  | [] => stack

@[simp]
def PSEval (pm: List (Slang Nat)) : List Nat :=
  let h := [0, 0];
  PEval h (by constructor) pm

-- The compiler from higher level language to stack language
@[simp]
def compile_term_slang (pm: List (Slang Nat)) (t: Term Nat) : List (Slang Nat) :=
  match t with
  | Term.C l => (Slang.Push l) :: pm
  | Term.Plus x y => Slang.Add :: compile_term_slang (compile_term_slang pm x) y
              -- compile_term_slang pm x ++ compile_term_slang pm y ++ [Slang.Add]
  | Term.Mult x y => Slang.Mult :: compile_term_slang (compile_term_slang pm x) y
                --compile_term_slang pm x ++ compile_term_slang pm y ++ [Slang.Mult]

theorem Eval_eq_SEval': ∀ (t: Term Nat), ∀ (n: Nat), ∀ (s s': List Nat), 
        ∀ (pm: List (Slang Nat)),
        (s = [0, 0]) → compute t = n → (PSEval (compile_term_slang pm t) = s') →
        (q: 2 ≤ s'.length) → s'.head 
        (by apply List.ne_nil_of_length_pos; exact Nat.zero_lt_of_lt q ) = n
        :=
by
  intro t n s s' pm o p3 q k;
  cases p3;
  cases t; 
  case _ n => match s' with
              | x::s' => simp; simp at q; rw[q.left]
  case _ n1 n2 => match s' with
                  | x :: s' => simp; simp only [PSEval, CSEval] at q; sorry
  case _ n1 n2 => match s' with
                  | x :: s' => simp; simp at q;sorry
  

-- Now we are ready to prove some properties about this compiler
theorem Eval_eq_SEval : ∀ (t: Term Nat), ∀ (n m: Nat), ∀ (s: List Nat), 
        ∀(pm: List (Slang Nat)), s = [0,0] →
        compute t = n → (PSEval (compile_term_slang pm t) = m :: s)
        → n = m :=
  by
  sorry
