module Sf_imp where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

data Nat =
   O
 | S Nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x y -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) x y -> y}

length :: ([] a1) -> Nat
length l =
  case l of {
   [] -> O;
   (:) y l' -> S (length l')}

data Comparison =
   Eq
 | Lt
 | Gt

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type x y c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

nat_iter :: Nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x =
  case n of {
   O -> x;
   S n' -> f (nat_iter n' f x)}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

existsb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
existsb f l =
  case l of {
   [] -> Prelude.False;
   (:) a l0 -> orb (f a) (existsb f l0)}

forallb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
forallb f l =
  case l of {
   [] -> Prelude.True;
   (:) a l0 -> andb (f a) (forallb f l0)}

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

n_rect :: a1 -> (Positive -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Positive -> a1) -> N -> a1
n_rec =
  n_rect

type T = Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred :: Positive -> Positive
pred x =
  case x of {
   XI p -> XO p;
   XO p -> pred_double p;
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

mask_rect :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    case q of {
     XH -> IsNul;
     _ -> IsPos (pred q)};
   _ -> IsNeg}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: Positive -> (a1 -> a1) -> a1 -> a1
iter n f x =
  case n of {
   XI n' -> f (iter n' f (iter n' f x));
   XO n' -> iter n' f (iter n' f x);
   XH -> f x}

pow :: Positive -> Positive -> Positive
pow x y =
  iter y (mul x) XH

square :: Positive -> Positive
square p =
  case p of {
   XI p0 -> XI (XO (add (square p0) p0));
   XO p0 -> XO (XO (square p0));
   XH -> XH}

div2 :: Positive -> Positive
div2 p =
  case p of {
   XI p0 -> p0;
   XO p0 -> p0;
   XH -> XH}

div2_up :: Positive -> Positive
div2_up p =
  case p of {
   XI p0 -> succ p0;
   XO p0 -> p0;
   XH -> XH}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

size :: Positive -> Positive
size p =
  case p of {
   XI p0 -> succ (size p0);
   XO p0 -> succ (size p0);
   XH -> XH}

compare_cont :: Positive -> Positive -> Comparison -> Comparison
compare_cont x y r =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont p q r;
     XO q -> compare_cont p q Gt;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont p q Lt;
     XO q -> compare_cont p q r;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare x y =
  compare_cont x y Eq

min :: Positive -> Positive -> Positive
min p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max :: Positive -> Positive -> Positive
max p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb :: Positive -> Positive -> Prelude.Bool
eqb p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> eqb p0 q0;
     _ -> Prelude.False};
   XO p0 ->
    case q of {
     XO q0 -> eqb p0 q0;
     _ -> Prelude.False};
   XH ->
    case q of {
     XH -> Prelude.True;
     _ -> Prelude.False}}

leb :: Positive -> Positive -> Prelude.Bool
leb x y =
  case compare x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Positive -> Positive -> Prelude.Bool
ltb x y =
  case compare x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> ((,)
                Positive Mask) -> (,) Positive Mask
sqrtrem_step f g p =
  case p of {
   (,) s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       Prelude.True -> (,) (XI s) (sub_mask r' s');
       Prelude.False -> (,) (XO s) (IsPos r')};
     _ -> (,) (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> (,) Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p1);
     XH -> (,) XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p1);
     XH -> (,) XH (IsPos XH)};
   XH -> (,) XH IsNul}

sqrt :: Positive -> Positive
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Positive -> Positive -> Positive
gcdn n a b =
  case n of {
   O -> XH;
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b};
       XO b0 -> gcdn n0 a b0;
       XH -> XH};
     XO a0 ->
      case b of {
       XI p -> gcdn n0 a0 b;
       XO b0 -> XO (gcdn n0 a0 b0);
       XH -> XH};
     XH -> XH}}

gcd :: Positive -> Positive -> Positive
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcdn n a b =
  case n of {
   O -> (,) XH ((,) a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa (XO bb))}};
       XH -> (,) XH ((,) a XH)};
     XO a0 ->
      case b of {
       XI p ->
        case ggcdn n0 a0 b of {
         (,) g p0 ->
          case p0 of {
           (,) aa bb -> (,) g ((,) (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         (,) g p -> (,) (XO g) p};
       XH -> (,) XH ((,) a XH)};
     XH -> (,) XH ((,) XH b)}}

ggcd :: Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XI (lor p0 q0);
     XH -> p};
   XO p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XO (lor p0 q0);
     XH -> XI p0};
   XH ->
    case q of {
     XO q0 -> XI q0;
     _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> nsucc_double (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> Npos XH};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> N0};
   XH ->
    case q of {
     XO q0 -> N0;
     _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> nsucc_double (ldiff p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> ndouble (ldiff p0 q0);
     XH -> Npos p};
   XH ->
    case q of {
     XO q0 -> Npos XH;
     _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (lxor p0 q0);
     XO q0 -> nsucc_double (lxor p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> nsucc_double (lxor p0 q0);
     XO q0 -> ndouble (lxor p0 q0);
     XH -> Npos (XI p0)};
   XH ->
    case q of {
     XI q0 -> Npos (XO q0);
     XO q0 -> Npos (XI q0);
     XH -> N0}}

shiftl_nat :: Positive -> Nat -> Positive
shiftl_nat p n =
  nat_iter n (\x -> XO x) p

shiftr_nat :: Positive -> Nat -> Positive
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x -> XO x) p}

shiftr :: Positive -> N -> Positive
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Positive -> Nat -> Prelude.Bool
testbit_nat p n =
  case p of {
   XI p0 ->
    case n of {
     O -> Prelude.True;
     S n' -> testbit_nat p0 n'};
   XO p0 ->
    case n of {
     O -> Prelude.False;
     S n' -> testbit_nat p0 n'};
   XH ->
    case n of {
     O -> Prelude.True;
     S n0 -> Prelude.False}}

testbit :: Positive -> N -> Prelude.Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> Prelude.True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> Prelude.False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH ->
    case n of {
     N0 -> Prelude.True;
     Npos p0 -> Prelude.False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op plus x (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x ->
    case x of {
     O -> XH;
     S n0 -> succ (of_nat x)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

eq_dec :: Positive -> Positive -> Prelude.Bool
eq_dec x y =
  positive_rec (\p h y0 ->
    case y0 of {
     XI p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0);
     _ -> Prelude.False}) (\p h y0 ->
    case y0 of {
     XO p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (h p0);
     _ -> Prelude.False}) (\y0 ->
    case y0 of {
     XH -> Prelude.True;
     _ -> Prelude.False}) x y

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x -> f (succ (XO p0)) (f (XO p0) x))} in
  case p of {
   XI q -> f (XO q) (f2 q);
   XO q -> f2 q;
   XH -> a}

peano_rec :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Positive PeanoView

peanoView_rect :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                  PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                 PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Positive -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc XH PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ (XO p0)) (PeanoSucc (XO p0)
    (peanoView_xO p0 q0))}

peanoView_xI :: Positive -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ XH) (PeanoSucc XH PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc (succ (XI p0)) (PeanoSucc (XI p0)
    (peanoView_xI p0 q0))}

peanoView :: Positive -> PeanoView
peanoView p =
  case p of {
   XI p0 -> peanoView_xI p0 (peanoView p0);
   XO p0 -> peanoView_xO p0 (peanoView p0);
   XH -> PeanoOne}

peanoView_iter :: a1 -> (Positive -> a1 -> a1) -> Positive -> PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Positive -> Positive -> Reflect
eqb_spec x y =
  iff_reflect (eqb x y)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x -> x}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos p0 -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Positive -> Positive -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Positive -> Positive -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Positive -> Positive -> Prelude.Bool
max_dec n m =
  max_case n m (\x y _ h0 -> h0) Prelude.True Prelude.False

min_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Positive -> Positive -> Prelude.Bool
min_dec n m =
  min_case n m (\x y _ h0 -> h0) Prelude.True Prelude.False

max_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Positive -> Positive -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Positive -> Positive -> Prelude.Bool
max_dec0 =
  max_dec

min_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Positive -> Positive -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Positive -> Positive -> Prelude.Bool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos XH

two :: N
two =
  Npos (XO XH)

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

succ0 :: N -> N
succ0 n =
  case n of {
   N0 -> Npos XH;
   Npos p -> Npos (succ p)}

pred0 :: N -> N
pred0 n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Positive
succ_pos n =
  case n of {
   N0 -> XH;
   Npos p -> succ p}

add0 :: N -> N -> N
add0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (add p q)}}

sub0 :: N -> N -> N
sub0 n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos (mul p q)}}

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Eq;
     Npos m' -> Lt};
   Npos n' ->
    case m of {
     N0 -> Gt;
     Npos m' -> compare n' m'}}

eqb0 :: N -> N -> Prelude.Bool
eqb0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Prelude.True;
     Npos p -> Prelude.False};
   Npos p ->
    case m of {
     N0 -> Prelude.False;
     Npos q -> eqb p q}}

leb0 :: N -> N -> Prelude.Bool
leb0 x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: N -> N -> Prelude.Bool
ltb0 x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

min0 :: N -> N -> N
min0 n n' =
  case compare0 n n' of {
   Gt -> n';
   _ -> n}

max0 :: N -> N -> N
max0 n n' =
  case compare0 n n' of {
   Gt -> n;
   _ -> n'}

div0 :: N -> N
div0 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos p;
     XO p -> Npos p;
     XH -> N0}}

even :: N -> Prelude.Bool
even n =
  case n of {
   N0 -> Prelude.True;
   Npos p ->
    case p of {
     XO p0 -> Prelude.True;
     _ -> Prelude.False}}

odd :: N -> Prelude.Bool
odd n =
  negb (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos XH;
   Npos p0 ->
    case n of {
     N0 -> N0;
     Npos q -> Npos (pow q p0)}}

square0 :: N -> N
square0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (square p)}

log2 :: N -> N
log2 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos (size p);
     XO p -> Npos (size p);
     XH -> N0}}

size0 :: N -> N
size0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (size p)}

size_nat0 :: N -> Nat
size_nat0 n =
  case n of {
   N0 -> O;
   Npos p -> size_nat p}

pos_div_eucl :: Positive -> N -> (,) N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}};
   XH ->
    case b of {
     N0 -> (,) N0 (Npos XH);
     Npos p ->
      case p of {
       XH -> (,) (Npos XH) N0;
       _ -> (,) N0 (Npos XH)}}}

div_eucl :: N -> N -> (,) N N
div_eucl a b =
  case a of {
   N0 -> (,) N0 N0;
   Npos na ->
    case b of {
     N0 -> (,) N0 a;
     Npos p -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  snd (div_eucl a b)

gcd0 :: N -> N -> N
gcd0 a b =
  case a of {
   N0 -> b;
   Npos p ->
    case b of {
     N0 -> a;
     Npos q -> Npos (gcd p q)}}

ggcd0 :: N -> N -> (,) N ((,) N N)
ggcd0 a b =
  case a of {
   N0 -> (,) b ((,) N0 (Npos XH));
   Npos p ->
    case b of {
     N0 -> (,) a ((,) (Npos XH) N0);
     Npos q ->
      case ggcd p q of {
       (,) g p0 ->
        case p0 of {
         (,) aa bb -> (,) (Npos g) ((,) (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> (,) N N
sqrtrem0 n =
  case n of {
   N0 -> (,) N0 N0;
   Npos p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) (Npos s) (Npos r);
       _ -> (,) (Npos s) N0}}}

sqrt0 :: N -> N
sqrt0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (sqrt p)}

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> lxor p q}}

shiftl_nat0 :: N -> Nat -> N
shiftl_nat0 a n =
  nat_iter n double a

shiftr_nat0 :: N -> Nat -> N
shiftr_nat0 a n =
  nat_iter n div0 a

shiftl0 :: N -> N -> N
shiftl0 a n =
  case a of {
   N0 -> N0;
   Npos a0 -> Npos (shiftl a0 n)}

shiftr0 :: N -> N -> N
shiftr0 a n =
  case n of {
   N0 -> a;
   Npos p -> iter p div0 a}

testbit_nat0 :: N -> Nat -> Prelude.Bool
testbit_nat0 a =
  case a of {
   N0 -> (\x -> Prelude.False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Prelude.Bool
testbit0 a n =
  case a of {
   N0 -> Prelude.False;
   Npos p -> testbit p n}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

of_nat0 :: Nat -> N
of_nat0 n =
  case n of {
   O -> N0;
   S n' -> Npos (of_succ_nat n')}

iter0 :: N -> (a1 -> a1) -> a1 -> a1
iter0 n f x =
  case n of {
   N0 -> x;
   Npos p -> iter p f x}

eq_dec0 :: N -> N -> Prelude.Bool
eq_dec0 n m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Prelude.True;
     Npos p -> Prelude.False}) (\p m0 ->
    case m0 of {
     N0 -> Prelude.False;
     Npos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Prelude.True p) (\_ -> Prelude.False)
        (eq_dec p p0)}) n m

discr :: N -> Prelude.Maybe Positive
discr n =
  case n of {
   N0 -> Prelude.Nothing;
   Npos p -> Prelude.Just p}

binary_rect :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rect f0 f2 fS2 n =
  let {f2' = \p -> f2 (Npos p)} in
  let {fS2' = \p -> fS2 (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> positive_rect fS2' f2' (fS2 N0 f0) p}

binary_rec :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> peano_rect (f N0 f0) f' p}

peano_rec0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rec0 =
  peano_rect0

leb_spec1 :: N -> N -> Reflect
leb_spec1 x y =
  iff_reflect (leb0 x y)

ltb_spec1 :: N -> N -> Reflect
ltb_spec1 x y =
  iff_reflect (ltb0 x y)

recursion :: a1 -> (N -> a1 -> a1) -> N -> a1
recursion =
  peano_rect0

sqrt_up :: N -> N
sqrt_up a =
  case compare0 N0 a of {
   Lt -> succ0 (sqrt0 (pred0 a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare0 (Npos XH) a of {
   Lt -> succ0 (log2 (pred0 a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb0 x y)

b2n :: Prelude.Bool -> N
b2n b =
  case b of {
   Prelude.True -> Npos XH;
   Prelude.False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos XH) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos XH) n)

ones :: N -> N
ones n =
  pred0 (shiftl0 (Npos XH) n)

lnot :: N -> N -> N
lnot a n =
  lxor0 a (ones n)

max_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n m x x0 x1 =
  max_case_strong1 n m x (\_ -> x0) (\_ -> x1)

max_dec1 :: N -> N -> Prelude.Bool
max_dec1 n m =
  max_case1 n m (\x y _ h0 -> h0) Prelude.True Prelude.False

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n m x x0 x1 =
  min_case_strong1 n m x (\_ -> x0) (\_ -> x1)

min_dec1 :: N -> N -> Prelude.Bool
min_dec1 n m =
  min_case1 n m (\x y _ h0 -> h0) Prelude.True Prelude.False

max_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong2 n m x x0 =
  max_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case2 :: N -> N -> a1 -> a1 -> a1
max_case2 n m x x0 =
  max_case_strong2 n m (\_ -> x) (\_ -> x0)

max_dec2 :: N -> N -> Prelude.Bool
max_dec2 =
  max_dec1

min_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong2 n m x x0 =
  min_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case2 :: N -> N -> a1 -> a1 -> a1
min_case2 n m x x0 =
  min_case_strong2 n m (\_ -> x) (\_ -> x0)

min_dec2 :: N -> N -> Prelude.Bool
min_dec2 =
  min_dec1

type RankSelection candidate = [] candidate

type Ballot candidate = [] (RankSelection candidate)

type RelDec t =
  t -> t -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_RelDec
  
rel_dec :: (RelDec a1) -> a1 -> a1 -> Prelude.Bool
rel_dec relDec =
  relDec

eq_dec1 :: (RelDec a1) -> a1 -> a1 -> Prelude.Bool
eq_dec1 eD =
  rel_dec eD

type Ballot0 candidate = Ballot candidate

type Record candidate = [] ([] candidate)

eliminated :: (RelDec a1) -> (Record a1) -> a1 -> Prelude.Bool
eliminated reldec_candidate rec cand =
  existsb (existsb (eq_dec1 reldec_candidate cand)) rec

next_ranking :: (RelDec a1) -> (Record a1) -> (Ballot0 a1) -> Prelude.Maybe
                ((,) a1 (Ballot0 a1))
next_ranking reldec_candidate rec bal =
  case bal of {
   [] -> Prelude.Nothing;
   (:) r t ->
    case r of {
     [] -> next_ranking reldec_candidate rec t;
     (:) h l ->
      case forallb (eq_dec1 reldec_candidate h) l of {
       Prelude.True ->
        case eliminated reldec_candidate rec h of {
         Prelude.True -> next_ranking reldec_candidate rec t;
         Prelude.False -> Prelude.Just ((,) h bal)};
       Prelude.False -> Prelude.Nothing}}}

drop_none :: ([] (Prelude.Maybe a1)) -> [] a1
drop_none l =
  case l of {
   [] -> [];
   (:) o t ->
    case o of {
     Prelude.Just x -> (:) x (drop_none t);
     Prelude.Nothing -> drop_none t}}

increment :: (RelDec a1) -> ([] ((,) a1 N)) -> a1 -> [] ((,) a1 N)
increment reldec_candidate r c =
  case r of {
   [] -> (:) ((,) c (Npos XH)) [];
   (:) p t ->
    case p of {
     (,) c1 n ->
      case eq_dec1 reldec_candidate c1 c of {
       Prelude.True -> (:) ((,) c1 (add0 n (Npos XH))) t;
       Prelude.False -> (:) ((,) c1 n) (increment reldec_candidate t c)}}}

tabulate'' :: (RelDec a1) -> ([] (Prelude.Maybe a1)) -> ([] ((,) a1 N)) -> []
              ((,) a1 N)
tabulate'' reldec_candidate rs lc =
  case rs of {
   [] -> lc;
   (:) o t ->
    case o of {
     Prelude.Just h ->
      tabulate'' reldec_candidate t (increment reldec_candidate lc h);
     Prelude.Nothing -> tabulate'' reldec_candidate t lc}}

tabulate' :: (RelDec a1) -> ([] (Prelude.Maybe a1)) -> [] ((,) a1 N)
tabulate' reldec_candidate rs =
  tabulate'' reldec_candidate rs []

cnle :: ((,) a1 N) -> ((,) a1 N) -> Prelude.Bool
cnle a b =
  case a of {
   (,) c n1 ->
    case b of {
     (,) c0 n2 -> leb0 n1 n2}}

insert :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> [] a1
insert cmp i l =
  case l of {
   [] -> (:) i [];
   (:) h t ->
    case cmp i h of {
     Prelude.True -> (:) i l;
     Prelude.False -> (:) h (insert cmp i t)}}

insertionsort' :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([] a1) -> [] a1
insertionsort' cmp l srtd =
  case l of {
   [] -> srtd;
   (:) h t -> insertionsort' cmp t (insert cmp h srtd)}

insertionsort :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> [] a1
insertionsort cmp l =
  insertionsort' cmp l []

type Election candidate = [] (Ballot0 candidate)

option_split :: ([] (Prelude.Maybe ((,) a1 a2))) -> (,)
                ([] (Prelude.Maybe a1)) ([] (Prelude.Maybe a2))
option_split l =
  case l of {
   [] -> (,) [] [];
   (:) o t ->
    case o of {
     Prelude.Just p ->
      case p of {
       (,) a b ->
        case option_split t of {
         (,) l1 l2 -> (,) ((:) (Prelude.Just a) l1) ((:) (Prelude.Just b) l2)}};
     Prelude.Nothing ->
      case option_split t of {
       (,) l1 l2 -> (,) ((:) Prelude.Nothing l1) ((:) Prelude.Nothing l2)}}}

tabulate :: (RelDec a1) -> (Record a1) -> (Election a1) -> (,)
            ([] ((,) a1 N)) (Election a1)
tabulate reldec_candidate rec elect =
  let {get_candidates = map (next_ranking reldec_candidate rec) elect} in
  case option_split get_candidates of {
   (,) next_ranks next_election ->
    let {counts = tabulate' reldec_candidate next_ranks} in
    let {sorted_ranks = insertionsort cnle counts} in
    (,) sorted_ranks (drop_none next_election)}

gtb_N :: N -> N -> Prelude.Bool
gtb_N a b =
  negb (leb0 a b)

get_bottom_votes :: ([] ((,) a1 N)) -> [] a1
get_bottom_votes votes =
  case votes of {
   [] -> [];
   (:) p t ->
    case p of {
     (,) c v ->
      map fst
        (filter (\x ->
          case x of {
           (,) x0 v' -> eqb0 v v'}) votes)}}

find_eliminated_noopt :: (([] a1) -> Prelude.Maybe a1) -> ([] ((,) a1 N)) ->
                         Prelude.Maybe ([] a1)
find_eliminated_noopt break_tie votes =
  case break_tie (get_bottom_votes votes) of {
   Prelude.Just c -> Prelude.Just ((:) c []);
   Prelude.Nothing -> Prelude.Nothing}

last_item :: ([] ((,) a1 N)) -> Prelude.Maybe ((,) a1 N)
last_item votes =
  case votes of {
   [] -> Prelude.Nothing;
   (:) h t ->
    case t of {
     [] -> Prelude.Just h;
     (:) y l -> last_item t}}

run_election' :: (RelDec a1) -> (([] a1) -> Prelude.Maybe a1) -> (Election
                 a1) -> (Record a1) -> Nat -> (,) (Prelude.Maybe a1)
                 (Record a1)
run_election' reldec_candidate break_tie elect rec fuel =
  case fuel of {
   O -> (,) Prelude.Nothing rec;
   S n' ->
    case tabulate reldec_candidate rec elect of {
     (,) ranks elect' ->
      let {win_threshhold = of_nat0 (length elect')} in
      case last_item ranks of {
       Prelude.Just p ->
        case p of {
         (,) cand1 cand1_votes ->
          case gtb_N (mul0 cand1_votes (Npos (XO XH))) win_threshhold of {
           Prelude.True -> (,) (Prelude.Just cand1) rec;
           Prelude.False ->
            case find_eliminated_noopt break_tie ranks of {
             Prelude.Just el ->
              run_election' reldec_candidate break_tie elect ((:) el rec) n';
             Prelude.Nothing -> (,) Prelude.Nothing rec}}};
       Prelude.Nothing -> (,) Prelude.Nothing rec}}}

find_0s :: (RelDec a1) -> ([] a1) -> (Election a1) -> [] a1
find_0s reldec_candidate all_candidates el =
  let {get_candidates = map (next_ranking reldec_candidate []) el} in
  case option_split get_candidates of {
   (,) next_ranks x ->
    let {initial = map (\x0 -> (,) x0 N0) all_candidates} in
    let {counts = tabulate'' reldec_candidate next_ranks initial} in
    map fst
      (filter (\x0 ->
        case x0 of {
         (,) x1 ct -> eqb0 ct N0}) counts)}

run_election :: (RelDec a1) -> (([] a1) -> Prelude.Maybe a1) -> ([]
                (Ballot0 a1)) -> ([] a1) -> (,) (Prelude.Maybe a1)
                (Record a1)
run_election reldec_candidate break_tie elect all_candidates =
  run_election' reldec_candidate break_tie elect ((:)
    (find_0s reldec_candidate all_candidates elect) []) (length elect)

type T1 = Prelude.Int

prop_drop_none_keeps :: ([] (Prelude.Maybe T1)) -> T1 -> Prelude.Bool
prop_drop_none_keeps l i =
  (Prelude.==) (existsb ((Prelude.==) (Prelude.Just i)) l)
    (existsb ((Prelude.==) i) (drop_none l))

prop_next_ranking_contains :: (Record T1) -> (Ballot0 T1) -> Prelude.Bool
prop_next_ranking_contains rec bal =
  case next_ranking (Prelude.==) rec bal of {
   Prelude.Just p ->
    case p of {
     (,) c b -> existsb (existsb ((Prelude.==) c)) bal};
   Prelude.Nothing -> Prelude.True}

prop_next_ranking_not_eliminated :: (Record T1) -> (Ballot0 T1) ->
                                    Prelude.Bool
prop_next_ranking_not_eliminated rec bal =
  case next_ranking (Prelude.==) rec bal of {
   Prelude.Just p ->
    case p of {
     (,) c b -> negb (eliminated (Prelude.==) rec c)};
   Prelude.Nothing -> Prelude.True}

all_props :: (,)
             ((,) (([] (Prelude.Maybe T1)) -> T1 -> Prelude.Bool)
             ((Record T1) -> (Ballot0 T1) -> Prelude.Bool))
             ((Record T1) -> (Ballot0 T1) -> Prelude.Bool)
all_props =
  (,) ((,) prop_drop_none_keeps prop_next_ranking_contains)
    prop_next_ranking_not_eliminated

