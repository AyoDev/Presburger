module Formula where

import Term
import Prettyprinter
--import Data.Hashable
--import Data.Text (Text, pack as pack', cons)
pack = pretty

data Atomic = LE Term Term | Div Integer Term deriving Eq

data Formula = Atom Atomic | Top | Bot | Not Formula | And Formula Formula | Or Formula Formula | Exists Variable Formula | Forall Variable Formula deriving (Eq)

type Vector = [Variable]
-----------------------------
----helpers

bigAND f xs = foldr (\x y -> And y ( f x )) (Top) xs
bigOR  f xs = foldr (\x y -> Or  y ( f x )) (Bot) xs


di x y= Atom $ Div x y

abs_ :: (Term -> Formula) -> Term -> Formula
abs_ f x = ((x `geq` 0) `implies` f x) `And` ((x `le` 0) `implies` f (-x) )

le x y = Atom $ x  `LE` y
ge = flip le
leq x y = Atom $ LE x (y+1)
geq = flip leq
eq x y = (x `leq` y) `And` (x `geq` y)
neq x y = Not $ eq x y

implies x y = Not x `Or` y

bool :: Bool -> Formula
bool True  = Top
bool False = Bot
------------------------------
-- induct over Terms in a formula
induct :: (Atomic -> x) -> (x -> x -> x) -> x -> Formula -> x
induct f (g) z (Or x y) = induct f g z x `g` induct f g z y
induct f (g) z (And x y) = induct f g z x `g` induct f g z y
induct f (g) z (Exists _ x) = induct f g z x
induct f (g) z (Forall _ x) = induct f g z x
induct f (g) z (Not x) = induct f g z x
induct f (g) z (Atom x) = f x
induct f (g) z c = z

--transform atoms inductive ly
transform :: (Atomic -> Formula) ->  Formula -> Formula
transform f (Or x y) = (transform f x) `Or` (transform f y)
transform f (And x y) = (transform f x) `And` (transform f y)
transform f (Exists v x) = Exists v $ transform f x
transform f (Forall v x) = Forall v $ transform f x
transform f (Not x) = Not $ transform f x
transform f (Atom x) = f x
transform f c = c

transform' f = transform (Atom . f)
----helpers------------------
map_ f (LE t1 t2) = f (t1 - t2)
map_ f (Div _ a) = f a
induct' f = induct (map_ f) 
variables = induct' vars (++) []
atoms = induct (:[]) (++) []

check_some f = induct f (||) False
check_all  f = induct f (&&) True

atomise f (LE x y) = LE (f x) (f y)
atomise f (Div q t) = Div q (f t)

is_in :: Variable -> Formula -> Bool
is_in x phi = induct' ((elem x) . vars) (||) False phi

is_exp_in :: Variable -> Formula -> Bool
is_exp_in x phi = induct' ((elem x) . evars) (||) False phi

is_exp_in' x = ((elem x) . evars)

linear_in :: Variable -> Formula -> Bool
linear_in x phi = x `is_in` phi &&  not (x `is_exp_in` phi)

powcmp (LE a b) = is_2_evar (a-b) || is_evar_const (a-b) 
powcmp (Div a b) = constant b `elem` [0..a] && length (evars b) == 1 && length (vars b) ==0
------------
divides x y = if y==0 then True else
	      if x == 0 then False else
	      y `rem` x == 0

-- replaces trivial atoms with T or Bot
simple w@(LE a b) = if is_const (a - b) then bool (constant (a - b) < 0) else Atom (LE (a-b) 0)
simple (Div 1 t) = Top
simple (Div q 0) = Top
simple w@(Div q t) = if is_const t then bool ( q `divides` constant t) else Atom w

simplify f = simple' $ transform simple f
--svIntvl (LE a b) (LE c d) = case split_term (a-b) of(x,t)-> if is_const t then 

simpleOR (Or Bot f) = f
simpleOR (Or f Bot) = f
simpleOR (Or Top _) = Top
simpleOR (Or _ Top) = Top
---simpleOR (Or (Atom x) (Atom y)) = svIntvl x y
simpleOR x =x

simpleAND (And Bot f) = Bot
simpleAND (And f Bot) = Bot
simpleAND (And Top f) = f
simpleAND (And f Top) = f
simpleAND x =x

simpleNOT (Not Top) = Bot
simpleNOT (Not Bot) = Top
simpleNOT x = x

simpleEX (Exists x Top) = Top
simpleEX (Exists x Bot) = Bot
simpleEX x =x

simpleALL (Forall x Top) = Top
simpleALL (Forall x Bot) = Bot
simpleALL x =x

simple' (Or f g) = simpleOR $ Or (simple' f) (simple' g)
simple' (And f g) = simpleAND $ And (simple' f) (simple' g)
simple' (Not f) =simpleNOT $ Not $ simple' f 
simple' (Exists x f) = simpleEX $ Exists x (simple' f)
simple' (Forall x f) = simpleALL$ Forall x (simple' f)

simple' Top = Top
simple' Bot = Bot
simple' (Atom a) = simple a
----------- ✨pretty✨-------
instance Show Atomic where show = show . pretty
instance Pretty Atomic where
 pretty (Div a t)  = pretty a <+> pretty '|' <+> pretty t
 pretty (LE t1 t2) = pretty t1 <+> pretty '<' <+> pretty t2

lbr = pretty '('
rbr = pretty ')'

instance Show Formula where show = show . pretty
instance Pretty Formula where
 pretty (Or x y) = lbr <>pretty x<>rbr <+> pack "or" <+>lbr<> (pretty y)<>rbr
 pretty (And x y) =lbr<> pretty x <+> pack "and" <+>(pretty y)<>rbr
 pretty (Exists v x) = pretty '∃' <> pretty (v_n v) <+> pretty x
 pretty (Forall v x) = pretty '∀' <>pretty (v_n v) <+> pretty x
 pretty (Not x) = pretty "¬(" <> pretty x <> pretty ')'
 pretty (Atom x) = pretty x
 pretty Top = pretty 'T'
 pretty Bot = pretty '⊥'

