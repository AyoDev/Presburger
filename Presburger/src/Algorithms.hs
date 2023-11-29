{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE TupleSections #-}
module Algorithms where
-- first go at dmitry algorithm
import Data.List (uncons,delete,subsequences,(\\), nub)
--import Data.Stack
import qualified Data.Map as Map
import Term
import Formula
import Data.Maybe
-----------------------
fst3 (a,_,_) = a
snd3 (_,a,_) = a
thd3 (_,_,a) = a
mapFst f (a ,b) = (f a,b)
---------------------------
type Quantifier = (Char, Variable)
data Prefix = Prefix {negated ::Bool, string :: [Quantifier],block ::Vector, formula :: Formula} deriving (Eq,Show)
type Prefix' = (Prefix,Naming)
empty_p = (Prefix False [] [] $ Exists 0 Bot,Map.empty)
pre_cons x p = p {string = x:string p}
flip_q (Prefix b q v phi) = Prefix (not b) (map neg q) v (Not phi)
shift_bv p@(Prefix b q v phi)| q' == 'E' = shift_bv $ p {string = init q, block =x:v }
                             | otherwise = p
          where (q', x) = case uncons $ reverse q of Just ((l,w),b) -> (l,w); Nothing -> ('?',-1)
max_bv p@(Prefix b q v phi) = if length (block w2) > length (block w1) then w2 else w1 where w1 =shift_bv p; w2=shift_bv $ flip_q p
neg :: Quantifier -> Quantifier
neg ('E',x) = ('A',x)
neg ('A',x) = ('E',x)

quant 'E' x f = Exists x f
quant 'A' x f = Forall x f

empty_pi p = string p == [] && block p == []
-- assumes prennex normal form
prefix :: Formula -> Prefix
prefix (Exists v f) = ('E', v) `pre_cons` (prefix f)
prefix (Forall v f) = ('A', v) `pre_cons` (prefix f)
prefix f = Prefix False []  [] f

to_formula :: Prefix -> Formula
to_formula p@(Prefix True a b c) = to_formula (flip_q $ p)
to_formula (Prefix _ s (x:xs) f) = to_formula (Prefix False s xs (Exists x f))
to_formula (Prefix _ ((c,x):ss) [] f) = to_formula (Prefix False ss [] (quant c x f))
to_formula (Prefix _ [] [] f) = f

get_pi = max_bv . prefix
----------------------------
----------------------------
--Stack a = State [a] a
type State = (Formula, Prefix')

step' :: State-> State
step' (f, p') = ((to_formula $ fst ste),snd ste) where ste = step p' $ get_pi f
--     Prenex+simple -> Quantifier free / existential in free variables 
qtfy :: State -> Formula
qtfy (f,(p,n)) = to_formula $ p{formula=f}


master phi = qtfy $ (until (empty_pi . get_pi . fst ) $ step' ) start where start = step' (phi,empty_p)


or_list [] = Top
or_list [x] = x
or_list (x:xs) = Or x (or_list xs)

step p' pr = (pr {formula = simplify $ or_list $ snd3 $ temp , block = []},thd3 temp) where u = block pr;psi=formula pr;q= string pr;temp= make_dis ( [(u,psi)] ,[],p')

unused_var :: Vector -> Formula -> (Maybe Variable, Vector)
unused_var [] phi = (Nothing, [])
unused_var (x:xs) phi = if not (x `is_in` phi) then (Just x,xs) else fmap (x:) (unused_var xs phi)

existl_var :: Vector -> Formula -> (Maybe Variable, Vector)
existl_var [] phi = (Nothing, [])
existl_var (x:xs) phi = if predicate (Exists x phi) then (Just x,xs) else fmap (x:) (existl_var xs phi)

linear_var :: Vector -> Formula -> Maybe Variable
linear_var [] phi = Nothing
linear_var (x:xs) phi = if x `linear_in` phi then Just x else linear_var xs phi

linear_varN xs phi = filter (`linear_in` phi) xs
predicate x = False

--make_dis :: ([(Vector,Formula)],[Formula],Prefix')-> [Formula]
make_dis  w = until (null . fst3 ) (stuff) w

stuff ([], d,p) = ([],d,p)
stuff (((x,phi):q), d,p) = if x == [] then (q, phi:d,p) else ((fst out )++q,d,snd out) where out = stuff2 p x phi
stuff2 pi' x phi =
           if o  /= Nothing then ([(v, phi')],pi') else
           if o' /= Nothing then ([(v', (Exists (fromJust o') phi'))],pi') else
           if x' /= Nothing then (presQE (fromJust x') x phi',pi') else
           mapFst linearise $ semcover pi' x phi'
  where phi' = simplify phi
        (o,v) =unused_var x phi'
        x' = linear_var x phi'
        (o',v') = existl_var x phi'

stuff3 pi' x phi =
        (o,o',x')
  where (o,v) =unused_var x phi
        x' = linear_var x phi
        (o',v') = existl_var x phi

------------------------------
------------------------------
lin' (LE t1 t2) =if True || (is_linear t1 && is_linear t2) then  [(t1 - t2)] else []
lin' _ = []

lin :: Formula -> [Term]
lin'' phi = induct lin' (++) [] phi
lin phi = [0,2]++lin'' phi
hom phi = map homogenise $ lin'' phi
-- heft

divisor (LE _ _) = 1
divisor (Div q t) = q

mod' phi = induct divisor lcm 1 phi
---


-----------------------------------
--}
--

-- |x| < t -> (x ≥ 0        →           a · x < t)     ∧  (x < 0         →         −a · x < t).
abs_le x t = ((x `geq` 0) `implies` (x `le` t)) `And` ((x `le` 0) `implies` ((-x) `le` t))
abs_ge x t = ((x `geq` 0) `implies` (x `ge` t)) `And` ((x `le` 0) `implies` ((-x) `ge` t))


-- |x| < |y| + t -> ( x >= 0 /\ y >= 0 =>  x <  y +t) /\
--		    ( x >= 0 /\ y < 0  =>  x < -y +t) /\
--		    ( x < 0  /\ y >= 0 => -x <  y +t) /\
--		    ( x < 0  /\ y < 0  => -x < -y +t)

abs_plus_le x y t =( ((x `geq` 0) `And` (y `geq` 0)) `implies` (  x  `le` (  y  + t)) )
        `And`      ( ((x `geq` 0) `And` (y `le`  0)) `implies` (  x  `le` ((-y) + t)) )
        `And`      ( ((x `le`  0) `And` (y `geq` 0)) `implies` ((-x) `le` (  y  + t)) )
        `And`      ( ((x `le`  0) `And` (y `le`  0)) `implies` ((-x) `le` ((-y) + t)) )

abs_plus_ge x y t =( ((x `geq` 0) `And` (y `geq` 0)) `implies` (  x  `ge` (  y  + t)) )
        `And`      ( ((x `geq` 0) `And` (y `le`  0)) `implies` (  x  `ge` ((-y) + t)) )
        `And`      ( ((x `le`  0) `And` (y `geq` 0)) `implies` ((-x) `ge` (  y  + t)) )
        `And`      ( ((x `le`  0) `And` (y `le`  0)) `implies` ((-x) `ge` ((-y) + t)) )

abs_lle s se se2 =    ((s `geq` 0) `implies` ((se `leq` s) `And` (s`le` se2)) )
                `And` ((s `le` 0) `implies` ((se `leq` (-s)) `And` ((-s)`le` se2)) )

log2c b a =num $ ceiling $ logBase 2 $ fromInteger b / fromInteger a
log2f b a =num $ floor   $ logBase 2 $ fromInteger b / fromIntegral a
log2  b   =floor   $ logBase 2 $ fromInteger b

pwcmps theta xs = filter (\t -> check_all (\f -> powcmp f && t `elem` map_ evars f) theta ) xs

linear_helper :: (Vector,Formula)->(Vector,Formula)
linear_helper (xs,theta) =(xs,foldr (lineer') theta (pwcmps theta xs) )


lineer' x = transform $ lineer x
-- assumes terms are normalised so,
-- t < 0, aka b == 0
lineer :: Variable -> Atomic -> Formula
lineer x (LE a b)  = case split_eterm x (a - b) of
        (0,t) -> (le t 0)
        (c,t) -> case is_constant t of
                Just d -> rule1 x c (-d)
                Nothing -> case is_evar' t of
                        Just (y,d) -> rule2 x y c (-d)
                        Nothing -> (le a b)
lineer x (Div q t) = case split_eterm x t of
                        (1,r) -> case is_constant (-r) of
                                Just k -> rule3 x k q
                                Nothing -> Atom (Div q t)
                        _ -> Atom (Div q t)

--q12w
q' q r = [t|t<-[1..q-1], q `divides` (r*(2^t -1)) ]
r' q r = [s|s<-[0..q-1], q `divides` (2^s -r)  ]


minus_div q r x = Atom $ q `Div` (x - r)
rule3 x q r = case (q' q r, r' q r) of
                (_,[]) -> Bot
                ([],rr) -> abs_  (`eq` (num $ minimum rr)) (var x)
                (qq,rr) -> abs_ (minus_div (minimum qq) (num $ minimum rr) ) (var x)

rule1 x a b   = if a > 0 && b>0 then abs_le      (var x)         (log2c b a) else
                if a < 0 && b<0 then abs_ge      (var x)         (log2f b a) else
                if (a < b)      then Top else Bot
rule2 x y a b = if a > 0 then abs_plus_le (var x) (var y) (log2c b a) else abs_plus_ge (var x) (var y) (log2f b a)

linearise :: [(Vector, Formula)] -> [(Vector, Formula)]
linearise = map linear_helper
---------------------------
-- substitition helpers --
---------------------------
sub :: Name -> Term -> Atomic -> Atomic
sub   x t  = atomise (subst_term  x t)
--[t/2^x]
sub_e x t  = Atom . (atomise (subst_eterm x t) )
sub_e' a x t  = Atom . (atomise (subst_eterm' a x t) )
sub' a x t  = atomise (subst_term' a x t)

sub' :: Integer -> Name -> Term -> Atomic -> Atomic
--subst :: Formula -> Formula -> Formula -> Formula
subst' :: Integer -> Name -> Term -> Formula -> Formula
subst' n x t phi = transform' (sub' n x t) phi

subst_e x t phi = transform (sub_e x t) phi

subst_es [] t f = f
subst_es (x:xs) t f= subst_e x t (subst_es xs t f)
-- [y/x]
subst_atom x y a = if a ==x then y else Atom $ a
subst_atoms x y phi = transform (subst_atom x y) phi

subst_terms :: [Atomic] -> (Atomic -> Formula) -> Formula -> Formula

subst_terms [] f phi = phi
subst_terms (x:xs) f phi = subst_atoms x (f x) (subst_terms xs f phi)
-- f x --> T 
-- f x a --> sub_e x (num) a

-------------
------------


p1 (a,t) = (a,-t)
p2 (a,t) = (-a,t)
f1 (a,t) = a > 0
f2 (a,t) = a < 0

normI' xs = maximum $ map normI xs
-----------------
-----------------
-- PresQE   basicalyy solves for x and tries the values in [-g,g]
presQE :: Variable -> Vector -> Formula -> [(Vector,Formula)]
presQE x xs phi = [(xs,f)|g'<-gamma,f<-simplifyDiv (g')]
                  where gamma = [subst' a x (t+(num k)) phi `And` ( Atom $ Div a (t+(num k))) |(a,t)<-tt, k<-[-a*r'..a*r'] ]
                        r'    = (2* (fromIntegral $ normI' $ lin phi) + gg*(mod' phi))
                        gg    = (foldr lcm 1) [a | (a,_) <- tt]
                        tt    = nub $ (map p1 $ filter f1 $ map (split_lterm x) $ hom phi) ++ (map p2 $filter f2 $ map (split_lterm x) $ hom phi)

--presQE' :: Variable -> Vector -> Formula -> [(Vector,Formula)]
presQE' x xs phi = (0,r',gg,mod' phi,tt)
                  where gamma = [subst' a x (t+(num k)) phi `And` ( Atom $ Div a (t+(num k))) |(a,t)<-tt, k<-[-a*r'..a*r'] ]
                        r'    = (2* (fromIntegral $ normI' $ lin phi) + gg*(mod' phi))
                        gg    = (foldr gcd 1) [a | (a,_) <- tt]
                        tt    =  (map p1 $ filter f1 $ map (split_lterm x) $ hom phi) ++ (map p2 $filter f2 $ map (split_lterm x) $ hom phi)



------------------------------
-------------------------------



---------------
--simplifydiv
--------------
simplediv :: Atomic -> Bool
simplediv (LE _ _) = False
simplediv (Div q t) = case vars t of {[] -> False;(x:xs) -> if xs ==[] then fst3 (split_term x t) == 1 && constant t `elem` [-q..0] else False }

nonsimpledivs :: Formula -> [Atomic]
nonsimpledivs phi = filter (not . simplediv) (atoms phi)

-- t -> [d]
enum_env :: [Variable] -> Integer -> [Env] -- enumerates [t-> [d]] 'environments over [d]'
enum_env [] n = [env_empty]
enum_env (y:ys) n = [env_extend y a x|a<-[1..n],x<-(enum_env ys n)]

rec' :: (Env) -> Atomic -> Formula
rec' r (Div q t) = di q (num $ eval_term t r)
rec' r x = Atom x
-- r is an Env
--  ( /\ t∈t d | t − r(t)) ∧ ϕ[r(α) / α : α ∈ G])
div_substitution t r phi g d = simplify$ And (bigAND (\x ->  d `di` ( var x - (num $ eval_var x r))) t) (subst_terms g (rec' r) phi)


simplifyDiv :: Formula -> [Formula]
simplifyDiv phi = [div_substitution t r phi g d | r<- (enum_env t d) ] where {t = variables phi; d = foldr (\x -> lcm (divisor x)) 1 g ; g= nonsimpledivs phi}
---------------------------
---------------------------
lambda 0 = 0
lambda n = until (\x -> 2*x>n) (2*) 1

--phi[n/2^x]
asub x n as phi = subst_terms as (n) phi
asub' x n as phi = subst_terms as (n) phi

ineq x f = if not (powcmp f) && x `is_exp_in` (Atom f) then [f] else []
ineqs x f = induct (ineq x) (++) [] f

trm (LE t1 t2) = t1 -t2

semcover pi xs phi = (map (xs,) thetas, pi2) where
        nam = snd pi;
        (gg,nom) = semcover' xs nam phi;
        gam = gamma_list gg xs;
        sigmas = filter (\x -> (w_ nam x )`elem` (concat $ concat $ map ((map variables).snd) gg)) $  Map.keys nom;
        pi2 = update_pi' pi sigmas;
        thetas = map simplify $ (theta nom sigmas) ++ (theta2 nom sigmas gam)

type Naming = Map.Map Term Int
update :: Naming -> [Term] -> Naming
update x [] = x
update x (v:vs) |x==Map.empty = Map.fromList [(v,-1)]
                |otherwise    = Map.insertWith (flip const) v (minimum (Map.elems x) -1) x

w_ lambdas sigma = (Map.findWithDefault 0  sigma lambdas)

semcover' :: Vector -> Naming -> Formula -> ([(Variable,[Formula])],Naming)
semcover' [] sigs phi = ([],sigs)
semcover' xx@(x:xs) sigs phi = ((x,semloop x gamma_x sigs2 hh ii):( fst $ semcover' xs sigs2 phi),sigs2) where
        gamma_x = [phi]
        ii = ineqs x phi;
        hh = map (split_terms xx . trm ) ii
        sigmas = map snd hh;
        sigs2 = update sigs sigmas
ud = undefined
semcover'2 [] sigs phi = (ud,ud,ud,ud,ud)
semcover'2 xx@(x:xs) sigs phi = (gamma_x, ii, hh, sigmas, sigs2) where
        gamma_x = [phi]
        ii = ineqs x phi;
        hh = map (split_terms xx . trm ) ii
        sigmas = map snd hh;
        sigs2 = update sigs sigmas


top' = const Top
bot' = const Bot
ll = sub_e'
semloop x gamma_x lambdas [] ii = gamma_x
semloop x gamma_x lambdas ((eta,sigma):xs) ii = semloop x gamma_xx lambdas xs ii where
        aa = filter (\x-> (homogenise . trm) x == eta +sigma) ii
        aa' = map trm aa
        twoG = 128 * ( lambda (norm1 eta + maximum (map constant aa'))^2)
        g = log2 twoG
        a = ecoeff x eta
        vv = delete x $ vars eta
        w_s = evar (w_ lambdas sigma)
        l_a = lambda a
        beta = (evar x `ge` num twoG) `And` (bigAND (\u-> evar x `ge` (twoG .* evar u))  vv )
        gamma_1 g j v = ((evar x) `eq` (num 2^j))  `And` (asub x (sub_e x (2^j)) aa g)
        gamma_2 g j v = (evar x `ge` (num twoG)) `And` ((evar x) `eq` ((2^j) .* (evar v)))  `And` (asub x (sub_e x ((2^j).*(evar v))) aa g)
        gamma_3 g j v = beta `And` (lambda a .* (evar x) `le` (w_s)) `And` (sigma `le`  0) `And` (asub x top' aa g)
        gamma_4 g j v = beta `And` (lambda a .* (evar x) `le` (w_s)) `And` (sigma `geq` 0) `And` (asub x bot' aa g)
        gamma_5 g j v = beta `And` (lambda a .* (evar x) `eq` (w_s)) `And` (asub x (sub_e' l_a x w_s) aa g)
        gamma_6 g j v = beta `And` (lambda a .* (evar x) `eq` (2 .* w_s)) `And` (asub x (sub_e' l_a x $ 2 .* w_s) aa g)
        gamma_7 g j v = beta `And` (lambda a .* (evar x) `ge` (2 .* w_s)) `And` (num a `le` 0) `And` (asub x top' aa g)
        gamma_8 g j v = beta `And` (lambda a .* (evar x) `ge` (2 .* w_s)) `And` (num a `ge` 0) `And` (asub x bot' aa g)
        gammas_ = [gamma_1,gamma_2,gamma_3,gamma_4,gamma_5,gamma_6,gamma_7,gamma_8]
        gamma_xx = [gamma_n gamma j v |gamma_n<-gammas_, gamma <- gamma_x,j<-[0..g],v<-vv]

gammaX :: [(Variable,[Formula])] -> Variable -> [Formula]
gammaX g' x =  Map.findWithDefault [] x (Map.fromList g')
gamma_list g' xs = concat $ map (\x -> [And g $ bigAND (\y -> evar x `geq` evar y) xs| g<-gammaX g' x] ) xs


in_q x (pre,nam) = (w_ nam x) `elem` (map snd $ string pre)

update_pi' s [] = s
update_pi' p@(pre,nam) (sig:sigs) = if sig `in_q` p then p else (('A',w_ nam sig) `pre_cons` pre,nam)

--sem22 pi' = undefined-- if forall w_sigma not in pi' add it

theta lam sigmas = [sig `neq` 0 `And` (Not $ abs_lle (evar $ w_ lam sig) sig ((.*) 2 $ evar $ w_ lam sig) )|sig<-sigmas]


snull lam ss g = (subst_es (map (w_ lam) ss ) 0 g)

theta_term lam sigs sigs' gamma = (bigAND (\s ->  abs_lle (evar $ w_ lam s) s ((.*) 2 $ evar $ w_ lam s) ) sigs')
  `And`                       (bigAND (\s -> s `eq` 0) $ sigs \\ sigs') `And`
                              (snull lam (sigs\\sigs') gamma)
theta2 lam sigs ggamma = [theta_term lam sigs sigs' gamma | sigs'<-subsequences sigs, gamma <- ggamma]
sig = undefined





