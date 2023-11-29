module Term where
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
import qualified Data.IntMap as Map
import Prettyprinter
import Data.Text (Text, pack, cons)
import Data.Maybe(fromMaybe)
import Control.Monad


--type T = Text
char = pretty
text = pretty
empty = emptyDoc

type Name = Int
type Variable = Int

data Term = Term (Map.IntMap Integer) (Map.IntMap Integer) Integer deriving Ord

null' = all (== 0) . Map.elems
size m =length $ Map.elems $ Map.fromList $ non_zero m
--                            lin coeff, exp coeff
split_term :: Name -> Term -> (Integer, Integer, Term)
split_term x (Term m' m n) = (fromMaybe 0 c1,fromMaybe 0 c2, Term m2 m1 n)
  where (c1, m1) = Map.updateLookupWithKey (\_ _ -> Nothing) x m
        (c2, m2) = Map.updateLookupWithKey (\_ _ -> Nothing) x m'
--lterm means linear term
split_eterm :: Name -> Term -> (Integer, Term)
split_eterm x (Term m' m n) = (fromMaybe 0 c, Term m1 m n)
  where (c, m1) = Map.updateLookupWithKey (\_ _ -> Nothing) x m'

--lterm means linear term
split_lterm :: Name -> Term -> (Integer, Term)
split_lterm x (Term m' m n) = (fromMaybe 0 c, Term m' m1 n)
  where (c, m1) = Map.updateLookupWithKey (\_ _ -> Nothing) x m

split_terms :: [Variable] -> Term -> (Term,Term)
split_terms [] t =(0::Term, homogenise t)::(Term,Term)
split_terms (x:xs) t = case split_term x t of (c1,c2,t')-> (c1.*(var x) + c2.*(evar x) + (fst v),snd v) where v= split_terms xs t'

var :: Name -> Term
var x = Term (Map.empty) (Map.singleton x 1) 0
evar :: Name -> Term
evar x = Term (Map.singleton x 1) (Map.empty) 0

num :: Integer -> Term
num n = Term Map.empty Map.empty n


is_linear  (Term m' m n) = null' m'
homogenise (Term m' m n) = Term m' m 0
-------Eval-----------------------
newtype Env = Env (Map.IntMap Integer)

env_empty :: Env
env_empty = Env (Map.empty)

env_extend :: Name -> Integer -> Env -> Env
env_extend x v (Env m) = Env (Map.insert x v m)

env_function :: Env -> Name -> Integer
env_function (Env m) = (m Map.!)
-- The meaning of a term with free variables
-- If the term contains free variables that are not defined, then
-- we assume that these variables are 0.
eval_term :: Term -> Env -> Integer
eval_term (Term m' m k) (Env env) = sum (k : map eval_var (Map.toList m)++map eval_var2 (Map.toList m'))
  where eval_var (x,c) = case Map.lookup x env of
                           Nothing -> 0
                           Just v  -> c * v
        eval_var2 (x,c) = case Map.lookup x env of
                           Nothing -> 0
                           Just v  -> c * 2^v

subst_term :: Name -> Term -> Term -> Term
subst_term x n t = case split_term x t of
                     (c1, c2, Term m' m k) -> Term m' m k + c1 .* n 

subst_eterm :: Name -> Term -> Term -> Term
subst_eterm x n t = case split_term x t of
                     (c1, c2, Term m' m k) -> Term m' m k + c2 .* n 

subst_term' :: Integer -> Name -> Term -> Term -> Term
subst_term' a x n t = case split_term x t of
                     (c1, c2, Term m' m k) -> a .* (Term m' m k) + c1 .* n 

subst_eterm' :: Integer -> Name -> Term -> Term -> Term
subst_eterm' a x n t = case split_term x t of
                     (c1, c2, Term m' m k) -> a .* (Term m' m k) + c2 .* n 

eval_var :: Name -> Env -> Integer
eval_var x (Env e) = e Map.! x

non_zero ma = filter ((/= 0) . snd) (Map.toList ma) 
vars (Term m' m n) = map fst $ non_zero m' ++ non_zero m
lvars (Term m' m n) =map fst $ non_zero m  -- ++ non_zero m
evars (Term m' m n) =map fst $ non_zero m' -- ++ non_zero m

lcoeff x (Term m' m n) = Map.findWithDefault 0 x m
ecoeff x (Term m' m n) = Map.findWithDefault 0 x m'

coeffs (Term m' m n) = map abs $ Map.elems m' ++ Map.elems m ++[n]
norm1 = sum .coeffs
normI = maximum . coeffs
constant (Term m' m n) = n
----------------------arithmetic i guess---------------
instance Eq Term where
  t1 == t2 = is_constant (t1 -t2) == Just 0

instance Num Term where
 fromInteger = num
 Term m'1 m1 n1 + Term m'2 m2 n2 = Term (Map.unionWith (+) m'1 m'2) (Map.unionWith (+) m1 m2) (n1 + n2)
 negate (Term m' m n) = Term (Map.map negate m') (Map.map negate m) (negate n)
 t1 * t2  = case fmap (.* t2) (is_constant t1) `mplus`
                 fmap (.* t1) (is_constant t2) of
               Just t  -> t
               Nothing -> error $ unlines [ "[(*) @ Term] Non-linear product:"
                                          , "  *** " ++ show t1
                                          , "  *** " ++ show t2
                                          ]
 signum t  = case is_constant t of
               Just n  -> num (signum n)
               Nothing -> error $ unlines [ "[signum @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]

 abs t     = case is_constant t of
               Just n  -> num (abs n)
               Nothing -> error $ unlines [ "[abs @ Term]: Non-constant:"
                                           , " *** " ++ show t
                                           ]

(.*) :: Integer -> Term -> Term
0 .* _        = 0
1 .* t        = t
k .* Term m' m n = Term (Map.map (k *) m') (Map.map (k *) m) (k * n)


is_constant :: Term -> Maybe Integer
is_constant (Term m' m n) = guard (all (0 ==) (Map.elems m ++ Map.elems m')) >> return n

is_const (Term m' m n) = null' m && null' m'

is_evar' :: Term -> Maybe (Variable, Integer)
is_evar' (Term m' m n) = if (n == 0) && (null' m) && (size m' ==1) then return $ head $ Map.toList m' else Nothing

is_evar (Term m' m n) = (n == 0) && (size m'==1) && (null' m ) 
is_2_evar (Term m' m n) = (n == 0) && (size m'==2) && (null' m ) 
is_evar_const (Term m' m n) = (size m'==1) && (null' m ) 

------------------pretty shit--------------------
var_name' :: Name -> Text
var_name' x = let (a,b) = divMod x 26; rest = if a == 0 then mempty else pack (show a)
                  in toEnum (97 + b) `cons` rest
e_n  = (pack "2^" <>).var_name' 
v_n = var_name'


instance Show Term where show x = show (pretty x)
instance Pretty Term where
  pretty (Term m' m k) | show vars == mempty = text (pack $ show k)
                       | k == 0        = vars
                       | k > 0         = vars <+> char '+' <+> text (pack $ show k)
                       | otherwise     = vars <+> char '-' <+> text ( pack $ show $ abs k)
    where ppvar var_name (x,n) = sign <+> co <+> text (var_name x) 
              where (sign, co)| n == -1    = (char '-', empty)
                              | n < 0      = (char '-', text (pack  $show (abs n)) <+> char '*')
                              | n == 1     = (char '+', empty)
                              | otherwise  = (char '+', text (pack $ show n) <+> char '*')
          first_var :: (Name -> Text) -> (Name,Integer) -> Doc ann
          first_var var_name (x,1)  = text (var_name x)
          first_var var_name (x,-1) = char '-' <> text (var_name x)
          first_var var_name (x,n)  = text (pack (show n)) <+> char '*' <+> text (var_name x)
          vars = case (non_zero m', non_zero m)of
            ([],[])     -> empty
            ([],v:vs ) -> (first_var v_n v) <+> hsep (map (ppvar v_n) vs)
            (v:vs,[]) ->  (first_var e_n v) <+> hsep (map (ppvar e_n) vs)
            (v:vs, v') -> (first_var e_n v) <+> hsep (map (ppvar e_n) vs) <+> hsep (map (ppvar v_n) v')
          
instance Pretty Env where
  pretty (Env e)  = vcat (map sh (Map.toList e))
    where sh (x,y)  = text (var_name' x) <+> text (pack "=") <+> pretty y


