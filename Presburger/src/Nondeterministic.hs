module Nondeterministic where
import Algorithms
import Formula
import Data.Function (on)
import Data.List (minimumBy, delete)
import Control.Monad (guard)

type Choice a = [a]


subformulae = undefined
masterN phi = qtfy $ (until (empty_pi . get_pi . fst ) $ step' ) start where start = step' (phi,empty_p)

stepN :: Choice State -> Choice State
stepN = map step'
step'N (f, p') = ((to_formula $ fst ste),snd ste) where ste = step p' $ get_pi f


stuffN ([], d) = ([],d)
stuffN (((x,phi):q), d) = if x == [] then (q, phi:d) else ((fst out )++q,d) where out = stuff2 p x phi
stuff2 pi' x phi =
           if o  /= Nothing then [(v, phi')] else
           if o' /= Nothing then [(v', (Exists (fromJust o') phi'))] else
           if x' /= Nothing then presQE (fromJust x') x phi' else
           mapFst linearise $ semcover pi' x phi'
  where phi' = simplify phi
        (o,v) =unused_var x phi'
        x' = linear_var x phi'
        (o',v') = existl_var x phi'


















--------------------------------------
--:semcover'' xs phi = semloop 


semcover pi xs phi = (map (xs,) thetas, pi2) where
        nam = snd pi;
        (gg,nom) = semcover' xs nam phi;
        gam = gamma_list gg xs;
        thetas = map simplify $ gam



semcover' :: Vector -> Naming -> Formula -> ([(Variable,[Formula])])
semcover' [] phi = ([],sigs)
semcover' xx@(x:xs) sigs phi = ((x,semloop x gamma_x sigs2 hh ii):(fst $ semcover' xs sigs2 phi),sigs2) where
        gamma_x = [phi]
        ii = ineqs x phi;
        hh = map (split_terms xx . trm ) ii









semloop'' x gamma_x lambdas [] ii = gamma_x
semloop'' x gamma_x lambdas ((eta,sigma):xs) ii = semloop x gamma_xx lambdas xs ii where
        aa = filter (\x-> (homogenise . trm) x == eta +sigma) ii
        aa' = map trm aa
        twoG = 128 * ( lambda (norm1 eta + maximum (map constant aa'))^2)
        g = log2 twoG
        a = ecoeff x eta
        vv = delete x $ vars eta
        w_s = 0 --evar (w_ lambdas sigma)
        l_a = lambda a
        beta = (evar x `ge` num twoG) `And` (bigAND (\u-> evar x `ge` (twoG .* evar u))  vv )
        gamma_1 g j v = ((evar x) `eq` (num 2^j))  `And` (asub x (sub_e x (2^j)) aa g)
        gamma_2 g j v = (evar x `ge` (num twoG)) `And` ((evar x) `eq` ((2^j) .* (evar v)))  `And` (asub x (sub_e x ((2^j).*(evar v))) aa g)
        gamma_3 g j v = beta `And` (lambda a .* (evar x) `le` (w_s)) `And` (sigma `le`  0) `And` (asub x top' aa g)
        gamma_4 g j v = beta `And` (lambda a .* (evar x) `le` (w_s)) `And` (sigma `geq` 0) `And` (asub x bot' aa g)
        gamma_5 g j v = beta `And` (lambda a .* (evar x) `eq` (w_s)) `And` (asub x (sub_e x w_s) aa g)
        gamma_6 g j v = beta `And` (lambda a .* (evar x) `eq` (2 .* w_s)) `And` (asub x (sub_e x w_s) aa g)
        gamma_7 g j v = beta `And` (lambda a .* (evar x) `ge` (2 .* w_s)) `And` (num a `le` 0) `And` (asub x top' aa g)
        gamma_8 g j v = beta `And` (lambda a .* (evar x) `ge` (2 .* w_s)) `And` (num a `ge` 0) `And` (asub x bot' aa g)
        gammas_ = [gamma_1,gamma_2,gamma_3,gamma_4,gamma_5,gamma_6,gamma_7,gamma_8]
        gamma_xx = [gamma_n gamma j v |gamma_n<-gammas_, gamma <- gamma_x,j<-[0..g],v<-vv]

gammaX :: [(Variable,[Formula])] -> Variable -> [Formula]
gammaX g' x =  Map.findWithDefault [] x (Map.fromList g')
gamma_list g' xs = concat $ map (\x -> [And g $ bigAND (\y -> evar x `geq` evar y) xs| g<-gammaX g' x] ) xs


