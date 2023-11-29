import Algorithms
import Test
import Formula
(<.) = le
(^.) = And
j' = Top ^. Top ^. (Not (x'' <. y'')) ^. Top ^. (y'' <. (y''+ 1))
test1 = ([([a,b],(a'' <. b'') ^. Top )],[([a,b],a' <.b')])
main :: IO ()
main = do 
    print $ linear_helper  ([24],j') 
    print $ lineer' 24 j'
    print $ pwcmps j' [24]
    print $ pwcmps (a'' <. b'') [b] == [b]
