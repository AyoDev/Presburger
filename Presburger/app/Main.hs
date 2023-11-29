module Main (main) where
import Nondeterministic
import Algorithms
import Test
import Formula
main :: IO ()
main = do print $ simplify $ master w; print $ master w
