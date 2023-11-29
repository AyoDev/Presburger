module Test where
import Formula
import Term
import Algorithms
---------debug-------------------------------
a=0;b=1;c=2;x=23;y=24;z=25;a'=var a;b'=var b;c'=var c;x'=var x;y'=var y;z'= var z;a''=evar a;b''=evar b;c''=evar c;x''=evar x;y''=evar y;z''=evar z

e = Exists
u = Forall
aa [] phi =phi
aa (x:xs) phi = u x $ aa xs phi



ee [] phi = phi
ee (x:xs) phi = e x $ ee xs phi


j = e x $ e y $ (x' `le` y' ) `And` (x'' `le` 10) `Or` (x'' `eq` y'') `And` (Not $ x'' `ge` (y'' + 4))
w = e x $ e y $ e z $ (y' `eq` x'') `And` (z' `eq` y'')
w' = e x $ e y $ e z $ (y' `eq` x'') `And` (z' `eq` y'') `And` ((z' `le` 0) `And` (z' `ge` 2))

count = induct (const 1) (+) 0


f = Forall x (Atom $ x' `LE` 0)
k = e x $ e y $ (2.*x'' -5.*y'' - z') `le` 0

q = e x$ u y$ x'' `le` y''
q'' = ([([x,y],q)],[],empty_p)

q''' = (q, empty_p)
h = iterate stuff q''
h' = iterate step' q''' 


