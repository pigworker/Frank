> module Tm where

> import Data.List

> newtype LName = LName String deriving (Eq, Ord)
> instance Show LName where show (LName x) = x

> data VIn
>   = VK LName [VIn]
>   | VT [([Req], VIn)]
>   | VO VOut
>   | VL VOut Pat VIn

> instance Show VIn where
>   show (VK k vs)    = brackety (show k) vs
>   show (VT bs )     = "{" ++ intercalate " | " (map body bs) ++ "}" where
>     body ([], v)    = show v
>     body (rs, v)    = (rs >>= \ r -> show r ++ " ") ++ " -> " ++ show v
>   show (VO o)       = show o
>   show (VL o PU v)  = show o ++ "; " ++ show v
>   show (VL o p v)   = show o ++ " => " ++ show p ++ "; " ++ show v

> data VOut
>   = VX LName
>   | VC LName [VIn]
>   | VA VHead [VIn]

> instance Show VOut where
>   show (VX x) = show x
>   show (VC c vs) = brackety (show c) vs
>   show (VA h vs) = brackety (show h) vs

> data VHead
>   = VF VOut
>   | VP LName

> instance Show VHead where
>   show (VF o) = show o ++ "!"
>   show (VP p) = show p

> data Req
>   = RP Pat
>   | RC LName [Pat] LName

> instance Show Req where
>   show (RP p)       = show p
>   show (RC c ps g)  = "(" ++ show c ++ (ps >>= \ p -> ' ' : show p) 
>                       ++ " ? " ++ show g ++ ")"

> data Pat
>   = PX LName
>   | PU
>   | PK LName [Pat]

> instance Show Pat where
>   show (PX x)     = show x
>   show PU         = "_"
>   show (PK k ps)  = brackety (show k) ps

> brackety :: Show a => String -> [a] -> String
> brackety f [] = f
> brackety f as = "(" ++ show f ++ (as >>= \ a -> ' ' : show a) ++ ")"
