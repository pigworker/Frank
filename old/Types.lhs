> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, FlexibleInstances #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Types where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Control.Newtype
> import Control.Applicative
> import Control.Monad.Identity
> import Data.Traversable
> import Data.List

> import Gubbins


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Datatypes for types                                                %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Frank has *value types*...

> data VT
>   = Ze                -- empty type                    {}
>   | Un                -- unit type                     ()
>   | U CT              -- thunked computation type      {C}
>   | D UpId [VT]       -- type constructor with params  D V1 .. Vn
>   | M [Sig] [Sig] VT  -- message from the first bunch
>   | X Int             -- rigid type variable           X
>   | Q Int             -- flexible type variable        ?X

... and *computation types*.

> data CT
>   = VT :-> CT      -- function type                 V -> C
>   | F [Sig] VT     -- effectful value type          [Ss] V
> infixr 4 :->

Types are named by UpId identifiers, beginning in uppercase.

> newtype UpId = Up {ui :: String} deriving (Show, Eq, Ord)

Signatures are named and parametrized.

> data Sig
>   =  (:$) {sigU :: UpId, sigPs :: [VT]}
>   |  Pure



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% The very nice mangler                                              %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> class TMang t where
>   tMang :: Applicative f => (Var -> f VT) -> t -> f t

> data Var = VD UpId | VX Int | VQ Int
> vD :: UpId -> VT
> vD u = D u []
> var :: (UpId -> x) -> (Int -> x) -> (Int -> x) -> Var -> x
> var vd vx vq (VD u) = vd u
> var vd vx vq (VX i) = vx i
> var vd vx vq (VQ i) = vq i

> instance TMang VT where
>   tMang s Ze           = (|Ze|)
>   tMang s Un           = (|Un|)
>   tMang s (U c)        = (|U (tMang s c)|)
>   tMang s (D u [])     = s (VD u)
>   tMang s (D u vs)     = (|D ~u (tMang s vs)|)
>   tMang s (M os ss v)  = (|M (tMang s os) (tMang s ss) (tMang s v) |)
>   tMang s (X i)        = s (VX i)
>   tMang s (Q i)        = s (VQ i)

> instance TMang CT where
>   tMang s (v :-> c)  = (|tMang s v :-> tMang s c|)
>   tMang s (F ss v)   = (|F (tMang s ss) (tMang s v)|)

> instance TMang Sig where
>   tMang s (u :$ vs) = (| ~u :$ tMang s vs|)
>   tMang s Pure      = (|Pure|)

> instance TMang x => TMang [x] where
>   tMang = traverse . tMang

> instance TMang x => TMang (Maybe x) where
>   tMang = traverse . tMang

> instance (TMang x, TMang y) => TMang (x, y) where
>   tMang s (x, y) = (|tMang s x, tMang s y|)

> instance TMang Int where
>   tMang s = pure

> xsub :: (TMang t) => [VT] -> t -> t
> xsub vs = ala' Identity tMang (var vD (bof vs) Q) where
>   bof [] i = X i
>   bof (x : xs) 0 = x
>   bof (x : xs) i = bof xs (i - 1)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Sig Action                                                         %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

A signature acts on a collection of signatures by shadowing or
disabling. (Might add individual disabling?) We lift structurally.

> class SigAct t where
>   sAct :: t -> [Sig] -> t

> instance SigAct [Sig] where
>   sAct sa ss = foldr s1 ss sa where
>     s1 Pure _ = []
>     s1 s@(f :$ _) ss = s : [s' | s'@(f' :$ _) <- ss, f' /= f]

> instance SigAct VT where
>   sAct (U c)        ss = U (sAct c ss)
>   sAct (D n vs)     ss = D n (map (`sAct` ss) vs)  -- really?
>   sAct (M os sa v)  ss = M os (sAct sa ss) (sAct v ss)
>   sAct t            ss = t

> instance SigAct CT where
>   sAct (F sa v)   ss = F (sAct sa ss) (sAct v ss)
>   sAct (v :-> c)  ss = sAct v ss :-> sAct c ss



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Show instances                                                     %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> instance Show VT where
>   show Ze           = "{}"
>   show Un           = "()"
>   show (U c)        = "{" ++ show c ++ "}"
>   show (D u [])     = ui u
>   show (D u vs)     = "(" ++ ui u ++ (vs >>= ((' ' :) . show)) ++ ")"
>   show (M os ss v)
>     = "[" ++ intercalate ", " (map show os) ++ " ? "
>     ++ (if null ss then "" else "[" ++ intercalate ", " (map show ss) ++ "]")
>     ++ show v ++ "]"
>   show (X i)        = "#" ++ show i
>   show (Q i)        = "?" ++ show i

> instance Show CT where
>   show (v :-> c)       = show v ++ " -> " ++ show c
>   show (F [] v)        = show v
>   show (F (s : ss) v)
>     = "[" ++ show s ++ (ss >>= ((", " ++) . show)) ++ "] " ++ show v

> instance Show Sig where
>   show (u :$ vs) = ui u ++ (vs >>= ((' ' :) . show))
>   show Pure = "{}"
