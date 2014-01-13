> {-# OPTIONS_GHC -F -pgmF she #-}
> {-#  LANGUAGE TypeOperators, FunctionalDependencies,
>      FlexibleContexts #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Unify where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Debug.Trace

> import Control.Newtype
> import Control.Applicative
> import Control.Monad
> import Control.Arrow
> import Data.Monoid
> import Data.Void
> import Data.Function
> import Data.List

> import Gubbins
> import Types
> import Template
> import Check
> import ElabMonad


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Unification Class                                                  %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> class Unify t where
>   (=?=) :: t -> t -> ElabM ()


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Unification Instances                                              %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> instance Unify VT where
>   -- s =?= t | trace (show s ++ " =?= " ++ show t) False = undefined
>   Un      =?=  Un      = return ()
>   U b     =?=  U c     = b =?= c
>   D b us  =?=  D c vs  | b == c = us =?= vs
>   M os v  =?=  M ps u  = os =?= ps >> v =?= u   -- too tight?
>   X i     =?=  X j     | i == j = return ()
>   Q i     =?=  Q j     = if i == j then return () else identify i j
>   Q i     =?=  v       = solve i [] v
>   v       =?=  Q i     = solve i [] v
>   s       =?=  t       = moanE $ UnifyVFail s t

> instance Unify CT where
>   (u :-> b)  =?=  (v :-> c)  = do u =?= v; b =?= c
>   F rr u     =?=  F ss v     = do
>     sortBy (compare `on` sigU) rr =?= sortBy (compare `on` sigU) ss
>     u =?= v
>   s          =?=  t          = moanE $ UnifyCFail s t

> instance Unify Sig where
>   (x :$ us) =?= (y :$ vs) | x == y = us =?= vs
>   s =?= t = moanE $ UnifySFail s t

> instance Unify t => Unify [t] where
>   []        =?=  []        = return ()
>   (a : as)  =?=  (b : bs)  = do a =?= b; as =?= bs
>   _         =?=  _         = moanE $ Cockup "arity mismatch"


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Occur Check                                                        %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> qoccur :: TMang t => Int -> t -> Bool
> qoccur q = ala' Any (ala' Const tMang) $
>   var (const False) (const False) (q ==)

> xoccur :: TMang t => Int -> t -> Bool
> xoccur i = ala' Any (ala' Const tMang) $
>   var (const False) (i ==) (const False)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Identification and Solving                                         %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

|identify i j| assumes |i| is not |j|

> identify :: Int -> Int -> ElabM ()
> identify i j = do
>  --(g, _) <- getCxE
>  --False <- trace ("IDENTIFY " ++ show g ++ show (i, j)) $ return False
>  withTopEntry $ \ e -> case e of
>   k :=? Nothing
>     | k == i -> return (B0 :< (k :=? Just (Q j)))
>     | k == j -> return (B0 :< (k :=? Just (Q i)))
>   k :=? Just v
>     | k == i -> solve j [] v >> return (B0 :< e)
>     | k == j -> solve i [] v >> return (B0 :< e)
>   _ -> identify i j >> return (B0 :< e)

|solve q es v| assumes |v| is not |Q q|

> solve :: Int -> [Entry] -> VT -> ElabM ()
> solve q es v = do
>  (g, _) <- getCxE
>  -- False <- trace ("SOLVE " ++ show g ++ show (q, es, v)) $ return False
>  withTopEntry $ \ e -> case e of
>   q' :=? mu | q' == q ->
>     if qoccur q es || qoccur q v
>       then moanE $ UnifyVFail (Q q) v
>       else case mu of
>         Nothing  -> return (B0 <>< es :< (q :=? Just v))
>         Just u   -> do modCxE ((<>< es) *** id); u =?= v; return (B0 :< e)
>   q' :=? _ | qoccur q' es || qoccur q' v -> solve q (e : es) v >> return B0
>   Skolem i -> if xoccur i es || xoccur i v
>       then moanE $ UnifyVFail (X i) v
>       else solve q es v >> return (B0 :< e)
>   e -> solve q es v >> return (B0 :< e)
