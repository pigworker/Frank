> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, KindSignatures, GADTs, TypeSynonymInstances,
>     FlexibleInstances, GeneralizedNewtypeDeriving, TupleSections,
>     MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module ElabMonad where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Debug.Trace

> import Prelude hiding (elem, all, foldr, concat)
> import Data.Char
> import Data.List hiding (elem, all, foldr, concat)
> import Data.Monoid
> import Data.Foldable
> import Data.Traversable
> import Control.Applicative
> import Control.Monad
> import Control.Newtype
> import Control.Arrow
> import Data.Void

> import Gubbins
> import Types
> import Pa
> import Syntax
> import Template
> import Check



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Elaboration Monad and ghastly plumbing                             %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> type GetSigs = () :>>: [Sig]
> type GetInfo = () :>>: TypeInfo
> type GetCx = () :>>: Cx
> type SetCx = Cx :>>: ()

> type ElabM = Free ((Moan :+: (GetCx :+: SetCx)) :+: (GetSigs :+: GetInfo))

> moanE :: TError -> ElabM a
> moanE e = com (L (L (e :? absurd)))

> getCxE :: ElabM Cx
> getCxE = com (L (R (L (() :? Ret))))

> setCxE :: Cx -> ElabM ()
> setCxE g = com (L (R (R (g :? Ret))))

> modCxE :: (Cx -> Cx) -> ElabM ()
> modCxE f = (|setCxE (|f getCxE|) @ |)

> getSigsE :: ElabM [Sig]
> getSigsE = com (R (L (() :? Ret)))

> getInfoE :: ElabM TypeInfo
> getInfoE = com (R (R (() :? Ret)))

 elabUnify :: UnifyM x -> ElabM x
 elabUnify u = case moc u of
   Right x -> Ret x
   Left (L _) -> moanE UnifyFail
   Left (R (L (_ :? k))) -> getCxE >>= (elabUnify . k)
   Left (R (R (g :? k))) -> setCxE g >>= (elabUnify . k)

> ttT :: ElabM TemplateTable
> ttT = do
>     info <- getInfoE
>     (g, _) <- getCxE
>     let tt = templateT info
>     return (tt {ttTemplates =  cxTemps g (ttTemplates tt)})
>   where
>     cxTemps B0                ts  = ts
>     cxTemps (g :< (x ::: _))  ts  = cxTemps g (x : ts)
>     cxTemps (g :< _)          ts  = cxTemps g ts

> cxLocal :: Bwd Entry -> ElabM x -> ElabM x
> cxLocal g c = do
>     modCxE (((`mappend` g) . (:< Semicolon)) *** id)
>     x <- c
>     modCxE (popSemi *** id)
>     return x
>  where
>    popSemi (g :< Semicolon)    = g
>    popSemi (g :< _)            = popSemi g

> withSigs :: [Sig] -> ElabM x -> ElabM x
> withSigs ss c = case moc c of
>   Right x -> Ret x
>   Left (L (L (e :? k))) -> moanE e
>   Left (L (R (L (_ :? k)))) -> getCxE >>= (withSigs ss. k)
>   Left (L (R (R (g :? k)))) -> setCxE g >>= (withSigs ss. k)
>   Left (R (L (() :? k))) -> withSigs ss (k ss)
>   Left (R (R (() :? k))) -> getInfoE >>= (withSigs ss . k)   

> baseInfo :: TypeInfo -> ElabM x -> Either TError x
> baseInfo info = go (B0, 0) where
>   go g c = case moc c of
>     Right x -> Right x
>     Left (L (L (e :? k))) -> Left e
>     Left (L (R (L (_ :? k)))) -> go g (k g)
>     Left (L (R (R (g :? k)))) -> go g (k ())
>     Left (R (L (() :? k))) -> go g (k [Up "" :$ []])  -- the ineffable
>     Left (R (R (() :? k))) -> go g (k info)

> err :: (TError -> TError) -> ElabM x -> ElabM x
> err f c = case moc c of
>   Right x -> Ret x
>   Left (L (L (e :? k))) -> moanE $ f e
>   Left (L (R (L (_ :? k)))) -> getCxE >>= (err f . k)
>   Left (L (R (R (g :? k)))) -> setCxE g >>= (err f . k)
>   Left (R (L (() :? k))) -> getSigsE >>= (err f . k)
>   Left (R (R (() :? k))) -> getInfoE >>= (err f . k)   

> hnf :: VT -> ElabM VT
> hnf (Q i) = do
>     (g, _) <- getCxE
>     return $ improve (Q i) g
>   where
>     improve (Q i)  (g :< (j :=? Just v)) | i == j  = improve v g
>     improve (Q i)  (g :< _)                        = improve (Q i) g
>     improve v      _                               = v
> hnf v = (|v|)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Datatypes for contexts                                             %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data Entry
>   = Semicolon
>   | Int :=? Maybe VT
>   | Template ::: (Int, VT)
>   deriving Show

> type Cx = (Bwd Entry, Int)  -- a context and a nonce

> instance TMang Entry where
>   tMang s Semicolon = (|Semicolon|)
>   tMang s (q :=? mv) = (| ~q :=? tMang s mv|)
>   tMang s (x ::: iv) = (| ~x ::: tMang s' iv|) where
>     s' (VX i) = pure (X i)
>     s' v = s v

> withTopEntry :: (Entry -> ElabM (Bwd Entry)) -> ElabM ()
> withTopEntry f = getCxE >>= \ (g, i) -> case g of
>   B0      -> moanE $ Cockup "fell off the bottom of the context"
>   g :< e  -> do
>     setCxE (g, i)
>     h <- f e
>     modCxE ((`mappend` h) *** id)


