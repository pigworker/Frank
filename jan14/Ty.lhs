> {-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Ty where

> import Prelude hiding (concat)
> import Control.Applicative
> import Data.Traversable
> import Data.Foldable
> import Data.Maybe
> import Data.Monoid
> import Data.Set hiding (empty)
> import Control.Monad.State

> import Gubbins

> newtype UName = UName String deriving (Show, Eq) -- initial uppercase

> data Ty e x
>   = X x
>   | D UName [Ty e x]
>   | [SgTy e x] :-> SgTy e x
>   deriving Show

> data Sg x e
>   = E e
>   | Pure
>   | (UName, [Ty e x]) :+ Sg x e
>   deriving Show

> type SgTy e x = (Sg x e, Ty e x)

> ($+) :: (UName, [Ty e x]) -> Sg x e -> Sg x e
> s@(u, _) $+ sg = s :+ sgNo u sg where
>   sgNo u ((v, _) :+ sg) | u == v = sg
>   sgNo u (s :+ sg) = s :+ sgNo u sg
>   sgNo u sg = sg

> substTy :: Applicative a =>
>   (x -> a (Ty f y)) -> (e -> a (Sg y f)) -> Ty e x -> a (Ty f y)
> substTy x' e' (X x) = x' x
> substTy x' e' (D dn ts) = D dn <$> traverse (substTy x' e') ts
> substTy x' e' (is :-> o) =
>   (:->) <$> traverse (substSgTy x' e') is <*> substSgTy x' e' o

> substSg :: Applicative a =>
>   (x -> a (Ty f y)) -> (e -> a (Sg y f)) -> Sg x e -> a (Sg y f)
> substSg x' e' (E e) = e' e
> substSg x' e' Pure = pure Pure
> substSg x' e' ((sn, ts) :+ sg) =
>   ($+) <$> ((,) sn <$> traverse (substTy x' e') ts) <*> substSg x' e' sg

> substSgTy :: Applicative a =>
>   (x -> a (Ty f y)) -> (e -> a (Sg y f)) -> SgTy e x -> a (SgTy f y)
> substSgTy x' e' (s, t) = (,) <$> substSg x' e' s <*> substTy x' e' t

> instance Monad (Ty e) where
>   return = X
>   t >>= k = unI $ substTy (I . k) (I . E) t

> instance Monad (Sg t) where
>   return = E
>   sg >>= k = unI $ substSg (I . X) (I . k) sg

> occursTy :: Eq x => x -> Ty e x -> Bool
> occursTy x = getAny . getConst . substTy (failOn x) (Const . mempty) where
>   failOn x y = if x == y then Const (Any True) else Const mempty

> class Ord x => Deps t x where
>   deps :: t -> Set x

> instance Ord x => Deps (Ty e x) x where
>   deps = getConst . substTy (Const . singleton) (Const . mempty)

> instance Deps t x => Deps (Maybe t) x where
>   deps Nothing   = mempty
>   deps (Just t)  = deps t

> data TyV x u = Skol x | Unif u deriving (Show, Eq, Ord)

> class Rigid t c where
>   rigid :: t -> t -> Maybe [c]

> instance Rigid UName c where
>   rigid x y = if x == y then Just [] else Nothing

> instance (Rigid s c, Rigid t c) => Rigid (s, t) c where
>   rigid (s, t) (s', t') = (++) <$> rigid s s' <*> rigid t t'

> instance Rigid t c => Rigid [t] c where
>   rigid ts us = concat <$> halfZipWith rigid ts us

> instance (Eq x, Eq u) => Rigid (Ty () (TyV x u)) (u, Ty () (TyV x u)) where
>   rigid (X x)         (X y)         | x == y = pure []
>   rigid (X (Unif u))  t             = pure [(u, t)]
>   rigid t             (X (Unif u))  = pure [(u, t)]
>   rigid (D d as)      (D e bs)      = rigid (d, as) (e, bs)
>   rigid (is :-> o)    (js :-> p)    = rigid (is, o) (js, p)
>   rigid _             _             = empty

> instance (Eq x, Eq u) => Rigid (Sg (TyV x u) ()) (u, Ty () (TyV x u)) where
>   rigid (E _)             (E _)  = pure []
>   rigid Pure              Pure   = pure []
>   rigid ((sn, as) :+ sg)  sg'    = rigid (as, sg) =<< findSg sn sg'
>   rigid _                 _      = empty

> findSg :: UName -> Sg x e -> Maybe ([Ty e x], Sg x e)
> findSg sn ((sm, ts) :+ sg)
>   | sn == sm = return (ts, sg)
>   | otherwise = do (ts, sg') <- findSg sn sg ; return (ts, (sm, ts) :+ sg')
> findSg _ _ = empty

> class (Ord x, Ord u) => TyDeclCx g x u | g -> x u where
>   declSkol :: g -> Maybe x
>   declUnif :: g -> Maybe (u, Maybe (Ty () (TyV x u)))
>   defnUnif :: u -> Ty () (TyV x u) -> g

> solve ::  TyDeclCx g x u => (u, Ty () (TyV x u)) -> StateT (Bwd g) Maybe ()
> solve (u, X (Unif w))
>   | u == w = return ()
>   | otherwise = StateT $ \ gz -> (,) () <$> go gz
>   where
>   go B0 = empty
>   go (gz :< g) = case declUnif g of
>     Just (v, Nothing)
>       | v == u -> Just (gz :< defnUnif u (X (Unif w)))
>       | v == w -> Just (gz :< defnUnif w (X (Unif u)))
>     Just (v, Just t)
>       | v == u -> (:< g) <$> execStateT (solve (w, t)) gz
>       | v == w -> (:< g) <$> execStateT (solve (u, t)) gz
>     _ -> (:< g) <$> go gz
> solve (u, t) = StateT $ \ gz -> (,) () <$> go gz F0 (deps t)
>   where
>   -- go (context prefix) (shifted unif var decls) (dependency set)
>   go B0 _ _ = empty
>   go (gz :< g) gs vs = case (declSkol g, declUnif g) of
>     (Just x, _) | member (Skol x) vs  -> Nothing
>                 | otherwise           -> (:< g) <$> go gz gs vs
>     (_, Just (v, ms)) | u == v   -> case (member (Unif v) vs, ms) of
>       (True, _)          -> Nothing
>       (False, Nothing)   -> Just (gz <>< gs :< defnUnif u t)
>       (False, Just s)    -> (:< g) <$> unify gz s t
>     (_, Just (v, mt)) | member (Unif v) vs ->
>       go gz (g :> gs) (deps mt `mappend` vs)
>     _ -> (:< g) <$> go gz gs vs

> unify ::  (TyDeclCx g x u, Rigid p (u, Ty () (TyV x u))) => 
>           Bwd g -> p -> p -> Maybe (Bwd g)
> unify gz s t = do
>   cs <- rigid s t
>   execStateT (traverse solve cs) gz

> subSg :: TyDeclCx g x u =>
>          Bwd g -> Sg (TyV x u) () -> Sg (TyV x u) () -> Maybe (Bwd g)
> subSg gz Pure   _ = Just gz
> subSg gz (E ()) (E ()) = Just gz
> subSg gz (E ()) (_ :+ sg) = subSg gz (E ()) sg
> subSg gz ((sn, as) :+ sg) sg' | Just (bs, sg'') <- findSg sn sg' = do
>   gz <- subSg gz sg sg''
>   unify gz as bs

> data TestCx
>   = SKOL String
>   | UNIF String
>   | DEFN String (Ty () (TyV String String))
>   deriving Show

> instance TyDeclCx TestCx String String where
>   declSkol (SKOL x) = Just x
>   declSkol _ = Nothing
>   declUnif (UNIF u) = Just (u, Nothing)
>   declUnif (DEFN u t) = Just (u, Just t)
>   declUnif _ = Nothing
>   defnUnif = DEFN

