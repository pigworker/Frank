> {-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances #-}

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

> type UName = String -- initial uppercase

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

> rigidTy :: (Eq x, Eq u) => Ty () (TyV x u) -> Ty () (TyV x u) ->
>            Maybe [(u, Ty () (TyV x u))]
> rigidTy (X x) (X y) | x == y = pure []
> rigidTy (X (Unif u)) t = pure [(u, t)]
> rigidTy t (X (Unif u)) = pure [(u, t)]
> rigidTy (D d as) (D e bs) | d == e = concat <$> halfZipWith rigidTy as bs
> rigidTy (is :-> o) (js :-> p) =
>   concat <$> halfZipWith rigidSgTy (o : is) (p : js)
> rigidTy _ _ = empty

> rigidSgTy  :: (Eq x, Eq u) => SgTy () (TyV x u) -> SgTy () (TyV x u) ->
>            Maybe [(u, Ty () (TyV x u))]
> rigidSgTy (s, t) (r, u) = (++) <$> rigidSg s r <*> rigidTy t u

> rigidSg  ::  (Eq x, Eq u) => Sg (TyV x u) () -> Sg (TyV x u) () ->
>              Maybe [(u, Ty () (TyV x u))]
> rigidSg (E _) (E _) = pure []
> rigidSg Pure Pure = pure []
> rigidSg ((sn, as) :+ sg) sg' = do
>   (bs, sg'') <- findSg sn sg'
>   (++) <$> rigidSg sg sg'' <*> (concat <$> halfZipWith rigidTy as bs)
> rigidSg _ _ = empty

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
>       (False, Just s)    -> (:< g) <$> unifyTy gz s t
>     (_, Just (v, mt)) | member (Unif v) vs ->
>       go gz (g :> gs) (deps mt `mappend` vs)
>     _ -> (:< g) <$> go gz gs vs

> unifyTy ::  TyDeclCx g x u => 
>             Bwd g -> Ty () (TyV x u) -> Ty () (TyV x u) -> Maybe (Bwd g)
> unifyTy gz s t = do
>   cs <- rigidTy s t
>   execStateT (traverse solve cs) gz


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

