> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Gubbins where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> newtype I x = I {unI :: x}
> instance Applicative I where
>   pure = I
>   I f <*> I s = I (f s)
> instance Functor I where
>   fmap = (<*>) . pure

> class Traversable f => HalfZip f where
>   halfZipWith :: Alternative i => (a -> b -> i c) -> f a -> f b -> i (f c)
>   halfZipWith f as bs = case halfZip as bs of
>     Nothing   -> empty
>     Just abs  -> traverse (uncurry f) abs
>   halfZip :: Alternative i => f a -> f b -> i (f (a, b))
>   halfZip = halfZipWith (curry pure)

> instance HalfZip [] where
>   halfZipWith f [] [] = pure []
>   halfZipWith f (a : as) (b : bs) = (:) <$> f a b <*> halfZipWith f as bs
>   halfZipWith f _ _ = empty

> data Bwd x
>   = B0 | Bwd x :< x deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
> infixl 4 :<

> data Fwd x
>   = F0 | x :> Fwd x deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
> infixr 4 :>

> (<><) :: Bwd x -> Fwd x -> Bwd x
> infixl 4 <><
> xz <>< F0 = xz
> xz <>< (x :> xs) = xz :< x <>< xs
