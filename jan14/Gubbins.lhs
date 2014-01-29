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
>   halfZipWith :: (a -> b -> Maybe c) -> f a -> f b -> Maybe (f c)
>   halfZipWith f as bs =  halfZip as bs >>= traverse (uncurry f)
>   halfZip :: f a -> f b -> Maybe (f (a, b))
>   halfZip = halfZipWith $ \ a b -> Just (a, b)

> instance HalfZip [] where
>   halfZipWith f [] [] = pure []
>   halfZipWith f (a : as) (b : bs) = (:) <$> f a b <*> halfZipWith f as bs
>   halfZipWith f _ _ = Nothing

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
