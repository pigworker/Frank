> {-# OPTIONS_GHC -F -pgmF she #-}
> {-#  LANGUAGE TypeOperators, FlexibleInstances, FunctionalDependencies,
>      RankNTypes, MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Gubbins where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Control.Applicative
> import Control.Newtype
> import Control.Monad.Identity
> import Data.Void
> import Data.Monoid
> import Data.Foldable
> import Data.Traversable
> import Data.List


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Newtype instance for Identity                                      %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> instance Newtype (Identity x) x where
>   pack = Identity
>   unpack (Identity x) = x


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Higher Kind Show                                                   %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> class ShowStarStar f where
>   showStarStar :: Show x => f x -> String


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Free Monad, sort of                                                %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data Free f x
>    = Ret x
>    | Com (forall t. (x -> Free f t) -> f (Free f t))

< data Free f x
<    = Ret x
<    | Com (f (Free f x))

> instance Monad (Free f) where
>   return = Ret
>   Ret x  >>= f = f x
>   Com d  >>= f = Com $ \ k -> d $ \ x -> f x >>= k

> com :: Functor f => f (Free f x) -> Free f x
> com ffx = Com $ \ k -> fmap (>>= k) ffx

> moc :: Free f x -> Either (f (Free f x)) x
> moc (Ret x) = Right x
> moc (Com f) = Left (f Ret)

> instance ShowStarStar f => ShowStarStar (Free f) where
>   showStarStar c = case moc c of
>     Right x -> "(Ret " ++ show x ++ ")"
>     Left ffx -> "(Com " ++ showStarStar ffx ++ ")"
> instance (ShowStarStar f, Show x) => Show (Free f x) where
>   show = showStarStar

> data (:>>:) s t x = s :? (t -> x)
> instance Functor (s :>>: t) where
>   fmap k (s :? f) = s :? (k . f)
> instance Show s => ShowStarStar (s :>>: t) where
>   showStarStar (s :? _) = "(" ++ show s ++ " :? ...)"
> instance (Show s, Show x) => Show ((s :>>: t) x) where
>   show = showStarStar

> data (:+:) f g x = L (f x) | R (g x)
> instance (Functor f, Functor g) => Functor (f :+: g) where
>   fmap k (L fx)  = L (fmap k fx)
>   fmap k (R gx)  = R (fmap k gx)
> instance (ShowStarStar f, ShowStarStar g) => ShowStarStar (f :+: g) where
>   showStarStar (L fx) = "(L " ++ showStarStar fx ++ ")"
>   showStarStar (R gx) = "(R " ++ showStarStar gx ++ ")"
> instance (ShowStarStar f, ShowStarStar g, Show x)
>   => Show ((f :+: g) x) where
>   show = showStarStar


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Snoc-lists                                                         %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Ord)
> infixl 5 :<

Fish...

> (<><) :: Bwd x -> [x] -> Bwd x
> xz <>< []        = xz
> xz <>< (x : xs)  = (xz :< x) <>< xs
> infixl 5 <><

...and chips

> (<>>) :: Bwd x -> [x] -> [x]
> B0         <>> xs  = xs
> (xz :< x)  <>> xs  = xz <>> (x : xs)
> infixr 5 <>>

> instance Monoid (Bwd x) where
>   mempty                = B0
>   mappend xz B0         = xz
>   mappend xz (yz :< y)  = mappend xz yz :< y

> instance Applicative Bwd where
>   hiding instance Functor
>   pure x = pure x :< x
>   (fz :< f)  <*> (sz :< s)  = (fz <*> sz) :< f s
>   _          <*> _          = B0

> instance Traversable Bwd where
>   traverse f B0         = (|B0|)
>   traverse f (xz :< x)  = (|traverse f xz :< f x|)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% UnionList                                                          %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> newtype UnionList x = UnionList [x] deriving (Show, Eq)
> instance Newtype (UnionList x) [x] where
>   pack = UnionList
>   unpack (UnionList x) = x
> instance Eq x => Monoid (UnionList x) where
>   mempty = UnionList []
>   mappend (UnionList a) (UnionList b) = UnionList (union a b)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Missing Traversables                                               %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> instance Traversable ((,) a) where
>   hiding instance Functor
>   traverse f (a, b) = (| ~a, f b|)

