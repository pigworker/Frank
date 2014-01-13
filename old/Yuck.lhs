> {-#  LANGUAGE FunctionalDependencies, OverlappingInstances,
>      FlexibleInstances, UndecidableInstances, KindSignatures,
>      GADTs #-}

> module Yuck where

> import Data.Void

> newtype Label x s = Label s

> class Get x r t | r x -> t where
>   get :: x -> r -> t

> instance Get x (a, Label x s) s where
>   get x (_, Label s) = s

> instance Get x a s => Get x (a, b) s where
>   get x = get x . fst

> data X = X
> data Y = Y
> data Z = Z

> label :: x -> s -> Label x s
> label x s = Label s

> data COM :: * -> (* -> *) -> (* -> *) where
>   Top :: s -> (t -> x) -> COM (a, s -> t) f x
>   Pop :: f x -> COM c f x

> data NIL :: * -> * where
>   Paf :: Void -> NIL x

> class INJ a s t f g | a f -> s t g where
>   (<!>) :: (a, s) -> (t -> x) -> f x
>   seek :: f x -> a -> (s -> (t -> x) -> u) -> (g x -> u) -> u

> instance INJ a s t (COM (a , s -> t) f) f where
>   (a, s) <!> k = Top s k
>   seek (Top s k)  a y n  = y s k
>   seek (Pop g)    a y n  = n g

> instance INJ a s t f g => INJ a s t (COM c f) (COM c g) where
>   c <!> k = Pop (c <!> k)
>   seek (Top s k)  a y n  = n (Top s k)
>   seek (Pop g)    a y n  = seek g a y (n . Pop)

> {-
> class SUBSIG f g h | f g -> h where
>   inject   :: f x -> g x
>   dissect  :: g x -> (f x -> u) -> (h x -> u) -> u

> instance SUBSIG NIL g g where
>   inject   (Paf z) = absurd z
>   dissect  g y n = n g

> instance  (INJ a s t g h, SUBSIG f h k) =>
>           SUBSIG (COM (a, s -> t) f) g k where
>   inject (Top as k)  = as <!> k
>   inject (Pop f)     = Pop (inject f)
>   dissect g y n = seek g (\ as k -> y (Top as k)) $ \ h ->
>     dissect h (y . Pop) n

> instance SUBSIG f h k => SUBSIG f (COM c h) (COM c k) where
>   inject = Pop . inject
>   dissect (Top as k)  y n = n (Top as k)
>   dissect (Pop h)     y n = dissect h y (n . Pop)
> -}