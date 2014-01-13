> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, FlexibleInstances, TupleSections,
>     GeneralizedNewtypeDeriving #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Pa where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Data.Char
> import Data.Monoid
> import Control.Applicative
> import Control.Monad

> import Gubbins


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Brackets and Tokens                                                %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data Brk = Rnd | Sqr | Crl deriving (Show, Eq)

> data Tok
>   = TB Brk [Tok] Bool
>   | TN String
>   deriving Show


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Chunking (and lexing)                                              %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> chunk :: String -> [[Tok]]
> chunk = snd . dent . lines where
>   dent = foldr
>     (\ s (d, gs) -> let sd = s ++ "\n" ++ d in
>       if leftA s then ("", lx B0 [] sd : gs) else (sd , gs))
>     ("", [])
>   leftA (c : cs) = not (isSpace c)
>   leftA _ = False

> lx :: Bwd Tok -> [(Brk, Bwd Tok)] -> String -> [Tok]
> lx tz  []                []         = tz <>> []
> lx tz  ((b, uz) : bs)    []         = lx (uz :< TB b (tz <>> []) False) bs []
> lx tz  bs                ('(' : s)  = lx B0 ((Rnd, tz) : bs) s
> lx tz  ((Rnd, uz) : bs)  (')' : s)  = lx (uz :< TB Rnd (tz <>> []) True) bs s
> lx tz  bs                ('[' : s)  = lx B0 ((Sqr, tz) : bs) s
> lx tz  ((Sqr, uz) : bs)  (']' : s)  = lx (uz :< TB Sqr (tz <>> []) True) bs s
> lx tz  bs                ('{' : s)  = lx B0 ((Crl, tz) : bs) s
> lx tz  ((Crl, uz) : bs)  ('}' : s)  = lx (uz :< TB Crl (tz <>> []) True) bs s
> lx tz  bs                ('\'' : c : '\'' : s)
>   | c /= '\\' = lx (tz :< TN ['\'', c, '\'']) bs s
> lx tz  bs                (c : s)
>   | solo c     = lx (tz :< TN [c]) bs s
>   | isSpace c  = lx tz bs s
>   | otherwise  = let (s0, s1) = span iddy s in lx (tz :< TN (c : s0)) bs s1
>   where
>     solo c = elem c ",;()[]{}!"
>     iddy c = not (isSpace c || solo c)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Parser Monad                                                       %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> newtype Pa t x = Pa {pa :: [t] -> [(x, [t])]} deriving Monoid
> instance Monad (Pa t) where
>   return x = Pa $ \ ts -> [(x, ts)]
>   Pa f >>= k = Pa $ \ ts -> do
>     (x, ts) <- f ts
>     pa (k x) ts
> instance MonadPlus (Pa t) where
>   mzero = mempty
>   mplus = mappend

> tok :: (t -> [x]) -> Pa t x
> tok p = Pa $ \ ts -> case ts of
>   t : ts -> map (, ts) (p t)
>   _ -> []

> eof :: Pa t ()
> eof = Pa $ \ ts -> case ts of
>  [] -> [((), [])]
>  _ -> []

> sep :: Pa t () -> Pa t x -> Pa t [x]
> sep s p = (| p : many (|id (-s-) p|)
>            | []
>            |)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Token-Specific Parsers                                             %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> is :: String -> Pa Tok ()
> is s = tok $ \ t -> case t of
>   TN s' | s == s' -> [()]
>   _ -> []

> brk :: Brk -> Pa Tok x -> Pa Tok x
> brk b p = tok $ \ t -> case t of
>   TB b' ts True | b == b' -> (|fst (pa (p <* eof) ts)|)
>   _ -> []
