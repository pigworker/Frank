> {-# LANGUAGE MultiParamTypeClasses #-}

> module Check where

> import Data.Traversable
> import Control.Applicative
> import Control.Monad
> import Control.Monad.State

> import Gubbins
> import Ty
> import Tm

> type Type = Ty () (TyV Int Int)
> type Intf = Sg (TyV Int Int) ()

> type TYPE = Ty () Int
> type LDECL x = (LName, (Int, x))
> type UDECL x = (UName, (Int, [LDECL x]))

> data Globs = Globs
>   {  datatypes     :: [UDECL [TYPE]]
>   ,  interfaces    :: [UDECL ([TYPE], TYPE)]
>   }

> data CxE
>   = SKOL Int
>   | UNIF Int
>   | DEFN Int Type
>   | NOUN LName Type
>   | MARK
>   deriving Show

> instance TyDeclCx CxE Int Int where
>   declSkol (SKOL x) = Just x
>   declSkol _ = Nothing
>   declUnif (UNIF u) = Just (u, Nothing)
>   declUnif (DEFN u t) = Just (u, Just t)
>   declUnif _ = Nothing
>   defnUnif = DEFN

> type ChkS = (Bwd CxE, Intf, Int)

> type CHECK = StateT ChkS Maybe

> solitary :: [UDECL d] -> LName -> CHECK (UName, Int, Int, d)
> solitary us x = case
>   [(u, ua, yx, d) | (u, (ua, fs)) <- us, (y, (yx, d)) <- fs, x == y] of
>   [r] -> return r
>   _ -> empty

> skols :: Int -> CHECK [Type]
> skols n = do
>   (gz, sg, i) <- get
>   put (gz, sg, i + n)
>   return $ take n [X (Skol j) | j <- [i..]]

> unifs :: Int -> CHECK [Type]
> unifs n = do
>   (gz, sg, i) <- get
>   put (gz, sg, i + n)
>   return $ take n [X (Unif j) | j <- [i..]]

> can :: UName -> CHECK [Type]
> can i = do
>   (_, sg, _) <- get
>   fst <$> lift (findSg i sg)

> intfOK :: Intf -> CHECK ()
> intfOK sg' = do
>   (gz, sg, n) <- get
>   gz <- lift $ subSg gz sg' sg
>   put (gz, sg, n)

> withIntf :: Intf -> CHECK x -> CHECK x
> withIntf sg' a = do
>   (gz, sg, n) <- get
>   put (gz, sg', n)
>   x <- a
>   (gz, _, n) <- get
>   put (gz, sg, n)
>   return x

> mark :: CHECK x -> CHECK x
> mark a = do
>   (gz, sg, i) <- get
>   put (gz :< MARK, sg, i)
>   x <- a
>   (gz, _, i) <- get
>   let  unmark (gz :< MARK) = gz
>        unmark (gz :< _) = unmark gz
>   put (unmark gz, sg, i)
>   return x

> cxFind :: (CxE -> Maybe t) -> CHECK t
> cxFind p = get >>= \ (gz, _, _) -> go gz where
>   go (gz :< g) = lift (p g) <|> go gz
>   go B0 = empty

> equal :: Type -> Type -> CHECK ()
> equal s t = do
>   (gz, sg, i) <- get
>   gz <- lift $ unify gz s t
>   put (gz, sg, i)

> vin :: Globs -> Type -> VIn -> CHECK ()
> vin stuf (D d us) (VK k vs) = do
>   (da, ks) <- lift $ lookup d (datatypes stuf)
>   guard $ da == length us
>   (xn, ss) <- lift $ lookup k ks
>   xs <- unifs xn
>   halfZipWith (vin stuf) (map (>>= ((us ++ xs) !!)) ss) vs
>   return ()
> vin stuf t@(X (Unif _)) (VK k vs) = do -- saves type annotation
>   (d, da, xn, ss) <- solitary (datatypes stuf) k
>   us <- unifs da
>   xs <- unifs xn
>   halfZipWith (vin stuf) (map (>>= ((us ++ xs) !!)) ss) vs
>   equal (D d us) t
> vin stuf (is :-> (oi, t)) (VF bs) = () <$ traverse body bs where
>   body (rs, v) = mark $ do
>     halfZipWith (\ (i, t) r -> withIntf i $ req stuf oi t r) is rs
>     withIntf oi $ vin stuf t v
> vin stuf t (VO v) = do
>   s <- vout stuf v
>   equal s t
> vin _ _ _ = empty

> noun :: LName -> Type -> CHECK ()
> noun x t = do
>   (gz, sg, i) <- get
>   put (gz :< NOUN x t, sg, i)

> req :: Globs -> Intf -> Type -> Req -> CHECK ()
> req stuf oi t  (RP p) = pat stuf t p
> req stuf oi t  (RC c ps g) = do
>   (i, _, xn, (ss, u)) <- solitary (interfaces stuf) c
>   us <- can i
>   xs <- skols xn
>   let sbst = (>>= ((us ++ xs) !!))
>   halfZipWith (pat stuf) (map sbst ss) ps
>   (_, sg, _) <- get
>   noun g ([(oi, sbst u)] :-> (sg, t))

> pat :: Globs -> Type -> Pat -> CHECK ()
> pat stuf t (PX x)            = noun x t
> pat stuf t PU                = pure ()
> pat stuf (D d us) (PK k ps)  = do
>   (da, ks) <- lift $ lookup d (datatypes stuf)
>   guard $ da == length us
>   (xn, ss) <- lift $ lookup k ks
>   xs <- skols xn
>   halfZipWith (pat stuf) (map (>>= ((us ++ xs) !!)) ss) ps
>   return ()
> pat stuf t@(X (Unif _)) (PK k ps)  = do -- saves type annotation
>   (d, da, xn, ss) <- solitary (datatypes stuf) k
>   us <- unifs da
>   xs <- skols xn
>   halfZipWith (pat stuf) (map (>>= ((us ++ xs) !!)) ss) ps
>   equal (D d us) t
> pat _ _ _ = empty

> vout :: Globs -> VOut -> CHECK Type
> vout stuf (VX x) = cxFind $ \ g -> case g of
>   NOUN y t | x == y -> Just t
>   _ -> Nothing
> vout stuf (VC c vs) = do
>   (i, _, xn, (ss, t)) <- solitary (interfaces stuf) c
>   us <- can i
>   xs <- unifs xn
>   let sbst = (>>= ((us ++ xs) !!))
>   halfZipWith (vin stuf) (map sbst ss) vs
>   return (sbst t)
> vout stuf (VA v vs) = do
>   is :-> (oi, ot) <- vout stuf v
>   intfOK oi
>   halfZipWith (\ (ii, t) v -> withIntf ii $ vin stuf t v) is vs
>   return ot

