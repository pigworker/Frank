> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, KindSignatures, GADTs, TypeSynonymInstances,
>     FlexibleInstances, GeneralizedNewtypeDeriving, TupleSections,
>     MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Run where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Prelude hiding (elem, all)
> import Data.Char
> import Data.List hiding (elem, all)
> import Data.Monoid
> import Data.Foldable
> import Data.Traversable
> import Control.Applicative
> import Control.Monad
> import Control.Newtype
> import Data.Void
> import Control.Arrow

> import Gubbins
> import Types
> import Pa
> import Syntax
> import Unify
> import Template
> import Check
> import Elab


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Operational Behaviour                                              %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data VAL
>   = VC Template [VAL]
>   | VL Char
>   | VU COMP
>   | VR VAL
>   | VO Template [VAL] VAL

> type COMP = [VAL] -> Free Frank VAL

> type Frank = (Template, [VAL]) :>>: VAL

> type Env = [VAL]

> eval :: [(Template, VAL)] -> Env -> TM {d} -> Free Frank VAL
> eval fs g (H (VA i)) = (|(g !! i)|)
> eval fs g (H (FN f)) =
>   case lookup f fs of
>     Just v -> (|v|)
>     Nothing -> error ("Missing definition for " ++ show f)
> eval fs g (H (OP o)) = (|(VU $ \ vs -> com $ (o, vs) :? Ret)|)
> eval fs g (f :/ es) = (|apply (eval fs g f) (traverse (eval fs g) es) @ |)
> eval fs g (PApp f es) = do
>   f <- eval fs g f
>   us <- traverse (eval fs g) es
>   (|(VU $ \ vs -> apply f (us ++ vs))|)
> eval fs g (HAN h e) = (|handle (eval fs g h) ~(eval fs g e) @ |)
> eval fs g (E e) = eval fs g e
> eval fs g (CN c es) = (|(VC c) (traverse (eval fs g) es)|)
> eval fs g (CL c) = (|(VL c)|)
> eval fs g (BUNK e) = eval fs g e  -- seeya!
> eval fs g (LAM pes) = (|(VU (lambda fs g pes))|)

> apply :: VAL -> [VAL] -> Free Frank VAL
> apply (VU f) vs = f vs

> handle :: VAL -> Free Frank VAL -> Free Frank VAL
> handle (VU h) e = case moc e of
>   Right v -> h [VR v]
>   Left ((o, vs) :? k) -> case moc (h [VO o vs (VU (k . head))]) of
>     Right v -> Ret v
>     Left (([Mark "match"], []) :? _) -> com ((o, vs) :? (handle (VU h) . k))
>     Left c -> com c

> lambda :: [(Template, VAL)] -> Env -> [([PAT], TM {CHK})] -> COMP
> lambda fs g ((ps, e) : pes) vs = case matches ps vs g of
>   Just g   -> eval fs g e
>   Nothing  -> lambda fs g pes vs
> lambda fs g [] vs = com (([Mark "match"], []) :? undefined)  -- cheeky

> matches :: [PAT] -> [VAL] -> Env -> Maybe Env
> matches []       []        = return
> matches (p : ps) (v : vs)  = match p v >=> matches ps vs

> match :: PAT -> VAL -> Env -> Maybe Env
> match (PV _)       v                     = (|Just (v :)|)
> match (PC c ps)    (VC d vs) | c == d    = matches ps vs
> match (PL c)       (VL d) | c == d       = (|Just id|)
> match (PR p)       (VR v)                = match p v
> match (PO o ps p)  (VO n vs v) | o == n  = matches ps vs >=> match p v
> match _            _                     = (|Nothing|)

> instance Show VAL where
>   show (VC t vs) = tempShow t (map show vs)
>   show (VL c)    = show c
>   show (VU _)    = "{...}"
>   show (VR v)    = "!! VR " ++ show v
>   show (VO o vs v) = "!! VO " ++ tempShow o (map show vs) ++ " " ++ show v

> display :: Free Frank VAL -> IO String
> display c = case moc c of
>   Right v -> return $ show v
>   Left (([Mark "inch"], []) :? k) -> do
>     c <- getChar
>     display (k (VL c))
>   Left (([Mark "ouch"], [VL c]) :? k) -> do
>     putChar c
>     display (k (VC [] []))
>   Left ((o, vs) :? k) -> return $ "Unhandled: " ++ tempShow o (map show vs)

> primitiveDefs :: [(Template, VAL)]
> primitiveDefs =
>   [  ([Place, Mark "=Char=", Place], VU $ \ [VL c, VL d] -> Ret $
>        if c == d then VC [Mark "tt"] [] else VC [Mark "ff"] [])
>   ]
