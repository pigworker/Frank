> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, KindSignatures, GADTs, TypeSynonymInstances,
>     FlexibleInstances, GeneralizedNewtypeDeriving, TupleSections,
>     MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Check where

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

> import Gubbins
> import Types
> import Pa
> import Syntax
> import Template


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% TError                                                             %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data TError
>   = TMissing UpId
>   | SMissing UpId
>   | TArity UpId Int [VT]
>   | SArity UpId Int [VT]
>   | BadTemplate
>   | Cockup String
>   | AmbiguousPats [Pat]
>   | AmbiguousRaws [Raw]
>   | BadPat VT Pat
>   | NoConstructor VT Template
>   | AppliedPVar String
>   | RepeatedPVar Template
>   | PatArityError Template
>   | RawArityError Template
>   | BadLhs [Pat]
>   | UnifyVFail VT VT
>   | UnifyCFail CT CT
>   | UnifySFail Sig Sig
>   | BadBunk
>   | Useless VT
>   | CheckR VT Raw
>   | CantDo Sig [Sig]
>   | AmbiguousOp Template [Sig]
>   | ThunkMismatch CT ([Pat], Raw)
>   | BadMessPat [Pat]
>   | GuessThunk [([Pat], Raw)]
>   | BadHandlerType VT
>   | SynCon
>   | Line ([Pat], Raw) TError
>   | Raw VT Raw TError
>   | Dunno Template [Sig] [Template]
>   deriving Show

> type Moan = TError :>>: Void
> type Moaning = Free Moan

> moan :: TError -> Moaning x
> moan e = com (e :? absurd)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% checking top level data, signature and function declarations       %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data TypeInfo = TypeInfo
>   {  dataDecls  :: [(UpId, (Int, [(Template, [VT])]))]
>   ,  sigDecls   :: [(UpId, (Int, [(Template, ([VT], VT))]))]
>   ,  funDecls   :: [(Template, (Int, [VT], [Sig], VT))]
>   ,  templateT  :: TemplateTable
>   }  deriving Show

> typeInfo :: Source -> Moaning TypeInfo
> typeInfo src = do
>   let dt (n, (xs, cs)) =
>         (| ~n, (| ~(length xs), traverse (conTemplate src xs) cs|)|)
>       sg (n, (xs, os)) = (| ~n, (| ~(length xs), traverse oper os|)|) where
>         oper (vs, v) = (|rass (conTemplate src xs vs) (tScope src xs v)|)
>         rass (a, b) c = (a, (b, c))
>       fn stuf@(vs, (ss, v)) = do
>         let xs = ftvs src stuf
>         (t, vs') <- conTemplate src xs vs
>         ss' <- tScope src xs ss
>         v' <- tScope src xs v
>         return (t, (length xs, vs', ss', v'))
>   ds <- (| ~ primitiveTypes ++ traverse dt (sourceData src) |)
>   ss <- (| ~ primitiveSigs ++ traverse sg (sourceSigs src) |)
>   fs <- (| ~primitiveFunDecls ++ traverse fn (sourceDecl src) |)
>   let ts = (| fst (|(snd . snd) ds @ |)
>             | fst (|(snd . snd) ss @ |)
>             | fst fs
>             |)
>   return $ TypeInfo ds ss fs (TemplateTable ts [] [])

> ftvs :: TMang t => Source -> t -> [UpId]
> ftvs src = ala' UnionList (ala' Const tMang) (var chk mempty mempty)
>   where chk u = maybe (maybe [u] (const []) (lookup u primitiveTypes))
>            (const []) (lookup u (sourceData src))


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% generating a template and domains from a declaration               %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> conTemplate ::  Source -> [UpId] -> [Lump] -> Moaning (Template, [VT])
> conTemplate src xs vs = do
>   (bs, us) <- go vs
>   (|tmp bs, ~us|)
>   where
>     go [] = return ([], [])
>     go (LTy v : vs) = do
>       u <- tScope src xs v
>       (bs, us) <- go vs
>       return (Place : bs, u : us)
>     go (LNm n : vs) = do
>       (bs, us) <- go vs
>       return (Mark n : bs, us)
>     tmp [] = moan $ BadTemplate
>     tmp (Mark n : bs) | all place bs = (|[Mark n]|)
>     tmp bs = (|id (post bs)|)
>     post [] = (|[]|)
>     post (Place : Place : bs) = moan $ BadTemplate
>     post (b : bs) = (| ~b : post bs|)
>     place Place = True
>     place _ = False


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% type scope and arity checking                                      %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> class TScope x where
>   tScope :: Source -> [UpId] -> x -> Moaning x

> instance TScope x => TScope [x] where
>   tScope src xs = traverse (tScope src xs)

> instance TScope VT where
>   tScope src xs (D x []) | Just i <- findIndex (==x) xs = return (X i)
>   tScope src xs (D x vs) = do
>     a <- maybe
>            (maybe (moan $ TMissing x) (return . fst) (lookup x primitiveTypes))
>            (return . length . fst) $
>          lookup x (sourceData src)
>     if a == length vs
>       then (|(D x) (tScope src xs vs)|)
>       else moan $ TArity x a vs
>   tScope src xs (M os ss v) =
>     (|M (tScope src xs os) (tScope src xs ss) (tScope src xs v)|)
>   tScope src xs Un = return Un
>   tScope src xs Ze = return Ze
>   tScope src xs (U c) = (|U (tScope src xs c)|)
>   tScope src xs (X _) = moan $ Cockup "X already?"
>   tScope src xs (Q _) = moan $ Cockup "Q already?"

> instance TScope CT where
>   tScope src xs (v :-> c)  = (|tScope src xs v :-> tScope src xs c|)
>   tScope src xs (F ss v)   = (|F (tScope src xs ss) (tScope src xs v)|)

> instance TScope Sig where
>   tScope src xs (s :$ vs) = do
>     a <- maybe (maybe (moan $ SMissing s)
>             (pure . fst) (lookup s primitiveSigs))
>           (pure . length . fst) $
>           lookup s (sourceSigs src)
>     if a == length vs
>       then (| ~s :$ tScope src xs vs|)
>       else moan $ SArity s a vs
>   tScope src xs Pure = (|Pure|)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% prmimitives                                                        %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> primitiveTypes :: [(UpId, (Int, [(Template, [VT])]))]
> primitiveTypes =
>   [  (Up "Char", (0, []))
>   ,  (Up "Bool", (0, [([Mark "tt"], []), ([Mark "ff"], [])]))
>   ]

> char :: VT
> char = D (Up "Char") []

> bool :: VT
> bool = D (Up "Bool") []

> primitiveFunDecls :: [(Template, (Int, [VT], [Sig], VT))]
> primitiveFunDecls =
>   [  ([Place, Mark "=Char=", Place], (0, [char, char], [], bool))
>   ]

> primitiveSigs :: [(UpId, (Int, [(Template, ([VT], VT))]))]
> primitiveSigs =
>   [  (Up "Console", (0,
>      [  ([Mark "inch"], ([], char))
>      ,  ([Mark "ouch"], ([char], Un))
>      ]))
>   ]
