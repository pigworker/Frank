> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, KindSignatures, GADTs, TypeSynonymInstances,
>     FlexibleInstances, GeneralizedNewtypeDeriving, TupleSections,
>     MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Main where

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
> import System.Environment
> import System.IO

> import Gubbins
> import Types
> import Pa
> import Syntax
> import Unify
> import Template
> import Check
> import ElabMonad
> import Elab
> import Run


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Line Checking                                                      %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


> lineCh :: ([Pat], Raw) -> ElabM (Template, ([PAT], TM {CHK}))
> lineCh l@(ps, r) = err (Line l) $ do
>   ((f, (i, (g, ps))), (ss, v)) <- lhsCh ps
>   t <- cxLocal g (withSigs ss (checkR v r))
>   return (f, (ps, t))

> lhsCh :: [Pat] -> ElabM ((Template, (Int, (Bwd Entry, [PAT]))), ([Sig], VT))
> lhsCh ps = patTree ps [] >>= \ t -> do
>   info <- getInfoE
>   case t of
>     TLeaf _ _ -> moanE $ BadLhs ps
>     TNode f ts -> case lookup f (funDecls info) of
>       Nothing -> moanE $ BadLhs ps
>       Just (i, vs, sa, v) -> do
>         ss <- getSigsE
>         gp <- ttpsCh f (map (`sAct` ss) vs) ts
>         return ((f, (i, gp)), (sAct sa ss, sAct v ss))

Must check coverage!


> makeDefs :: Source -> Either TError [(Template, VAL)]
> makeDefs src = case moc (typeInfo src) of
>   Left (e :? _) -> Left e
>   Right info -> do
>     tpes <- baseInfo info (traverse lineCh (sourceDefs src))
>     let fs = [ (t, [pes | (u, pes) <- tpes, t == u])
>              | (t, _) <- funDecls info
>              ]
>     let defs = primitiveDefs ++
>                map (\ (t, pes) -> (t, VU (lambda defs [] pes))) fs
>     return defs


> frank :: String -> IO ()
> frank s =
>   let src = source s in do
>     case sourceJunk src of
>       [] -> return ()
>       x -> putStrLn "Syntax Errors!" >> print x
>     case makeDefs src of
>       Left e -> putStrLn $ show e
>       Right defs -> putStrLn =<<
>         display (eval defs [] (H (FN [Mark "main"]) :/ []))

> main :: IO ()
> main = do
>   hSetBuffering stdout NoBuffering
>   hSetBuffering stdin NoBuffering
>   hSetEcho stdin False
>   args <- getArgs
>   case args of
>     [] -> frank =<< getContents
>     (f : _) -> do
>       frank =<< readFile (if elem '.' f then f else f ++ ".fk")
>       return ()


