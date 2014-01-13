> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, TypeSynonymInstances, KindSignatures,
>     FlexibleInstances, GeneralizedNewtypeDeriving, TupleSections,
>     MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Elab where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Debug.Trace

> import Prelude hiding (elem, all, foldr, concat)
> import Data.Char
> import Data.List hiding (elem, all, foldr, concat)
> import Data.Monoid
> import Data.Foldable
> import Data.Traversable
> import Control.Applicative
> import Control.Monad
> import Control.Newtype
> import Control.Arrow
> import Data.Void

> import Gubbins
> import Types
> import Pa
> import Syntax
> import ElabMonad
> import Unify
> import Template
> import Check


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Cooked Terms                                                       %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data PAT
>   = PV String
>   | PC Template [PAT]      -- void pattern is |PC [] []|
>   | PL Char                -- char literal
>   | PR PAT
>   | PO Template [PAT] PAT  -- op params continuation

> instance Show PAT where
>   show (PV x) = x
>   show (PC t ps) = tempShow t (map show ps)
>   show (PR p) = "[" ++ show p ++ "]"
>   show (PO t ps p) =
>     "[" ++ tempShow t (map show ps) ++ " ? " ++ show p ++ "]"

> data Dir
>   = CHK
>   | SYN

> data TM :: {Dir} -> * where
>   H     :: HD                      -> TM {SYN}
>   (:/)  :: TM {SYN} -> [TM {CHK}]  -> TM {SYN}
>   PApp  :: TM {SYN} -> [TM {CHK}]  -> TM {SYN}
>   HAN   :: TM {SYN} -> TM {CHK}    -> TM {SYN}
>
>   E     :: TM {SYN}                -> TM {CHK}
>   CL    :: Char                    -> TM {CHK}
>   CN    :: Template -> [TM {CHK}]  -> TM {CHK}
>   BUNK  :: TM {CHK}                -> TM {CHK}
>   LAM   :: [([PAT], TM {CHK})]     -> TM {CHK}

> data HD  = VA Int
>          | FN Template  -- cache the def like a Birdman?
>          | OP Template

> hTemp :: Bwd Entry -> HD -> Template
> hTemp g (VA i)  = fst (inx g i)
> hTemp g (FN f)  = f
> hTemp g (OP o)  = o

> gShow :: Bwd Entry -> TM {d} -> String
> gShow g (H h)           = tempShow x ["_" | Place <- x] where x = hTemp g h
> gShow g (f :/ [])       = gShow g f ++ " !"
> gShow g (H h :/ ts)     = tempShow (hTemp g h) (map (gShow g) ts)
> gShow g (f :/ ts)       = "(" ++ show f ++ (ts >>= ((' ' :) . show)) ++ ")"
> gShow g (PApp f ts)     = "(" ++ show f ++ (ts >>= ((' ' :) . show)) ++ ")"
> gShow g (HAN h e)       = "(" ++ gShow g h ++ "?" ++ gShow g e ++ ")"
> gShow g (E t)           = gShow g t
> gShow g (CL c)          = "'" ++ c : "'"
> gShow g (CN c ts)       = tempShow c (map (gShow g) ts)
> gShow g (BUNK t)        = "(" ++ gShow g t ++ " {})"
> gShow g (LAM (a : as))  =
>   "{" ++ lShow a ++ (as >>= ((" | " ++) . lShow)) ++ "}" where
>     lShow ([], t) = gShow g t
>     lShow (ps, t) =
>       intercalate " " (map show ps) ++ " -> " ++ gShow (patOn g ps) t
>     patOn g []               = g
>     patOn g (PV x : ps)      = patOn (bind g x) ps
>     patOn g (PC _ ps : ps')  = patOn (patOn g ps) ps'
>     bind g x = g :< ([Mark x] ::: (0, Un))  -- cheeky!

> inx :: Bwd Entry -> Int -> (Template, (Int, VT))
> inx (_ :< (x ::: (i, j)))  0 = (x, (i, j))
> inx (g :< (_ ::: _))       i = inx g (i - 1)
> inx (g :< _)               i = inx g i
> inx B0                     i = ([Mark ('#' : show i)], (0, Un))

> instance Show (TM {d}) where
>   show t = gShow B0 t



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Type Checking and Synthesis                                        %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> checkR :: VT -> Raw -> ElabM (TM {CHK})
> -- checkR v r | trace ("checkR " ++ show (v, r)) $ False = undefined
> checkR v r = hnf v >>= \ v -> err (Raw v r) $ case r of
>   RVd      -> (|(CN [] []) (-Un =?= v-)|)
>   RCh c    -> (|(CL c) (-char =?= v-)|)
>   RTh prs  -> case v of
>     U c -> (|LAM (traverse (body c) prs)|)
>     _ -> moanE $ GuessThunk prs
>   RN n     -> checkR v (RA [RN n])
>   RBunk    -> moanE BadBunk
>   RA rs    -> (|ttrCh ~v (|rawTree ~rs ~[] @ |) @ |)
>   RQ h e   -> do
>     ss <- getSigsE
>     (h, z) <- synR h
>     z <- hnf z
>     case z of
>       U (M hs is u :-> F os w) -> do
>         w =?= v
>         canDo os
>         e <- withSigs (sAct hs ss) $ do
>           canDo (sAct hs is)
>           checkR u e
>         (|(E (HAN h e))|)
>       _ -> moanE $ BadHandlerType z
>   r        -> synR r >>= want v

> synR :: Raw -> ElabM (TM {SYN}, VT)
> -- synR r | trace ("synR " ++ show r) $ False = undefined
> synR (RN n)     = synR (RA [RN n])
> synR RVd        = moanE SynCon
> synR (RCh _)    = moanE SynCon
> synR RBunk      = moanE BadBunk
> synR (RA rs)    = rawTree rs [] >>= \ t -> case t of
>   TNode f ts -> appSyn f ts
>   TLeaf r ts -> synR r >>= \ tv -> mention tv ts
> synR (RTh prs)  = moanE $ GuessThunk prs
> synR (RQ h e)   = do
>   ss <- getSigsE
>   (h, v) <- synR h
>   v <- hnf v
>   case v of
>     U (M hs is u :-> F os w) -> do
>       canDo os
>       e <- withSigs (sAct hs ss) $ do
>         canDo (sAct hs is)
>         checkR u e
>       (|(HAN h e, w)|)
>     _ -> moanE $ BadHandlerType v
> synR RBang = moanE $ Cockup "! in synR"

> isBunk :: TTree Raw -> Bool
> isBunk (TLeaf RBunk []) = True
> isBunk _ = False

> ttrCh :: VT -> (TTree Raw) -> ElabM (TM {CHK})
> -- ttrCh v t | trace ("ttrCh " ++ show (v, t)) $ False = undefined
> ttrCh v (TNode f ts) = if (not (null ts) && isBunk (last ts))
>   then (|BUNK (ttrCh Ze (TNode f (init ts)))|) else do
>   info <- getInfoE
>   (g, _) <- getCxE
>   let constrs = [ (c, ((u, i), vs))
>                 | (u, (i , cs)) <- dataDecls info
>                 , (c, vs) <- cs
>                 ]
>   v <- hnf v
>   case v of
>     D u vs -> case lookup u (dataDecls info) of
>       Nothing -> moanE $ TMissing u
>       Just (i, cs) -> case lookup f cs of
>         Just ws -> (|(CN f) (ttrsCh f (xsub vs ws) ts)|)
>         Nothing -> appSyn f ts >>= want v
>     Q _ -> case (gFetch g f, filter ((f ==) . fst) constrs) of
>       (Nothing, [(_, ((u, m), vs))]) -> do
>         ws <- fresh m
>         ts <- ttrsCh f (xsub ws vs) ts
>         D u ws =?= v
>         (|(CN f ts)|)
>       _ -> appSyn f ts >>= want v
>     _ -> appSyn f ts >>= want v
> ttrCh v (TLeaf r []) = checkR v r
> ttrCh v _ = moanE $ Cockup "oops"

> want :: VT -> (TM {SYN}, VT) -> ElabM (TM {CHK})
> want v (t, u) = -- trace ("WANT " ++ show t ++ " : " ++ show u ++ " = " ++ show v) $
>   (|(E t) (-u =?= v-)|)

> getOps :: [Sig] -> ElabM [(Template, ([VT], (Sig, VT)))]
> getOps [] = return []
> getOps (Pure : _) = return []
> getOps (s@(u :$ vs) : ss) = do
>   info <- getInfoE
>   (| ~[  (ot, (xsub vs ois, (s, xsub vs oo)))
>       |  (u', (i, os)) <- sigDecls info, u == u'
>       ,  (ot, (ois, oo)) <- os
>       ] ++ getOps ss |)

> mkOpType :: [Sig] -> ([VT], (Sig, VT)) -> VT
> mkOpType ss (vs, (s, v)) = sAct (U (foldr (:->) (F [s] v) vs)) ss

> appSyn :: Template -> [TTree Raw] -> ElabM (TM {SYN}, VT)
> -- appSyn f ts | trace ("appSyn " ++ show (f, ts)) $ False = undefined
> appSyn f ts = do
>   info <- getInfoE
>   sigs <- getSigsE
>   ops <-  (|(map (id *** mkOpType sigs)) (getOps sigs)|)
>   (g, _) <- getCxE
>   case gFetch g f of
>     Just (i, (m, v)) -> do
>       ws <- fresh m
>       let v' = xsub ws v
>       -- False <- trace ("FOUND: " ++ show f ++ " : " ++ show v') $
>       --   return False
>       mention (H (VA i), xsub ws v) ts
>     Nothing -> case [v | (f', v) <- ops, f == f'] of
>       (_:_:_) -> moanE $ AmbiguousOp f sigs
>       [v] -> -- trace ("OPTYPE " ++ show f ++ " : " ++ show v) $
>                mention (H (OP f), v) ts
>       [] -> case lookup f (funDecls info) of
>         Just (m, vs, sa, v) -> do
>           ws <- fresh m
>           mention  (H (FN f),
>                     sAct (xsub ws (U (foldr (:->) (F sa v) vs))) sigs)
>                    ts
>         Nothing -> moanE $ Dunno f sigs (foldMap gnom g)

> gnom :: Entry -> [Template]
> gnom (x ::: _) = [x]
> gnom _ = []

> mention :: (TM {SYN}, VT) -> [TTree Raw] -> ElabM (TM {SYN}, VT)
> mention tv        []  = {- trace ("MENTION " ++ show tv) $ -} return tv
> mention (t, U c)  ts  = use t [] c ts
> mention (t, v)    ts  = moanE $ Useless v

> use :: TM {SYN} -> [TM {CHK}] -> CT -> [TTree Raw] -> ElabM (TM {SYN}, VT)
> use f [] (F ss v) (TLeaf RBang [] : ts) = do
>   canDo ss
>   mention (f :/ [], v) ts
> use f as (F ss v) ts = do
>   canDo ss
>   mention (f :/ as, v) ts
> use f as (v :-> c) (t : ts) = do
>   a <- ttrCh v t
>   use f (as ++ [a]) c  ts
> use f as c [] = (|(PApp f as, U c)|)

> canDo :: [Sig] -> ElabM ()
> canDo [] = return ()
> canDo (Pure : _) = return ()
> canDo (s : ss) = do
>   ss' <- getSigsE
>   findSig s ss' ss'
>   canDo ss

> findSig :: Sig -> [Sig] -> [Sig] -> ElabM ()
> findSig s [] sd = moanE $ CantDo s sd
> findSig s@(a :$ us) ((b :$ vs) : ss) sd
>   | a == b = us =?= vs
>   | otherwise = findSig s ss sd

> gFetch :: Bwd Entry -> Template -> Maybe (Int, (Int, VT))
> gFetch B0 _ = Nothing
> gFetch (g :< (x ::: r)) y
>   | x == y = Just (0, r)
>   | otherwise = (|((1 +) *** id) (gFetch g y)|)
> gFetch (g :< _) y = gFetch g y

> fresh :: Int -> ElabM [VT]
> fresh m = do
>     (g, n) <- getCxE
>     setCxE (grow g n m)
>     return (map Q (take m [n ..]))
>   where
>     grow g n 0 = (g, n)
>     grow g n m = grow (g :< (n :=? Nothing)) (n + 1) (m - 1)

> ttrsCh :: Template -> [VT] -> [TTree Raw] -> ElabM [TM {CHK}]
> ttrsCh f [] [] = return []
> ttrsCh f (v : vs) (t : ts) = (|ttrCh v t : ttrsCh f vs ts|)
> ttrsCh f _ _ = moanE $ RawArityError f

> body :: CT -> ([Pat], Raw) -> ElabM ([PAT], TM {CHK})
> body (v :-> c) (p : ps, r) = do
>   v <- hnf v
>   (g, p) <- patCh v p
>   (ps, t) <- cxLocal g $ body c (ps, r)
>   return (p : ps, t)
> body (F ss v) ([], r) = do
>   t <- withSigs ss (checkR v r)
>   return ([], t)
> body c (ps, r) = moanE $ ThunkMismatch c (ps, r)

> rawTree :: [Raw] -> [TTree Raw] -> ElabM (TTree Raw)
> rawTree rs ts = do
>   tbl <- ttT
>   case pa (resolve tbl) (map (rawPunc tbl) rs) of
>     [(t, [])]  -> case t of
>       TLeaf (RA rs) ts -> rawTree rs ts
>       t -> return (tApp t ts)
>     _          -> moanE $ AmbiguousRaws rs
>   where
>     rawPunc tbl (RN x) | punc tbl x  = Left x
>     rawPunc tbl p                    = Right p


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Pattern Checking                                                   %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> patCh :: VT -> Pat -> ElabM (Bwd Entry, PAT)
> patCh v            (PN x)      = do
>   info <- getInfoE
>   if elem [Mark x] (ttTemplates (templateT info))
>     then ttpCh v (TNode [Mark x] [])
>     else (|(B0 :< ([Mark x] ::: (0, v)), PV x)|)
> patCh v           PVd         = (|(B0, PC [] []) (-Un =?= v-)|)
> patCh v (PCh c) = (|(B0, PL c) (-char =?= v-)|)
> patCh (M os ss v)  (PRet p)    = (|(id *** PR) (patCh v p)|)
> patCh (M os ss v)  (POp ps p)  = patTree ps [] >>= \ z -> case z of
>   TLeaf p _ -> moanE $ BadMessPat ps
>   TNode o ts -> do
>     ops <- getOps os
>     case [x | (o', x) <- ops, o == o'] of
>       [(us, (s, u))] -> do
>         (gz, ps)  <- ttpsCh o us ts
>         (hz, p)   <- patCh (U (u :-> F (sAct os ss) v)) p
>         (|disjoin gz hz, ~(PO o ps p)|)
> patCh v            (PA ps)     = patTree ps [] >>= ttpCh v
> patCh v            p           = moanE $ BadPat v p

> ttpCh :: VT -> TTree Pat -> ElabM (Bwd Entry, PAT)
> ttpCh v (TLeaf p []) = patCh v p
> ttpCh v (TLeaf (PN n) _) = moanE $ AppliedPVar n
> ttpCh t@(D u vs) (TNode c ps) = do
>   info <- getInfoE
>   case lookup u (dataDecls info) of
>     Nothing -> moanE $ TMissing u
>     Just (i, cs) ->
>       case lookup c cs of
>         Nothing -> moanE $ NoConstructor t c
>         Just ws -> (|(id *** PC c) (ttpsCh c (xsub vs ws) ps)|)
> ttpCh v (TNode c _) = moanE $ NoConstructor v c

> ttpsCh ::  Template -> [VT] -> [TTree Pat] -> ElabM (Bwd Entry, [PAT])
> ttpsCh f [] [] = (| ~B0, ~[] |)
> ttpsCh f (v : vs) (t : ts) = do
>   v <- hnf v
>   (| disjoinC (ttpCh v t) (ttpsCh f vs ts) @ |)
> ttpsCh f _ _ = moanE $ PatArityError f

> disjoin :: Bwd Entry -> Bwd Entry -> ElabM (Bwd Entry)
> disjoin ez fz = (|(mappend ez fz) (-traverse chk fz-)|) where
>   chk e@(x ::: _) = traverse (occ x) ez
>   chk e = (|B0|)
>   occ x (y ::: _) | x == y = moanE $ RepeatedPVar x
>   occ x _ = (|()|)

> disjoinC ::  (Bwd Entry, PAT) -> (Bwd Entry, [PAT]) ->
>             ElabM (Bwd Entry, [PAT])
> disjoinC (ez, p) (fz, ps) = (|disjoin ez fz, ~(p : ps)|)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Patterns for Template Resolution                                   %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> patTree :: [Pat] -> [TTree Pat] -> ElabM (TTree Pat)
> patTree ps ts = do
>     tbl <- (|templateT getInfoE|)
>     case pa (resolve tbl) (map (patPunc tbl) ps) of
>       [(t, [])]  -> case t of
>         TLeaf (PA ps) ts -> patTree ps ts
>         t -> return (tApp t ts)
>       _          -> moanE $ AmbiguousPats ps
>   where
>     patPunc tbl (PN x) | punc tbl x  = Left x
>     patPunc tbl p                    = Right p

