> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, KindSignatures, GADTs, TypeSynonymInstances,
>     FlexibleInstances, GeneralizedNewtypeDeriving, TupleSections,
>     MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Syntax where

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

> import Types
> import Pa


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% top level Source                                                   %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data Source = Source
>   {  sourceData :: [(UpId, ([UpId], [[Lump]]))]
>   ,  sourceSigs :: [(UpId, ([UpId], [([Lump], ([Sig], VT))]))]
>   ,  sourceDecl :: [([Lump], ([Sig], VT))]
>   ,  sourceDefs :: [([Pat], Raw)]
>   ,  sourceNote :: [[Tok]]
>   ,  sourceJunk :: [[Tok]]
>   }  deriving Show

> instance Monoid Source where
>   mempty = Source [] [] [] [] [] []
>   mappend (Source x1 x2 x3 x4 x5 x6) (Source y1 y2 y3 y4 y5 y6) =
>     Source (x1 ++ y1) (x2 ++ y2) (x3 ++ y3) (x4 ++ y4) (x5 ++ y5) (x6 ++ y6)

> source :: String -> Source
> source = foldMap ch . chunk where
>   ch ts = 
>     case (pa dataP ts, pa sgdP ts, pa declP ts, pa lineP ts, pa noteP ts) of
>       ([(d, [])], [], [], [], [])  ->  Source [d] [] [] [] [] []
>       ([], [(s, [])], [], [], [])  ->  Source [] [s] [] [] [] []
>       ([], [], [(f, [])], [], [])  ->  Source [] [] [f] [] [] []
>       ([], [], [], [(l, [])], [])  ->  Source [] [] [] [l] [] []
>       ([], [], [], [], [(n, [])])  ->  Source [] [] [] [] [n] []
>       _                            ->  Source [] [] [] [] [] [ts]

> data Lump = LNm String | LTy VT

> instance Show Lump where
>   show (LNm x) = x
>   show (LTy t) = show t

> instance TMang Lump where
>   tMang s (LNm x) = (|LNm ~x|)
>   tMang s (LTy t) = (|LTy (tMang s t)|)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% datatypes for Raw terms and patterns                               %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data Raw
>   = RN String
>   | RA [Raw]
>   | RCh Char
>   | RVd
>   | RBang
>   | RTh [([Pat],Raw)]
>   | RQ Raw Raw
>   deriving Show

> data Pat
>   = PN String
>   | PCh Char
>   | PVd
>   | PA [Pat]
>   | PRet Pat
>   | POp [Pat] Pat
>   deriving Show


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% top level chunks                                                   %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> dataP :: Pa Tok (UpId, ([UpId], [[Lump]]))
> dataP = (| (,) (-is "data"-) upid
>            (|(,) (many upid) (-is "="-) (sep (is "|") nomTys) (-eof-) |)
>          |)

> sgdP :: Pa Tok (UpId, ([UpId], [([Lump], ([Sig], VT))]))
> sgdP = (| (,) (-is "sig"-) upid
>           (|(,) (many upid) (-is "="-) 
>              (sep (is "|")
>                (|nomTys,
>                  (|(brk Sqr sigsP), (| id bigVT | Un |) | ([], Un) |)|))
>              (-eof-) |)
>         |)

> declP :: Pa Tok ([Lump], ([Sig], VT))
> declP = (|(,) nomTys (|(brk Sqr sigsP), (| id bigVT | Un |) | ([], Un) |)
>           (-eof-)|)

> lineP :: Pa Tok ([Pat], Raw)
> lineP = (|(,) (some patP) (-is "="-) bigRaw (-eof-)|)

> noteP :: Pa Tok [Tok]
> noteP = (|id (-is "note"-) (many (tok return)) (-eof-)|)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% parsing types                                                      %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> weeVT :: Pa Tok VT
> weeVT = (| D upid ~[]
>          | id (brk Sqr (|M sigsP (-is "?"-) bigVT|))
>          | Un (-brk Rnd eof-)
>          | U (brk Crl bigCT)
>          | id (brk Rnd bigVT)
>          |)

> bigVT :: Pa Tok VT
> bigVT = (| D upid (some weeVT)
>          | id weeVT
>          |)

> bigCT :: Pa Tok CT
> bigCT = (| bigVT :-> (-is "->"-) bigCT
>          | F (| id (brk Sqr sigsP) | [] |) bigVT
>          |)

> nomTys :: Pa Tok [Lump]
> nomTys = some (| LNm nom | LTy weeVT |)

> sigP :: Pa Tok Sig
> sigP = (| Pure (-brk Crl eof -)
>         | upid :$ (many weeVT)
>         |)

> sigsP :: Pa Tok [Sig]
> sigsP = sep (is ",") sigP


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% keywords and identifiers                                           %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> keywords :: [String]
> keywords = ["note","sig", "data", "->", ";", ",", "=", "|", "!","?"]

> nom :: Pa Tok String
> nom = tok $ \ t -> case t of
>   TN x@(c:_)
>     | not (c == '\''), not (isUpper c), not (elem x keywords) -> [x]
>   _ -> []

> upid :: Pa Tok UpId
> upid = tok $ \ t -> case t of
>   TN x@(c:_) | isUpper c, not (elem x keywords) -> [Up x]
>   _ -> []

> lit :: Pa Tok Char
> lit = tok $ \ t -> case t of
>     TN ['\'',c,'\'']       | c /= '\\' -> [c]
>     TN ['\'','\\',c,'\'']  -> [d| (c', d) <- escapees, c' == c]
>     _ -> []
>   where
>     escapees =
>       [  ('\'', '\'')
>       ,  ('\"', '\"')
>       ,  ('\\', '\\')
>       ,  ('n', '\n')
>       ,  ('r', '\r')
>       ,  ('t', '\t')
>       ,  ('b', '\b')
>       ]


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% parsing raw terms and patterns                                     %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> bigRaw :: Pa Tok Raw
> bigRaw = (| RQ medRaw (-is "?"-) bigRaw
>           | id medRaw
>           |)

> medRaw :: Pa Tok Raw
> medRaw = (| RA (|weeRaw : some weeRaw|)
>           | id weeRaw
>           |)

> weeRaw :: Pa Tok Raw
> weeRaw = (| RBang (-is "!"-)
>           | RN nom
>           | RCh lit
>           | RVd (-brk Rnd eof-)
>           | id (brk Rnd bigRaw)
>           | RTh (brk Crl (|clauseP : many (|id (-is "|"-) clauseP|)|))
>           |)

> clauseP :: Pa Tok ([Pat], Raw)
> clauseP = (| some patP, (-is "->"-) bigRaw
>            | ~[], bigRaw
>            |)

> patP :: Pa Tok Pat
> patP = (| PN nom
>         | PCh lit
>         | PVd (-brk Rnd eof-)
>         | PA (brk Rnd (some patP))
>         | PRet (brk Sqr patP)
>         | id (brk Sqr (|POp (some patP) (-is "?"-) patP|))
>         |)


