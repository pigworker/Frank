> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, FlexibleInstances, MultiParamTypeClasses #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> module Template where

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> import Prelude hiding (elem, any)
> import Control.Applicative
> import Control.Monad
> import Data.Foldable
> import Data.Monoid

> import Pa


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Templates                                                          %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> type Template = [TBit]
> data TBit = Place | Mark String deriving (Eq, Ord)

> prefix :: Template -> Bool
> prefix (Mark _ : _ : _) = True
> prefix _ = False

> postfix :: Template -> Bool
> postfix (Place : _) = True
> postfix _ = False

> tempShow :: Template -> [String] -> String
> tempShow [Mark c]  [] = c
> tempShow bs        ss = "(" ++ splice False bs ss ++ ")" where
>   splice _     []             []        = ""
>   splice True  bs             ss        = " "  ++  splice False  bs  ss
>   splice _     []             (s : ss)  = s    ++  splice True   []  ss
>   splice _     (Mark m : bs)  ss        = m    ++  splice True   bs  ss
>   splice _     (Place : bs)   (s : ss)  = s    ++  splice True   bs  ss


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Template Tables                                                    %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data TemplateTable = TemplateTable
>   {  ttTemplates   :: [Template]              -- what are the templates
>   ,  ttPrecedence  :: [(Template, Template)]  -- what's outside what
>   ,  ttAssocs      :: [(Template, Int)]       -- which place associates
>   }  deriving Show

> punc :: TemplateTable -> String -> Bool
> punc tt s = elem s [x | bs <- ttTemplates tt, Mark x <- bs]

> gassocs :: TemplateTable -> Template -> (Template, Int)
> gassocs tbl t = case lookup t (ttAssocs tbl) of
>   Just i -> (t , i)
>   _ -> (t , negate 1)

> prLT :: TemplateTable -> ([TBit], Int) -> [TBit] -> Bool
> prLT tbl ([], _) _ = True
> prLT tbl (x, 0) y | x == y = True
> prLT tbl _ [_] = True
> prLT tbl (x, _) y = grLT (ttPrecedence tbl) x y where
>   grLT g x y = x /= y && grLE g x y
>   grLE g x y | x == y = True
>   grLE g x y = any (grLE g x) [z | (z, y') <- g, y == y']


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Templates                                                          %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> data TTree x
>   = TLeaf x [TTree x]
>   | TNode Template [TTree x]
>   deriving Show

> tApp :: TTree x -> [TTree x] -> TTree x
> tApp (TLeaf x xs) ys = TLeaf x (xs ++ ys)
> tApp (TNode t xs) ys = TNode t (xs ++ ys)

> resolve :: TemplateTable -> Pa (Either String x) (TTree x)
> resolve tbl = big ([], 0) <* eof where
>   is s = tok $ either (guard . (s ==)) mempty
>   big ti = (| (mafter ti) medium @ |)
>   medium = (| safter small @ |) <|>
>     foldMap (\ t -> (| (TNode t) (tmpl t (gassocs tbl t)) |)) pres
>   small = tok (either single (return . (`TLeaf` [])))
>   mafter ti s = (| (mafter ti) more @ | s |) where
>     more = (| id (foldMap
>                   (\ t -> (| (TNode t . (s :))
>                             (tmpl t (dock (gassocs tbl t))) |))
>                   possibles)
>             |)
>     dock (x : xs, i) = (xs, i - 1)
>     possibles = filter (\ u -> postfix u && prLT tbl ti u && grabs s u)
>                   (ttTemplates tbl)
>     grabs (TNode t _) u = prLT tbl (gassocs tbl u) t
>     grabs _ _ = True
>   safter s = (| safter (| (tApp s . return) small |) @ | s |) where
>   tmpl t ([], _) = (|[]|)
>   tmpl t (Mark s : ts, i) = (| id (-is s-) (tmpl t (ts, i)) |)
>   tmpl t (Place : ts, i) = (| big (t, i) : tmpl t (ts, i - 1) |)
>   pres = filter prefix (ttTemplates tbl)
>   single t  | elem [Mark t] (ttTemplates tbl)
>             = [TNode [Mark t] []]
>             | otherwise                        = []


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Show Instances                                                     %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

> instance Show TBit where
>   show Place     = "_"
>   show (Mark x)  = x


