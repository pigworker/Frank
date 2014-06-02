> module Eval where

> import Data.List
> import Data.Maybe
> import Control.Applicative

> import Gubbins
> import Tm

> data Value
>   = Con LName [Value]
>   | Handler ([Value] -> Value)
>   | Comp LName [Value] (Value -> Value)

> type Env = [(LName, Value)]

> look :: LName -> Env -> Value
> look x env =
>   case lookup x env of
>     Nothing -> error $ "Failed to look up name: " ++ show x
>     Just v  -> v

> extend :: LName -> Value -> Env -> Env
> extend x v env = (x, v):env

> evalIn :: Env -> VIn -> Value
> evalIn env (VK l vs)  = Con l (map (evalIn env) vs)
> evalIn env (VT fs)    = Handler (handle env fs)
> evalIn env (VO v)     = evalOut env v
> evalIn env (VL v p w) =
>   bind (evalOut env v) (\v' -> evalIn (fromJust (matchPat p v') ++ env) w)

> bind :: Value -> (Value -> Value) -> Value
> bind (Comp c vs k) f = Comp c vs (\v -> bind (k v) f)
> bind v             f = f v

> handle :: Env -> [([Req], VIn)] -> [Value] -> Value
> handle env [] vs = Comp (LName "unhandled") [] undefined
> handle env ((rs, body):fs) vs =
>   case matchReqs rs vs of
>     Just env' -> evalIn env' body
>     Nothing   -> handle env fs vs

> matchReq :: Req -> Value -> Maybe Env
> matchReq (RP p)      v = matchPat p v
> matchReq (RC c ps x) (Comp c' vs k)
>              | c == c' = pure (extend x (Handler (\ [v] -> k v)))
>                            <*> matchPats ps vs
> matchReq _           _ = Nothing

> matchReqs :: [Req] -> [Value] -> Maybe Env
> matchReqs rs vs = fmap concat (halfZipWith matchReq rs vs)

> matchPat :: Pat -> Value -> Maybe Env
> matchPat (PX x)    v                     = return [(x, v)]
> matchPat PU        _                     = return []
> matchPat (PK k ps) (Con k' vs) | k == k' = matchPats ps vs
> matchPat _         _                     = Nothing

> matchPats :: [Pat] -> [Value] -> Maybe Env
> matchPats ps vs = fmap concat (halfZipWith matchPat ps vs)

> evalOut :: Env -> VOut -> Value
> evalOut env (VX x)    = look x env
> evalOut env (VC c vs) = Comp c (map (evalIn env) vs) id
> evalOut env (VA h vs) = evalHead env h (map (evalIn env) vs)

> evalHead :: Env -> VHead -> ([Value] -> Value)
> evalHead env (VF v) =
>   case evalOut env v of
>     Handler h -> h
