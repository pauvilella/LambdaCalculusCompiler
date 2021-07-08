-- PRACTICA LambdaHask

-- Definir el tipus LT per poder definir lambda termes.
type Var = String

data LT = V Var | L Var LT | A LT LT

-- Derivar LT de Show
instance Show LT where
    show (V x) = show x
    show (L x lt) = "(/"++x++". " ++ show lt ++ ")"
    show (A lt1 lt2) = "("++ show lt1 ++ " " ++ show lt2 ++ ")"

-- FUNCIONS AUXILIARS
-- Funcions per trobar les variables lliures d'un lambda terme
rmVarAbs :: Var -> [Var] -> [Var]
rmVarAbs _ [] = []
rmVarAbs x (y:ys) = if x == y then rmVarAbs x ys else y : rmVarAbs x ys

freeVars :: LT -> [Var]
freeVars (V x) = [x]
freeVars (L x lt) = rmVarAbs x (freeVars lt)
freeVars (A lt1 lt2) = freeVars lt1 ++ freeVars lt2

-- Funcions per trobar les variables lligades d'un lambda terme
checkBoundInLT :: LT -> Var -> Bool
checkBoundInLT (V x) y = x == y
checkBoundInLT (L x lt) y = x /= y &&  checkBoundInLT lt y
checkBoundInLT (A lt1 lt2) y = checkBoundInLT lt1 y || checkBoundInLT lt2 y

boundVars :: LT -> [Var]
boundVars (V x) = []
boundVars (L x lt) = if checkBoundInLT lt x then x : boundVars lt else boundVars lt
boundVars (A lt1 lt2) = boundVars lt1 ++ boundVars lt2

-- FUNCIO SUBST
subst :: LT -> Var -> LT -> LT
subst (V x) y lt2 = if x == y then lt2 else V x
subst (L x lt1) y lt2
    | x == y = L x lt1
    | checkBoundInLT lt2 x = subst (L (x++"*") (subst lt1 x (V (x++"*")))) y lt2 -- Aqui detectem que hi hauria captura de variables, per tant el que fem es tornar a fer la substitucio però amb un canvi de variable de x a x* a lt1
    | otherwise = L x (subst lt1 y lt2)
subst (A lt1 lt2) y lt3 = A (subst lt1 y lt3) (subst lt2 y lt3)