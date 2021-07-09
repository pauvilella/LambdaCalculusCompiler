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

-- Funcio que mira si una determinada variable es troba dins una llista de variables o no
-- La faig servir per mirar si la variable de la lambda abstracció que estic substiuint està a dins del lambda terme que es ficarà a dins. Si sí que hi és, vol dir que es faria captura de variables, ja que la lliure quedaria caputrada per la variable de la lambda abstracció.
checkIfIsInFreeVars :: Var -> [Var] -> Bool
checkIfIsInFreeVars _ [] = False 
checkIfIsInFreeVars x (y:ys)
    | x == y = True 
    | otherwise = checkIfIsInFreeVars x ys


-- FUNCIO SUBST
subst :: LT -> Var -> LT -> LT
subst (V x) y lt2 = if x == y then lt2 else V x -- Si és una sola variable, i aquesta és la variable a ser subsituida, la substiuim; si no, deixem la variable que hi havia.
subst (L x lt1) y lt2
    | x == y = L x lt1 -- Vol dir que la variable que hauria de ser substituida no es lliure, ja que la lliga la labmda abstracció, per tant, no es substiuirà res, es queda el mateix lambda terme.
    | checkIfIsInFreeVars x (freeVars lt2) = subst (L (x++"*") (subst lt1 x (V (x++"*")))) y lt2 -- Aqui detectem que hi hauria captura de variables, per tant el que fem eés tornar a fer la substitució però amb un canvi de variable de x a x* a lt1.
    | otherwise = L x (subst lt1 y lt2) -- Deixem la lambda abstracció normal i fem la substitució a la part de dins de l'abstracció
subst (A lt1 lt2) y lt3 = A (subst lt1 y lt3) (subst lt2 y lt3) -- Simplement apliquem la substituicó als dos lambda termes de l'aplicació.

test_subst_sense_captura = subst (L "x" (V "y")) "y" (L "a" (V "b"))
test_subst_amb_captura = subst (L "x" (V "y")) "y" (L "y" (V "x"))