-- PRACTICA LambdaHask

-- Definir el tipus LT per poder definir lambda termes.
type Var = String

data LT = V Var | L Var LT | A LT LT

-- Derivar LT de Show
instance Show LT where
    show (V x) = show x
    show (L x lt) = "(/"++x++". " ++ show lt ++ ")"
    show (A lt1 lt2) = "("++ show lt1 ++ " " ++ show lt2 ++ ")"

-- Derivar LT de Eq (Provisional)
instance Eq LT where
  V x == V y = x == y
  L x lt1 == L y lt2 = x == y && lt1 == lt2
  A lt1 lt2 == A lt3 lt4 = lt1 == lt3 && lt2 == lt4
  _ == _ = False

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

-- FUNCIO ESTA NORMAL
estaNormal :: LT -> Bool 
estaNormal (V x) = True -- Si es nomes una variable, està en FN
estaNormal (L x lt) = estaNormal lt -- La part de l'abstracció segur que no forma un redex, però pot ser que n'hi hagi a dins l'abstracció, per tant retornem el resultat d'aplicar estaNormal al lt de dins.
estaNormal (A (L x lt) lt2) = False -- Aquest és la definicó de redex, per tant, segur que no estarà en formal normal. El poso abans que el cas general de l'aplicació perquè sinó no seria capaç de detectar-ho mai.
estaNormal (A lt1 lt2) = estaNormal lt1 && estaNormal lt2 -- Simplement retornem una AND entre el que retorni estaNormal dels dos termes de l'aplicació

-- FUNCIO BETA REDUEIX
betaRedueix :: LT -> LT
betaRedueix (V x) = V x -- Si es una variable, no es un redex, simplement la retornem
betaRedueix (L x lt) = L x (betaRedueix lt) -- És una abstracció, per tant segur que encara no hem trobat el redex que busquem, llavors, simplement seguim buscant-lo en el lambda terme de dins l'abstracció.
betaRedueix (A (L x lt1) lt2) = subst lt1 x lt2 -- Això és el redex, per tant, simplement el que hem de fer és beta reduir-lo fent servir la funcio subst, substituint les variables x que apareixin a lt1 per lt2.
betaRedueix (A lt1 lt2) = A (betaRedueix lt1) (betaRedueix lt2) -- Cas general de l'aplicació, sabem que no és un redex perquè si ho fós, hauria entrat per l'equcació de dalt, per tant només continuem buscant el redex als dos lt de l'aplicació.

-- FUNCIO REDUEIX_UN_N
redueixUnN :: LT -> LT
redueixUnN = betaRedueix

-- FUNCIO REDUEIX_UN_A
redueixUnA :: LT -> LT
redueixUnA (V x) = V x -- Si es una variable, no es un redex, simplement la retornem
redueixUnA (L x lt) = L x (redueixUnA lt) -- És una abstracció, segur que no és un redex, per tant, seguim buscant un redex en el lt de dins l'abstracció.
redueixUnA (A (L x lt1) lt2) -- Cas del redex, ara el que hem de mirar és si és l'últim redex de tots (el de més endins), o si hem de seguir buscant un a més endins. Per fer-ho, utiltizo la funció estaNormal.
    | not (estaNormal lt2) = A (L x lt1) (redueixUnA lt2) -- Si el lt2 té un redex a dins, anem a buscar aquest.
    | not (estaNormal lt1) = A (L x (redueixUnA lt1)) lt2 -- Si el lt1 té un redex a dins, anem a buscar aquest.
    | otherwise = subst lt1 x lt2 -- Si els dos lt estan en forma normal, vol dir que aquest és ja el redex de més endins, per tant, fem servir la funció subst per beta-reduir-lo.
redueixUnA (A lt1 lt2) -- Cas general aplicació, hem de mirar quin dels dos lt té un redex a dins per anar-lo a buscar. Comencem primer pel de la dreta.
    | not (estaNormal lt2) = A lt1 (redueixUnA lt2) -- Si el lt2 té un redex a dins, anem a buscar-lo.
    | otherwise = A (redueixUnA lt1) lt2 -- Si no, anem a buscar el redex de lt1.

-- FUNCIONS L_NORMALITZA_N i L_NORMALITZA_A
lNormalitza :: (LT -> LT) -> LT -> [LT] -- Segons si volem fer lNormalitzaN o lNormalitzaA, podem passar redueixUnN o redueixUnA com a primer paràmetre a aquesta funció.
lNormalitza f lt 
    | estaNormal lt = [] -- Si ja està en forma normal, no hem de fer cap reducció més, per tant, retornem una llista buida perquè no s'han d'afegir més passos
    | otherwise = f lt : lNormalitza f (f lt) -- Si encara no estem en forma normal, fem un pas de la reducció, l'afegim a la llista, i seguim fent reduccions amb el lambda terme resultant d'haver aplicat la reducció.

lNormalitzaN :: LT -> [LT]
lNormalitzaN = lNormalitza redueixUnN -- Li passem redueixUnN a lNormalitza perquè les reduccions les faci en ordre normal.

lNormalitzaA :: LT -> [LT]
lNormalitzaA = lNormalitza redueixUnA -- Li passem redueixUnA a lNormalitza perquè les reduccions les faci en ordre aplicatiu.

-- FUNCIONS NORMALITZA_N i NORMALITZA_A
normalitza :: (LT -> [LT]) -> LT -> (LT, Int) -- Segons si volem fer normalitzaN o normalitzaA, li hem de passar (lNormalitza redueixUnN) o (lNormalitza redueixUnA) com a primer paràmetre a aquesta funció. És a dir, fem una parcialització de lNormalitza).
normalitza f lt = (last (f lt), length (f lt)) -- Creem una tupla on el primer element és l'últim lambda terme, és a dir, la forma normal is el lambda terme inicial en tenia; i el segon element és la quantitat de passos que s'ha fet per arribar-hi.

normalitzaN :: LT -> (LT, Int)
normalitzaN = normalitza lNormalitzaN -- Li passem lNormalitzaN perquè faci la seqüència de reduccions en ordre normal.

normalitzaA :: LT -> (LT, Int)
normalitzaA = normalitza lNormalitzaA -- Li passem lNormalitzaA perquè faci la seqüència de reduccions en ordre aplicatiu.

-- TESTS
-- Definicions de lambda termes
a :: LT
a = L "x" (V "y")

b :: LT
b = L "a" (V "b")

c :: LT
c = L "y" (V "x")

d :: LT
d = L "x" (L "y" (A (V "y") (A (L "b" (V "y")) (V "x"))))

e :: LT
e = L "x" (L "y" (A (V "y") (V "y")))

f :: LT
f = A (L "y" (V "y")) (A (L "x" (V "x")) (V "x"))

g :: LT
g = A (L "y" (V "y")) (V "x")

h :: LT
h = L "x" (L "z" (L "x" (A (A (A (L "x" (L "y" (A (V "x") (V "y")))) (V "x")) (V "x")) (V "z"))))

-- Tests funció subst
test_subst_sense_captura :: LT
test_subst_sense_captura = subst a "y" b

test_subst_amb_captura :: LT
test_subst_amb_captura = subst a "y" c

-- Tests funció estaNormal
test_estaNormal_false :: Bool
test_estaNormal_false = estaNormal d

test_estaNormal_true :: Bool
test_estaNormal_true = estaNormal e

-- Tests funció betaRedueix
test_betaRedueix :: Bool 
test_betaRedueix = betaRedueix d == e

-- Tests funció redueixUnN
test_redueixUnN :: Bool
test_redueixUnN = redueixUnN d == e

-- Tests funció redueixUnA
test_redueixUnA :: Bool
test_redueixUnA = redueixUnA f == g

-- Tests funcions lNormalitzaN i lNormalitzaA
test_lNormalitzaN :: [LT]
test_lNormalitzaN = lNormalitzaN h
test_lNormalitzaA :: [LT]
test_lNormalitzaA = lNormalitzaA h

-- Tests funció normalitza
test_normalitzaN :: (LT, Int)
test_normalitzaN = normalitzaN h
test_normalitzaA :: (LT, Int)
test_normalitzaA = normalitzaA h
