-- PRACTICA LambdaHask

-- Imports
import Data.Char (chr, ord)

-- Definir el tipus LT per poder definir lambda termes.
type Var = String

data LT = V Var | L Var LT | A LT LT

-- Derivar LT de Show
instance Show LT where
  show (V x) = show x
  show (L x lt) = "(\\" ++ x ++ ". " ++ show lt ++ ")"
  show (A lt1 lt2) = "(" ++ show lt1 ++ " " ++ show lt2 ++ ")"

-- Derivar LT de Eq
instance Eq LT where
  lt1 == lt2 = aDeBruijn lt1 == aDeBruijn lt2

-- Derivar LT de Ord
-- Havia pensat dues maneres de fer-ho, segons l'allargada (length de la llista) del context, o segons quin des dos té el índex de variable més gran. He impelementat el segon perquè he arribat a la conclusió que és com una mesura similar, ja que com més variables hi hagi (index més alt), més llarg serà el context; i la segona opció era més fàcil d'implementar.
instance Ord LT where
  lt1 <= lt2 = getHighestIndex (aDeBruijn lt1) <= getHighestIndex (aDeBruijn lt2)

-- FUNCIONS AUXILIARS
-- Funcions per trobar les variables lliures d'un lambda terme
rmVarAbs :: Var -> [Var] -> [Var]
rmVarAbs _ [] = []
rmVarAbs x (y : ys) = if x == y then rmVarAbs x ys else y : rmVarAbs x ys

freeVars :: LT -> [Var]
freeVars (V x) = [x]
freeVars (L x lt) = rmVarAbs x (freeVars lt)
freeVars (A lt1 lt2) = freeVars lt1 ++ freeVars lt2

-- Funcions per trobar les variables lligades d'un lambda terme
checkBoundInLT :: LT -> Var -> Bool
checkBoundInLT (V x) y = x == y
checkBoundInLT (L x lt) y = x /= y && checkBoundInLT lt y
checkBoundInLT (A lt1 lt2) y = checkBoundInLT lt1 y || checkBoundInLT lt2 y

boundVars :: LT -> [Var]
boundVars (V x) = []
boundVars (L x lt) = if checkBoundInLT lt x then x : boundVars lt else boundVars lt
boundVars (A lt1 lt2) = boundVars lt1 ++ boundVars lt2

-- Funcio que mira si una determinada variable es troba dins una llista de variables o no
-- La faig servir per mirar si la variable de la lambda abstracció que estic substiuint està a dins del lambda terme que es ficarà a dins. Si sí que hi és, vol dir que es faria captura de variables, ja que la lliure quedaria caputrada per la variable de la lambda abstracció.
checkIfIsInFreeVars :: Var -> [Var] -> Bool
checkIfIsInFreeVars _ [] = False
checkIfIsInFreeVars x (y : ys)
  | x == y = True
  | otherwise = checkIfIsInFreeVars x ys

-- Funció que retorna la següent variable que s'ha de subsituir al lambda terme (assegurant-nos que aquesta variable no hi sigui ja al lambda terme)
newVariable :: Var -> LT -> Var
newVariable x lt = if checkIfIsInFreeVars x (freeVars lt) then newVariable (x ++ "*") lt else x

-- FUNCIO SUBST
subst :: LT -> Var -> LT -> LT
subst (V x) y lt2 = if x == y then lt2 else V x -- Si és una sola variable, i aquesta és la variable a ser subsituida, la substiuim; si no, deixem la variable que hi havia.
subst (L x lt1) y lt2
  | x == y = L x lt1 -- Vol dir que la variable que hauria de ser substituida no es lliure, ja que la lliga la labmda abstracció, per tant, no es substiuirà res, es queda el mateix lambda terme.
  | checkIfIsInFreeVars x (freeVars lt2) = subst (L novaVariable (subst lt1 x (V novaVariable))) y lt2 -- Aqui detectem que hi hauria captura de variables, per tant el que fem és tornar a fer la substitució però amb un canvi de variable de x a novaVariable a lt1.
  | otherwise = L x (subst lt1 y lt2) -- Deixem la lambda abstracció normal i fem la substitució a la part de dins de l'abstracció
  where
    novaVariable = newVariable (x ++ "*") lt1 -- Ens dona la nova variable que haurà de ser subsituida per no fer captura de variables.
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
betaRedueix (A lt1 lt2)
  | not (estaNormal lt1) = A (betaRedueix lt1) lt2 -- Primer hem de mirar si la part de l'esquerra té està forma normal, si no ho està, anem a beta-reduir aquest.
  | otherwise = A lt1 (betaRedueix lt2) -- Si sí que està en forma normal, anem a beta-reduir el de la dreta.

-- FUNCIO REDUEIX_UN_N
redueixUnN :: LT -> LT
redueixUnN = betaRedueix

-- FUNCIO REDUEIX_UN_A
redueixUnA :: LT -> LT
redueixUnA (V x) = V x -- Si es una variable, no es un redex, simplement la retornem
redueixUnA (L x lt) = L x (redueixUnA lt) -- És una abstracció, segur que no és un redex, per tant, seguim buscant un redex en el lt de dins l'abstracció.
redueixUnA (A (L x lt1) lt2) -- Cas del redex, ara el que hem de mirar és si és l'últim redex de tots (el de més endins), o si hem de seguir buscant un a més endins. Per fer-ho, utiltizo la funció estaNormal.
  | not (estaNormal lt1) = A (L x (redueixUnA lt1)) lt2 -- Si el lt1 té un redex a dins, anem a buscar aquest.
  | not (estaNormal lt2) = A (L x lt1) (redueixUnA lt2) -- Si el lt2 té un redex a dins, anem a buscar aquest.
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

-- DEFINICIONS DE LAMBDA TERMES
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

defId :: LT -- \x. x
defId = L "x" (V "x")

defTrue :: LT -- \x. \y. x
defTrue = L "x" (L "y" (V "x"))

defFalse :: LT -- \x. \y. y
defFalse = L "x" (L "y" (V "y"))

defNot :: LT -- \t. t false true
defNot = L "t" (A (A (V "t") defFalse) defTrue)

defAnd :: LT -- \x. \y.(x -> y | false)
defAnd = L "x" (L "y" (A (A (V "x") (V "y")) defFalse))

defTupla :: LT -- \x. \y. \p. p x y
defTupla = L "x" (L "y" (L "p" (A (A (V "p") (V "x")) (V "y"))))

defFst :: LT -- \x. x true
defFst = L "x" (A (V "x") defTrue)

defSnd :: LT -- \x. x false
defSnd = L "x" (A (V "x") defFalse)

defSuc :: LT -- \n. \f. \x. n f (f x)
defSuc = L "n" (L "f" (L "x" (A (A (V "n") (V "f")) (A (V "f") (V "x")))))

defSuma :: LT -- \m. \n. \f. \x. m f (n f x)
defSuma = L "m" (L "n" (L "f" (L "x" (A (A (V "m") (V "f")) (A (A (V "n") (V "f")) (V "x"))))))

defProd :: LT -- \m. \n. \f. \x. m (n f) x
defProd = L "m" (L "n" (L "f" (L "x" (A (A (V "m") (A (V "n") (V "f"))) (V "x")))))

defEsZero :: LT -- \n. n (\x. false) true
defEsZero = L "n" (A (A (V "n") (L "x" defFalse)) defTrue)

def0 :: LT -- \f. \x. x
def0 = L "f" (L "x" (V "x"))

def1 :: LT -- \f. \x. f x
def1 = L "f" (L "x" (A (V "f") (V "x")))

def2 :: LT -- \f. \x. f (f x)
def2 = L "f" (L "x" (A (V "f") (A (V "f") (V "x"))))

def3 :: LT -- \f. \x. f (f (f x))
def3 = L "f" (L "x" (A (V "f") (A (V "f") (A (V "f") (V "x")))))

def4 :: LT -- \f. \x. f (f (f (f x)))
def4 = fst (normalitzaN (A (A defProd def2) def2))

defG :: LT -- \x. ((\y. (\x. y y)) (\y. (\x. y y)))
defG = L "x" (A (L "y" (L "x" (A (V "y") (V "y")))) (L "y" (L "x" (A (V "y") (V "y")))))

defPrefn :: LT -- \f. \p. < false , (fst p -> snd p | f(snd p)) >
defPrefn = L "f" (L "p" (L "x" (A (A (V "x") defFalse) (A (A (A defFst (V "p")) (A defSnd (V "p"))) (A (V "f") (A defSnd (V "p")))))))

defPrec :: LT -- \n. \f. \x. snd (n (prefn f) <true, x>)
defPrec = L "n" (L "f" (L "x" (A defSnd (A (A (V "n") (A defPrefn (V "f"))) (L "p" (A (A (V "p") defTrue) (V "x")))))))

defY :: LT -- \f. (\x. f (x x)) (\x. f (x x))
defY = L "f" (A (L "x" (A (V "f") (A (V "x") (V "x")))) (L "x" (A (V "f") (A (V "x") (V "x")))))

defT :: LT -- (\x.(\y. y(x x y))) (\x.(\y. y(x x y)))
defT = A (L "x" (L "y" (A (V "y") (A (A (V "x") (V "x")) (V "y"))))) (L "x" (L "y" (A (V "y") (A (A (V "x") (V "x")) (V "y")))))

defFact :: LT -- T (\f. \n. (eszero n -> 1 | * n (f (prec n))))
defFact = A defT (L "f" (L "n" (A (A (A defEsZero (V "n")) def1) (A (A defProd (V "n")) (A (V "f") (A defPrec (V "n")))))))

-- TESTS
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

-- Tests defNot
test_defNot1 :: Bool
test_defNot1 = fst (normalitzaN (A defNot defFalse)) == defTrue

test_defNot2 :: Bool
test_defNot2 = fst (normalitzaN (A defNot defTrue)) == defFalse

-- Tests defAnd
test_defAnd1 :: Bool
test_defAnd1 = fst (normalitzaN (A (A defAnd defTrue) defFalse)) == defFalse

test_defAnd2 :: Bool
test_defAnd2 = fst (normalitzaN (A (A defAnd defTrue) defTrue)) == defTrue

-- Tests defSuc
test_defSuc1 :: Bool
test_defSuc1 = fst (normalitzaN (A defSuc def0)) == def1

test_defSuc2 :: Bool
test_defSuc2 = fst (normalitzaN (A defSuc def1)) == def2

-- Tests defPrec
test_defPrec1 :: Bool
test_defPrec1 = fst (normalitzaN (A defPrec def1)) == def0

test_defPrec2 :: Bool
test_defPrec2 = fst (normalitzaN (A defPrec def2)) == def1

-- Tests defProc
test_defProc :: LT
test_defProc = fst (normalitzaN (A (A defProd def2) def3)) -- Ha de donar: (/f. (/x. ("f" ("f" ("f" ("f" ("f" ("f" "x"))))))))

-- Tests defSuma
test_defSuma :: Bool
test_defSuma = fst (normalitzaN (A (A defSuma def2) def2)) == def4

-- Tests defFact
test_defFact1 :: Bool
test_defFact1 = fst (normalitzaN (A defFact def2)) == def2

test_defFact2 :: LT
test_defFact2 = fst (normalitzaN (A defFact def3)) -- Ha de donar 6.

test_defFact3 :: LT
test_defFact3 = fst (normalitzaN (A defFact def4)) -- Ha de donar 24. (El calcula bé)

-- DE BRUIJN

-- Definir el tipus LTdB
data LTdB = Va Int | La LTdB | Ap LTdB LTdB deriving (Eq)

-- Derivar LT de Show
instance Show LTdB where
  show (Va x) = show x
  show (La y) = "(\\. " ++ show y ++ ")"
  show (Ap x y) = "(" ++ show x ++ " " ++ show y ++ ")"

-- Definir el que és un context, que és una llista de tuples de (variable, index de la lambda a la que està lligada).
type Context = [(Var, Int)]

-- FUNCIONS AUXILIARS aDeBruijn
-- Retorna l'index que té associat en el context la varible que reb per paràmetre. Si la variable no està el context, retorna l'índex més gran del context.
getVarContext :: (Var, Int) -> Context -> Int
getVarContext (x, mesGran) [] = mesGran
getVarContext (x, mesGran) (y : ys)
  | fst y == x = snd y
  | snd y > mesGran = getVarContext (x, snd y) ys
  | otherwise = getVarContext (x, mesGran) ys

-- Funció per cridar getVarContext més còmodament (no havent de passar 0).
getVarIndex :: Var -> Context -> Int
getVarIndex x = getVarContext (x, 0)

-- Funció que reb una tupla i incrementa en 1 el segon element d'aquesta. La faig servir per passar-la a la funció map, per incrementar l'índex de totes les variables que hi ha en el context.
incSndElemOfTuple :: (Var, Int) -> (Var, Int)
incSndElemOfTuple (x, num) = (x, num + 1)

-- Serveix per afegir una variable en el context.
addVarInContext :: Var -> Context -> Context
addVarInContext x c
  | (x, index) `elem` c = c -- Si ja hi era, no modifiquem el context, simplement retornem el mateix.
  | otherwise = c ++ [(x, index + 1)] -- Si no, vol dir que és una variable nova, per tant, la concateno al final del context, ficant-li (index + 1) com a índex, ja que retornem que si no hi és, getVarIndex el que retorna és l'índex més gran del context.
  where
    index = getVarIndex x c -- Recuperem l'índex de la varialbe que volem afegir

-- Funció per transformar LT a LTdB
aDeBruijnAux :: Context -> LT -> LTdB
aDeBruijnAux c (V x) -- És una variable
  | (x, index) `elem` c = Va index -- Si ja està en el context, retornem el seu índex
  | otherwise = aDeBruijnAux (addVarInContext x c) (V x) -- Si no hi és, vol dir que és una variable nova, per tant, l'afegim al context i tornem a cridar a aDeBruijn amb aquest nou context
  where
    index = getVarIndex x c
aDeBruijnAux c (L x lt) = La (aDeBruijnAux nouContext lt) -- És una labmda abstracció, simplement printem la "/." i transformem el LT de dins passant-li el nou context modificat.
  where
    nouContext = map incSndElemOfTuple c ++ [(x, 0)] -- Si afegim una lambda abstracció, vol dir que totes les variables que hi hagin a la dreta d'aquesta, és a dir, el que quedi per transformar, hauran d'estar tots incrementats en 1, ja que hi haurà aquesta /. de més. A part d'això, també afegim la nova variable al context amb un índex de 0, ja que com que és la /. que acabem d'afegir, segur que estarà a 0 de distància.
aDeBruijnAux c (A (V x) lt) = Ap (aDeBruijnAux c (V x)) (aDeBruijnAux nouContext lt) -- Si una de les part de l'aplicació és una variable, anem a transforma aquesta normal. No obstant, quan fem la crida per transformar l'altra part de l'aplicació, hem d'incloure la variable de l'altra part al context i fer la crida amb aquest nou context , sinó, no la tindrem en compte i agafarem el context antic, on no estava posada.
  where
    nouContext = addVarInContext x c -- Nou context amb la variable x afegida, el passem a l'altra part de l'aplicació.
aDeBruijnAux c (A lt (V x)) = Ap (aDeBruijnAux nouContext lt) (aDeBruijnAux c (V x)) -- Cas igual que l'anterior però amb la variable a la part dreta de l'aplicació.
  where
    nouContext = addVarInContext x c
aDeBruijnAux c (A lt1 lt2) = Ap (aDeBruijnAux c lt1) (aDeBruijnAux c lt2) -- Cas general de l'aplicació, simplement transformem els 2 costats de l'aplicació.

-- Funció per cridar aDeBruijnAux més còmodament, és la que utilitzo als tests. Simplement afegeix el context que necessita com a paràmetre la funció aDeBruijnAux.
aDeBruijn :: LT -> LTdB
aDeBruijn = aDeBruijnAux []

-- FUNCIONS AUXILIARS deDeBruijn
-- Funció equivalent a getVarContext, però enlloc de buscar per varible, busquem per índex, però és el mateix.
getIndexContext :: (Var, Int) -> Context -> Var
getIndexContext (varMesGran, index) [] = varMesGran
getIndexContext (varMesGran, index) (y : ys)
  | snd y == index = fst y
  | fst y > varMesGran = getIndexContext (fst y, index) ys
  | otherwise = getIndexContext (varMesGran, index) ys

-- Funció equivalent a getVarIndex, serveix per cridar més còmodament a getIndexContext.
getIndexVar :: Int -> Context -> Var
getIndexVar index = getIndexContext ("`", index)

-- Funció que donada una variable, retorna la següent variable segons el codi ASCII.
nextVar :: [Char] -> [Char]
nextVar [] = []
nextVar [x]
  | ord x `elem` [96 .. 121] = [chr (ord x + 1)] -- està entre la "a" i la "y"
  | ord x == 122 = x : ['1'] --Hem arribat a la z, retornem z1
  | ord x == 57 = x : ['1'] --La variable acaba en 9, hi afegim un 1 al final i tornem a començar...
  | ord x `elem` [31 .. 38] = [chr (ord x + 1)] -- Si estem entre el 0 i l'1, retornem el següent núemro
  | otherwise = [x]
nextVar (x : xs) = x : nextVar xs

-- Funció equivalent a addVarInContext. Fa el mateix però aquí tenim l'índex inicialment i no la variable. Si l'índex ja hi és, retorna la variable corresponent. Si no hi és, l'afageix amb el següent valor de la varialbe més gran.
addIndexInContext :: Int -> Context -> Context
addIndexInContext index c
  | (var, index) `elem` c = c
  | otherwise = c ++ [(nextVar var, index)]
  where
    var = getIndexVar index c

-- Funció per transformar de LTdB a LT
deDeBruijnAux :: Context -> LTdB -> LT
deDeBruijnAux c (Va index) -- És una variable
  | (var, index) `elem` c = V var -- Si ja està al context, retornem la variable.
  | otherwise = deDeBruijnAux (addIndexInContext index c) (Va index) -- Si no hi és, l'afegim al context i tornem a cridar la funció deDeBruijn per transformar-la.
  where
    var = getIndexVar index c -- Recuperem la variable associada a l'índex.
deDeBruijnAux c (La lt) = L var (deDeBruijnAux nouContext lt) -- És una lambda abstracció. Transformem la nova variable de l'abstracció, i cridem deDeBruijnAux per acabar de transformar el lambda terme de dins amb el nou context.
  where
    c2 = map incSndElemOfTuple c -- Creem un nou context on estan totes les varialbes incrementades en 1 (seguint el codi ascii).
    nouContext = addIndexInContext 0 c2 -- Afegim un nou índex al nou context, el nou índex és 0, perquè és l'índex de la nova lambda abstracció que acabem de ficar, per tant, segur que estarà a distància 0.
    var = getIndexVar 0 nouContext -- Recuperem la nova variable associada a l'índex que acabem d'afegir al context.
deDeBruijnAux c (Ap (Va index) lt) = A (deDeBruijnAux c (Va index)) (deDeBruijnAux nouContext lt) -- Si una de les part de l'aplicació és un índex, anem a transforma aquest normal. No obstant, quan fem la crida per transformar l'altra part de l'aplicació, hem d'incloure l'índex de l'altra part al context i fer la crida amb aquest nou context , sinó, no el tindrem en compte i agafarem el context antic, on no estava posat.
  where
    nouContext = addIndexInContext index c -- Nou context amb l'índex afegit. El passem a l'altra costat de l'aplicació
deDeBruijnAux c (Ap lt (Va index)) = A (deDeBruijnAux nouContext lt) (deDeBruijnAux c (Va index)) -- Cas igual que l'anterior però amb l'índex a la part dreta de l'aplicació.
  where
    nouContext = addIndexInContext index c
deDeBruijnAux c (Ap lt1 lt2) = A (deDeBruijnAux c lt1) (deDeBruijnAux c lt2) -- Cas general de l'aplicació, simplement transformem els 2 costats de l'aplicació.

-- Funció per cridar deDeBruijnAux més còmodament, és la que utilitzo als tests. Simplement afegeix el context que necessita com a paràmetre la funció deDeBruijnAux.
deDeBruijn :: LTdB -> LT
deDeBruijn = deDeBruijnAux []

-- Funció per trobar quin és l'índex més gran d'un LTdB
getHighestIndexAux :: Int -> LTdB -> Int
getHighestIndexAux greater (Va x) = if x > greater then x else greater
getHighestIndexAux greater (La lt) = getHighestIndexAux greater lt
getHighestIndexAux greater (Ap lt1 lt2) = if greaterLT1 > greaterLT2 then greaterLT1 else greaterLT2
  where
    greaterLT1 = getHighestIndexAux greater lt1
    greaterLT2 = getHighestIndexAux greater lt2

-- Funció per cridar més còmodament a getHighestIndexAux. És la que faré servir per fer la alfa-equivalencia.
getHighestIndex :: LTdB -> Int
getHighestIndex = getHighestIndexAux 0

-- TESTS
-- Tests aDeBruijn
test_aDeBruijn1 :: LTdB
test_aDeBruijn1 = aDeBruijn (L "a" (A (V "a") (L "b" (A (A (V "c") (V "d")) (V "b"))))) -- /a. a /b. c d b

test_aDeBruijn2 :: LTdB
test_aDeBruijn2 = aDeBruijn (L "a" (L "b" (A (A (A (V "c") (V "d")) (V "b")) (V "a")))) -- /a. /b. c d b a

test_aDeBruijn3 :: LTdB
test_aDeBruijn3 = aDeBruijn (A (L "x" (V "x")) (L "x" (V "x"))) -- (/a. a) (/a. a)

-- Tests deDebruijn
test_deDeBruijn1 :: LT
test_deDeBruijn1 = deDeBruijn test_aDeBruijn1

test_deDeBruijn2 :: LT
test_deDeBruijn2 = deDeBruijn test_aDeBruijn2

test_deDeBruijn3 :: LT
test_deDeBruijn3 = deDeBruijn test_aDeBruijn3

-- Tests getHigherIndex
test_getHighestIndex1 :: Int
test_getHighestIndex1 = getHighestIndex test_aDeBruijn1

test_getHighestIndex2 :: Int
test_getHighestIndex2 = getHighestIndex test_aDeBruijn2

test_getHighestIndex3 :: Int
test_getHighestIndex3 = getHighestIndex test_aDeBruijn3

-- Tests Ord de LT
test_Ord1 :: Bool
test_Ord1 = defT <= defFact -- True

test_Ord2 :: Bool
test_Ord2 = defFact <= defT -- False

test_Ord3 :: Bool
test_Ord3 = defTupla <= defSuma -- True