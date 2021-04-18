-- Practica03 - Lógica Computacional
-- Cruz Hernández Emmanuel
-- Martínez Hernández union Eduardo.
-- Montes Incin Sara Doris.

data Var = A|B|C|D|E|F|G|H|I|J|K|M|N|L|O|P|Q|R|S|T|U|V|W|X|Y|Z deriving (Show,Eq,Ord)
data Formula = Prop Var|Neg Formula|Formula :&: Formula|Formula :|: Formula|Formula :=>: Formula|Formula :<=>: Formula deriving (Show,Eq,Ord)

infixl 9 :&:
infixl 9 :|:
infixl 7 :=>:
infixl 8 :<=>:

{- Función que da la tabla de verdad.
-}
tablaVerdad:: Formula -> [([(Var,Bool)], Bool)]
tablaVerdad (Prop x)=interpG (Prop x) (assign (varList(Prop x)) (giveValue(varList(Prop x))))
tablaVerdad (Neg(Prop x))=interpG (Neg(Prop x)) (assign (varList(Neg(Prop x))) (giveValue(varList(Neg(Prop x)))))
tablaVerdad (Neg(f))=interpG (Neg(f)) (assign (varList(Neg(f))) (giveValue(varList(Neg(f)))))
tablaVerdad (f1:&:f2)=interpG (f1:&:f2 ) (assign (varList(f1:&:f2)) (giveValue(varList(f1:&:f2))))
tablaVerdad (f1:|:f2)=interpG (f1:|:f2) (assign (varList(f1:|:f2)) (giveValue(varList(f1:|:f2))))
tablaVerdad (f1:=>:f2)=interpG (f1:=>:f2) (assign (varList(f1:=>:f2)) (giveValue(varList(f1:=>:f2))))
tablaVerdad (f1:<=>:f2)=interpG (f1:<=>:f2) (assign (varList(f1:<=>:f2)) (giveValue(varList(f1:<=>:f2))))

{- 
	Función que nos dice si una fórmula es tautología.
	Regresa True si es una tautología, False en otro caso.

-}
esTautologia:: Formula -> Bool
esTautologia (Prop x)=verificaT (tablaVerdad (Prop x))
esTautologia (Neg(Prop x))=verificaT (tablaVerdad (Neg(Prop x)))
esTautologia (Neg(f))=verificaT (tablaVerdad (Neg(f)))
esTautologia (f1:&:f2)=verificaT (tablaVerdad (f1:&:f2))
esTautologia (f1:|:f2)=verificaT (tablaVerdad (f1:|:f2))
esTautologia (f1:=>:f2)=verificaT (tablaVerdad (f1:=>:f2))
esTautologia (f1:<=>:f2)=verificaT (tablaVerdad (f1:<=>:f2))

{- 
	Función que nos dice si una fórmula es contradicción.
	Regresa True si es contradicción, False en otro caso.
-}
esContradicción:: Formula -> Bool
esContradicción (Prop x)=verificaC (tablaVerdad (Prop x))
esContradicción (Neg(Prop x))=verificaC (tablaVerdad (Neg(Prop x)))
esContradicción (Neg(f))=verificaC (tablaVerdad (Neg(f)))
esContradicción (f1:&:f2)=verificaC (tablaVerdad (f1:&:f2))
esContradicción (f1:|:f2)=verificaC (tablaVerdad (f1:|:f2))
esContradicción (f1:=>:f2)=verificaC (tablaVerdad (f1:=>:f2))
esContradicción (f1:<=>:f2)=verificaC (tablaVerdad (f1:<=>:f2))

{-
	Función que nos dice si una fórmula es satisfacible.
	Regresa True si es satisfacible, False en otro caso.
-}
esSatisfacible:: Formula -> Bool
esSatisfacible (Prop x)=verificaS (tablaVerdad (Prop x))
esSatisfacible (Neg(Prop x))=verificaS (tablaVerdad (Neg(Prop x)))
esSatisfacible (Neg(f))=verificaS (tablaVerdad (Neg(f)))
esSatisfacible (f1:&:f2)=verificaS (tablaVerdad (f1:&:f2))
esSatisfacible (f1:|:f2)=verificaS (tablaVerdad (f1:|:f2))
esSatisfacible (f1:=>:f2)=verificaS (tablaVerdad (f1:=>:f2))
esSatisfacible (f1:<=>:f2)=verificaS (tablaVerdad (f1:<=>:f2))

{-
	Función que calcule el conjunto S de cláusulas de una fórmula.
	Regresa una lista con las cláusulas.
-}
calculaS :: Formula -> [[Formula]]
calculaS f = calculaSA (fnc f)
       where calculaSA (Prop x) = [[Prop x]]
             calculaSA (Neg (Prop x)) = [[Neg(Prop x)]]
             calculaSA (Prop f1 :&: Prop f2) = [[Prop f1],[Prop f2]]
             calculaSA (Neg(Prop f1) :&: Prop f2) = [[Neg(Prop f1)],[Prop f2]]
             calculaSA (Neg(Prop f1) :&: Neg(Prop f2)) = [[Neg(Prop f1)],[Neg(Prop f2)]]
             calculaSA ((Prop f1) :&: Neg(Prop f2)) = [[(Prop f1)],[Neg(Prop f2)]]
             calculaSA (f1:&:f2) = calculaS(f1)++calculaS(f2)
             calculaSA f = [listUnion f]

{-
	Función que hace la resolución de dos cláusulas.
	Regresa la resolución.
-}
res:: [Formula] -> [Formula] -> [Formula]
res [] _ =[]
res _ [] = []
res (x:xs) (y:ys)= daResC (x:xs) (y:ys) (thisPR (x:xs) (y:ys))

{-
	Función que indica si se obtiene la cláusula vacía después de aplicar el algoritmo de saturación
	a un conjunto de cláusulas.
	Regresa True si encontró la vacía, False en otro caso.
-}
resolucionBinaria:: Formula -> Bool
resolucionBinaria f = alSat(calculaS(f))
resolucionBinaria (Neg(f))=alSat(calculaS(f))

{-
	Función que recibe un conjunto de premisas, una conclusión y nos dice si el argumento lógico
	es correcto.
	Regresa True si es correcto, False en otro caso.
	NOTA: Es el ejercicio 8, pero Haskell no permite repetir nombres.
-}
resolucionBinaria2:: [Formula] -> Formula -> Bool
resolucionBinaria2 (x:xs) f=alSat(calculaS((disyuncion(x:xs)))++calculaS(Neg(f)))
resolucionBinaria2 (x:xs) (Neg(f))=alSat(calculaS((disyuncion(x:xs)))++calculaS(f))

-----------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------
------------------------------------------------ FUNCIONES AUXILIARES -------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------


fnCo:: [[Formula]] -> Formula
fnCo [x] = union(x)
fnCo (x:xs) = union(x):&:fnCo(xs)

union:: [Formula] -> Formula
union [x]=x
union (x:xs) =  x :|: union(xs)

disyuncion:: [Formula] -> Formula
disyuncion [x] = x
disyuncion (x:xs) = x :&: disyuncion xs

sat:: [Formula] -> [[Formula]] -> [[Formula]]
sat _ [] = []
sat [] _ =[]
sat (x:xs) (y:ys)=if resRec (x:xs) y then [res (x:xs) y]++sat (x:xs) (ys) else sat (x:xs) (ys)

satAux::[[Formula]] -> [[Formula]] -> [[Formula]]
satAux [] _ =[]
satAux _ [] =[]
satAux (x:xs) (y:ys)=eliminaDup(sat x (y:ys) ++ satAux xs (y:ys))

alSatAux:: [[Formula]] -> [[Formula]] -> Int -> Bool
alSatAux _ _ 20 = False
alSatAux (x:xs) (y:ys) z =if isEmpty(satAux (x:xs) (y:ys)) then True else alSatAux ((satAux (x:xs) (y:ys))++(x:xs)) ((x:xs)) (z+1)

alSat:: [[Formula]] -> Bool
alSat [] = False
alSat (x:xs)= alSatAux (x:xs) (x:xs) (0)

isEmpty::[[Formula]] -> Bool
isEmpty [] = False
isEmpty (x:xs) = if x==[] then True else isEmpty xs

{--Metodo auxiliar(funciona) que te dice si en dos formulas hay almenos una
--literal y su complementaria
--como solo son clausulas,solo se cubren los casos de or,y Prop x
--} 
resAuxAux:: Formula -> [Formula] -> Bool
resAuxAux (Prop x) [y] = negacion(Prop x)==y
resAuxAux (Neg (Prop x)) [y] = (Prop x)==y
resAuxAux (Prop x) (y:ys) =if negacion(Prop x)==y then True else resAuxAux (Prop x) (ys)
resAuxAux (Neg (Prop x)) (y:ys) =if (Prop x)==y then True else resAuxAux (Neg(Prop x)) (ys)

resRec:: [Formula] -> [Formula] -> Bool
resRec [] _ = False
resRec _ [] = False
resRec (x:xs) (y:ys)=(resAuxAux x (y:ys))||(resRec xs (y:ys))

thisP:: Formula -> [Formula] -> [Formula]
thisP _ [] = []
thisP (Prop x) (y:ys) =if negacion(Prop x)==y then [Prop x] else thisP (Prop x) (ys)
thisP (Neg (Prop x)) (y:ys) =if (Prop x)==y then [Prop x] else thisP (Neg(Prop x)) (ys)

thisPR:: [Formula] -> [Formula] -> [Formula]
thisPR [] _ = []
thisPR _ [] = []
thisPR (x:xs) (y:ys)=(thisP x (y:ys))++(thisPR xs (y:ys))

daRes:: [Formula] -> [Formula] -> [Formula]
daRes [] _= []
daRes (x:xs) (y:ys)=if (y==x)||(y==negacion(x)) then daRes xs (y:ys) else [x]++daRes xs (y:ys)

daResC:: [Formula] -> [Formula] -> [Formula] -> [Formula]
daResC _ _ []=[]
daResC (x:xs) (y:ys) (z:zs) = eliminaDup((daRes (x:xs) (z:zs))++(daRes (y:ys) (z:zs)))

listUnion:: Formula -> [Formula]
listUnion (Prop x)=[Prop x]
listUnion (Neg(Prop x))=[Neg(Prop x)]
listUnion (f1 :|: f)=listUnion f1++listUnion f

combinations:: Int -> [[Bool]] -> [[Bool]]
combinations _ [] = []
combinations n (x:ys)=if length(x)==n then [x]
else combinations n [x++[False]] ++ combinations n [x++[True]] ++ combinations n ys

giveValue:: [Var] -> [[Bool]]
giveValue [] = []
giveValue (x:xs) = if length(x:xs)==1 then [[False],[True]]
                   else combinations (length(x:xs)) [[False],[True]]

assignP:: [Var] -> [Bool] -> [(Var,Bool)]
assignP [] [] = []
assignP (x:xs) (y:ys)=[(x,y)]++assignP xs ys 

assign:: [Var] -> [[Bool]] -> [[(Var,Bool)]]
assign _ [] = []
assign (x:xs) (y:ys) = [(assignP (x:xs) y)] ++ assign (x:xs) ys


interpG:: Formula -> [[(Var,Bool)]] -> [([(Var,Bool)], Bool)]
interpG _ []=[]
interpG (Prop y) (x:xs)=[(x,daValor (Prop y) x)]++interpG (Prop y) xs
interpG (Neg(Prop y)) (x:xs)=[(x,daValor (Neg(Prop y)) x)]++interpG (Neg(Prop y)) xs
interpG (Neg(f)) (x:xs)=[(x,daValor (Neg(f)) x)]++interpG (Neg(f)) xs
interpG (f1:&:f2) (x:xs)=[(x,daValor (f1:&:f2) x)]++interpG (f1:&:f2) xs
interpG (f1:|:f2) (x:xs)=[(x,daValor (f1:|:f2) x)]++interpG (f1:|:f2) xs
interpG (f1:=>:f2) (x:xs)=[(x,daValor (f1:=>:f2) x)]++interpG (f1:=>:f2) xs
interpG (f1:<=>:f2) (x:xs)=[(x,daValor (f1:<=>:f2) x)]++interpG (f1:<=>:f2) xs

verificaS:: [([(Var,Bool)], Bool)] -> Bool
verificaS [] = False
verificaS (((x:xs),z):ys)=if z then True else verificaS ys

verificaC:: [([(Var,Bool)], Bool)] -> Bool
verificaC [] = True
verificaC (((x:xs),z):ys)=if z then False else verificaC ys

verificaT:: [([(Var,Bool)], Bool)] -> Bool
verificaT [] = True
verificaT (((x:xs),z):ys)=if z then verificaT ys else False

{-
  Función auxiliar que asigna un valor, True o False, a una variable o fórmula.
  Recibe una fórmula y una lista de pares ordenados de variables con un valor booleano
  a asignar.
  Regresa la evaluación de la fórmula, True o False.
-}
daValor :: Formula -> [(Var,Bool)] -> Bool
daValor (Prop x) []= error "No todas las variables están definidas"
daValor (Prop x) ((a,b):xs)=if a==x then b else daValor (Prop x) xs
daValor (Neg(Prop x)) ((a,b):xs)=not (daValor (Prop x) ((a,b):xs))
daValor (Neg(f)) ((a,b):xs)=not (daValor (f) ((a,b):xs))
daValor (f1:&:f2) ((a,b):xs)=(daValor f1 ((a,b):xs))&&(daValor f2 ((a,b):xs))
daValor (f1:|:f2) ((a,b):xs)=(daValor f1 ((a,b):xs))||(daValor f2 ((a,b):xs))
daValor (f1:=>:f2) ((a,b):xs)=if (daValor f1 ((a,b):xs)) then not(daValor f1 ((a,b):xs))||(daValor f2 ((a,b):xs)) else True
daValor (f1:<=>:f2) ((a,b):xs)=(not(daValor f1 ((a,b):xs))||(daValor f2 ((a,b):xs)))&&(not(daValor f2 ((a,b):xs))||(daValor f1 ((a,b):xs)))

countVar:: Formula -> Int
countVar (Prop x) = length(varList (Prop x))
countVar (Neg f) =length(varList f)
countVar (f1 :&: f2) = length((varList(f1:&:f2)))
countVar (f1 :|: f2) = length((varList(f1:&:f2)))
countVar (f1 :=>: f2) = length((varList(f1:=>:f2)))
countVar (f1 :<=>: f2) = length((varList(f1:<=>:f2)))

{-
	Funcion que enlista todas las variables proposicionales
	de una formula
	Recibe como parametros una formula,de la cual se enlistaran
	sus variables
	Regresa una lista de todas las variables que contiene
	la formula
-}
varList :: Formula -> [Var]
varList (Prop x) = [x]
varList (Neg f) = eliminaDup(varList f)
varList (f1 :&: f2) = eliminaDup(varList f1 ++ varList f2)
varList (f1 :|: f2) = eliminaDup(varList f1 ++ varList f2)
varList (f1 :=>: f2) = eliminaDup(varList f1 ++ varList f2)
varList (f1 :<=>: f2) = eliminaDup(varList f1 ++ varList f2)

{-
	Funcion auxiliar que elimina los duplicados de una lista
	Recibe como parametro una lista, a la cual queremos eliminar
	sus duplicados
	Regresa la misma lista,pero sin duplicados
-}
eliminaDup :: (Eq a) => [a] -> [a]
eliminaDup (x:xs) = x : eliminaDup (filtra (/= x) xs)
eliminaDup [] = []

filtra :: (a -> Bool) -> [a] -> [a]
filtra a [] = []	
filtra a (x:xs) =  if a x
	then [x] ++ filtra a xs 
	else filtra a xs

{-
	Funcion que niega una formula
	Recibe una formula,que es la formula que va a ser negada
	Regresa la misma formula pero negada
-}
negacion :: Formula -> Formula
negacion (Prop x)=Neg(Prop x)
negacion (Neg(Prop x))=Prop x
negacion (Neg(f))=f
negacion (f1 :&: f2) = negacion f1 :|: negacion f2
negacion (f1 :|: f2) = negacion (f1) :&: negacion f2
negacion (f1 :=>: f2) = f1 :&: negacion f2
negacion (f1 :<=>: f2) = negacion (f1 :=>: f2) :|: negacion (f2 :=>: f1)

{-
  Función que elimina todas las presencias de implicaciones y equivalencias.
  Recibe una fórmula, en la que se eliminaran las presencias de equivalencia
  e implicación.
  Regresa una fórmula equivalente a la dada en los parámetros, pero sin
  implicaciones y equivalencias.
-}
equivalencia:: Formula -> Formula
equivalencia (Prop x)= Prop x
equivalencia (Neg(Prop x))=negacion(Prop x)
equivalencia (Neg(f))=negacion(equivalencia(f))
equivalencia (f1:&:f2)=equivalencia f1:&:equivalencia f2
equivalencia (f1:|:f2)=equivalencia f1:|:equivalencia f2
equivalencia (f1:=>:f2)=equivalencia(negacion(f1)):|:equivalencia f2 
equivalencia (f1:<=>:f2)=equivalencia(f1:=>:f2):&:equivalencia(f2:=>:f1)

{-
  Función que convierte una fórmula a forma normal negativa.
  Recibe una fórmula.
  Regresa una fórmula en forma normal negativa.
-}
fnn:: Formula -> Formula
fnn f = equivalencia(f)
fnn (Neg(f))=equivalencia(negacion(f))

{-
  Función que convierte una formula a forma normal conjuntiva.
  Recibe una fórmula.
  Regrea una fórmula en forma normal conjuntiva.
-}
fnc:: Formula -> Formula
fnc f = auxfnc (fnn f)
  where auxfnc (f1 :&: f2) = fnc f1 :&: fnc f2
        auxfnc (f1 :|: f2) = distributividad((fnc f1) :|: (fnc f2))
        auxfnc f = f

{-
  Función auxiliar que aplica la operación de distributividad a una fórmula,
  con el fin de que el o los operadores principales sean conjunciones..
  Recibe la fórmula a la que se aplicará distributividad.
  Regresa la fórmula resultante de aplicar distributividad.
-}
distributividad :: Formula->Formula
distributividad (Prop x)=Prop x
distributividad (Neg(Prop x))=negacion(Prop x)
distributividad (f1 :|: (f2 :&: f3)) = distributividad(((distributividad f1 :|: distributividad f2) :&: (distributividad f1 :|: distributividad f3)))
distributividad ((f2 :&: f3) :|: f1) =distributividad(((distributividad f2 :|: distributividad f1) :&: (distributividad f3 :|: distributividad f1)))
distributividad (f1 :&: f2) = distributividad f1 :&: distributividad f2
distributividad ((f1 :|: f2)) =  f1 :|: f2
distributividad f=f
