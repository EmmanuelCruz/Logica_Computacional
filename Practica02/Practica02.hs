-- Practica02 - Lógica Computacional
-- Cruz Hernández Emmanuel
-- Martínez Hernández Luis Eduardo.
-- Montes Incin Sara Doris.

data Var = A|B|C|D|E|F|G|H|I|J|K|M|N|L|O|P|Q|R|S|T|U|V|W|X|Y|Z deriving (Show,Eq,Ord)
data Formula = Prop Var|Neg Formula|Formula :&: Formula|Formula :|: Formula|Formula :=>: Formula|Formula :<=>: Formula deriving (Show,Eq,Ord)

infixl 9 :&:
infixl 9 :|:
infixl 7 :=>:
infixl 8 :<=>:

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
	Funcion que niega una formula
	Recibe una formula,que es la formula que va a ser negada
	Regresa la misma formula pero negada
-}
negacion :: Formula -> Formula
negacion (Prop x)=Neg(Prop x)
negacion (Neg(Prop x))=(Prop x)
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
equivalencia (Prop x)=(Prop x)
equivalencia (Neg(Prop x))=(negacion(Prop x))
equivalencia (Neg(f))=(negacion(equivalencia(f)))
equivalencia (f1:&:f2)=equivalencia(f1):&:equivalencia(f2)
equivalencia (f1:|:f2)=equivalencia(f1):|:equivalencia(f2)
equivalencia (f1:=>:f2)=equivalencia(negacion(f1)):|:equivalencia(f2)
equivalencia (f1:<=>:f2)=equivalencia(f1:=>:f2):&:equivalencia(f2:=>:f1)

{-
	Funcion que sustituye variables proposicionales, en una
	formula
	Recibe una formula,de la cual queremos cambiar alguna variable
	proposicional,y una lista de tuplas,donde la primera entrada de la
	tupla es la variable que queremos cambiar, y la segunda tupla es
	el nuevo valor de la variable
	Regresa la misma formula excepto que con las variables que 
	estaban en la lista se cambiaron
-}

sustituye :: Formula -> [(Var,Var)] -> Formula
sustituye (Prop x) ((a,b):xs)=cambia (Prop x) ((a,b):xs)
sustituye (Neg f) ((x1,x2):xs) = negacion (sustituye f ((x1,x2):xs))
sustituye (f1 :&: f2) ((x1,x2):xs) = sustituye f1 ((x1,x2):xs) :&: sustituye f2 ((x1,x2):xs)
sustituye (f1 :|: f2) ((x1,x2):xs) = sustituye f1 ((x1,x2):xs) :|: sustituye f2 ((x1,x2):xs)
sustituye (f1 :=>: f2) ((x1,x2):xs) = sustituye f1 ((x1,x2):xs) :=>: sustituye f2 ((x1,x2):xs)
sustituye (f1 :<=>: f2) ((x1,x2):xs) = sustituye f1 ((x1,x2):xs) :<=>: sustituye f2 ((x1,x2):xs)  

{-
  Función que da la interpretación a verdadero o falso de una fórmula con
  un estado específico.
  Recibe una fórmula y una lista de parejas ordenadas de variables con
  estados (True y False)
  Regresa la evaluación de la fórmula con la información dada.
-}
interp :: Formula -> [(Var,Bool)] -> Bool
interp (Prop x) ((a,b):xs)=daValor (Prop x) ((a,b):xs)
interp (Neg(Prop x)) ((a,b):xs)=daValor (negacion(Prop x)) ((a,b):xs)
interp (f1:&:f2) ((a,b):xs)=daValor (f1:&:f2) ((a,b):xs)
interp (f1:|:f2) ((a,b):xs)=daValor (f1:|:f2) ((a,b):xs)
interp (f1:=>:f2) ((a,b):xs)=daValor (f1:=>:f2) ((a,b):xs)
interp (f1:<=>:f2) ((a,b):xs)=daValor (f1:<=>:f2) ((a,b):xs)

{-
  Función que convierte una fórmula a forma normal negativa.
  Recibe una fórmula.
  Regresa una fórmula en forma normal negativa.
-}
fnn:: Formula -> Formula
fnn (Prop x)=(Prop x)
fnn (Neg(Prop x))=(negacion(Prop x))
fnn (Neg(f))=negacion(equivalencia(f))
fnn (f1:&:f2)=equivalencia(f1:&:f2)
fnn (f1:|:f2)=equivalencia (f1:|:f2)
fnn (f1:=>:f2)=equivalencia (f1:=>:f2)
fnn (f1:<=>:f2)=equivalencia (f1:<=>:f2)

{-
  Función que convierte una formula a forma normal conjuntiva.
  Recibe una fórmula.
  Regrea una fórmula en forma normal conjuntiva.
-}
fnc:: Formula -> Formula
fnc (Prop x)=(Prop x)
fnc (Neg(Prop x))=(Neg(Prop x))
fnc (Neg(f))=fnc(fnn(negacion(f)))
fnc (f)=distributividad(fnn(f))


{-
	Funcion auxiliar que elimina los duplicados de una lista
	Recibe como parametro una lista, a la cual queremos eliminar
	sus duplicados
	Regresa la misma lista,pero sin duplicados
-}
eliminaDup :: (Eq a) => [a] -> [a]
eliminaDup (x:xs) = x : eliminaDup (filtra (/= x) xs)
eliminaDup [] = []

{-
	Funcion auxiliar que filtra los elementos de una lista
	dado que cumplan alguna condicion
	Recibe una funcion que regrese un valor booleano(la condicion)
	y una lista a la cual queremos filtrar
	Regresa una lista ya filtrada de los elementos de la original
	que cumplieron con la condicion
-}

filtra :: (a -> Bool) -> [a] -> [a]
filtra a [] = []	
filtra a (x:xs) =  if a x
	then [x] ++ filtra a xs 
	else filtra a xs

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
distributividad f = f

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
daValor (f1:&:f2) ((a,b):xs)=(daValor f1 ((a,b):xs))&&(daValor f2 ((a,b):xs))
daValor (f1:|:f2) ((a,b):xs)=(daValor f1 ((a,b):xs))||(daValor f2 ((a,b):xs))
daValor (f1:=>:f2) ((a,b):xs)=if (daValor f1 ((a,b):xs)) then not(daValor f1 ((a,b):xs))||(daValor f2 ((a,b):xs)) else True
daValor (f1:<=>:f2) ((a,b):xs)=(not(daValor f1 ((a,b):xs))||(daValor f2 ((a,b):xs)))&&(not(daValor f2 ((a,b):xs))||(daValor f1 ((a,b):xs)))


{-
	Funcion auxiliar que cambia la variable proposicional recibida
	con la primera entrada de la lista de tuplas
	Recibe una formula(Prop p) y una lista de tuplas,donde la primera entrada
	de las tuplas es la variable que queremos cambiar y la segunda es el valor por el 
	cual queremos cambiarlo
	Regresa la prop p con el nuevo valor que se definia en la lista de tuplas 
-}
cambia :: Formula->[(Var,Var)]->Formula
cambia (Prop y) [] = Prop y
cambia (Prop y) ((x1,x2):xs) = if x1 == y then Prop x2 else cambia (Prop y) xs
