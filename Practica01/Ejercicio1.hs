-- Práctica01. Lógica Computacional.
-- Sara Doris Montes Incin.
-- Emmanuel Cruz Hernández.

{- 
  Función que calcula el resultado de la derivada
  f(x)=a(x^2)+bx+c.
  Recibe tres enteros a, b, c, x, respectivamente.
  Regresa el resultado de efectuar la operación
  con los valores dados.
-}
deriva:: Int -> Int -> Int -> Int -> Int
deriva a b c x = (2*a*x)+b

areaCilindro:: Float -> Float -> Float
areaCilindro r h =
        if (r<=0.0||h<=0.0) then 0.0 else 2*pi*r*(r+h)

volumenCilindro:: Float -> Float -> Float
volumenCilindro r h = if (r<=0.0||h<=0.0) then 0.0 else 2*pi*r*r*h

aplicaOperacion:: Char -> Int -> Int -> Int
aplicaOperacion 's' a b = a
aplicaOperacion 't' a b = b
aplicaOperacion 'a' a b = a + b
aplicaOperacion 'r' a b = a - b
aplicaOperacion 'p' a b = a * b
aplicaOperacion 'd' a b = div a b
aplicaOperacion 'e' a b = a^b

raizEntera:: Int -> Int
raizEntera a = floor . sqrt $ fromIntegral a

sumaNat:: Int -> Int
sumaNat 1 = 1
sumaNat n = n + sumaNat(n-1)

{-
  Función que calcula los elemtentos de tribonaccie dado 'n'.
  Recibe un entero 'n'.
  Regresa una lista con los elementos de tribonaccie de 0 a 'n'.
-}
tribonaccies:: Int -> [Int]
tribonaccies n = map tri [0,1..n]

{-
  Función que elimina los elmentos duplicados adyacentes.
  Recibe una lista de elementos tipo 'a'.
  Regresa una lista con los elementos adyacentes eliminados.
  NOTA: Agregamos la sigla 'Eq' para especificar que la función
  recibe cualquier lista de elementos de tipo 'a'.
-}
eliminaDup:: Eq a => [a] -> [a]
eliminaDup (x:xs)
	| length(x:xs) == 1 = (x:xs)
	| x == (xs)!!0 =  eliminaDup(xs)
	| otherwise = [x]++eliminaDup(xs)

reversa::  [a] -> [a]
reversa [] = []
reversa (x:xs) = reversa(xs) ++ [x] 

filtra :: (a -> Bool) -> [a] -> [a]  
filtra _ [] = []  
filtra p (x:xs)   
    | p x       = x : filtra p xs  
    | otherwise = filtra p xs 

{-
  Función crea pares ordenados, relación entre el número 
  de apariciones adyacentes de 'x' en la lista y el elemento 'x'.
  Recibe una lista de elementos de tipo 'a'.
  Regresa una lista de pares ordenados, del número de máximas apariciones
  adyacentes de un elemento con el elemento.
  NOTA: Agregamos la sigla 'Eq' para especificar que la función
  recibe cualquier lista de elementos de tipo 'a'.
-}
apariciones:: Eq a => [a] -> [(Int, a)]
apariciones []=[]
apariciones (x:xs) = deleteX (createList (x:xs) (x:xs)) (createList (x:xs) (x:xs))

lista :: [Float]
lista = [2**(x-1)-1| x<-[1..7]]

dos :: [(Int,Int)]
dos = [(x,y) | x <-[0..20], y <-[0..20],y==x+1, mod(x) 4==3]

{-
  Función auxiliar que calcula tribonaccie de un número n.
  Recibe n, el número a calcular tribonaccie.
  Regresa tribonaccie de n.
-}
tri:: Int -> Int
tri 0 = 0
tri 1 = 1
tri 2 = 1
tri n = tri(n-1) + tri(n-2) + tri(n-3)

{-
  Función auxilar que calcula las ocurrecias del primer
  elemento adyacentes al mismo, de una lista.
  Recibe una lista de elementos de tipo 'a'.
  Regresa el número de ocurrencias del primer elemento 
  adyacentes al mismo, de la lista.
  NOTA: Agregamos la sigla 'Eq' para especificar que la función
  recibe cualquier lista de elementos de tipo 'a'.
-}
apar:: Eq a => [a] -> Int
apar [] = 0
apar (x:xs)
        | length(x:xs)==1 = 1
        | length(x:xs)==2 && x==(xs)!!0 =2
        | x==(xs)!!0 = 1+apar(xs)
        | otherwise = 1

{-
  Función drop.
  Recibe un entero n que indica cuantos elemtos del comienzo de
  la lista se eliminan, así como la lista de tipo 'a'.
  Regresa una lista sin los primeros n elementos.
-}
borrar:: Eq a => Int -> [a] -> [a]
borrar _ [] = []
borrar 0 (x:xs) = (x:xs)
borrar n (x:xs) =  borrar (n-1) (xs)

{-
  Crea una lista de pares ordenados, de el número máximo de 
  ocurrencias de un elemento con el elemento.
  Recibe dos listas de tipo [a].
  Regresa una lista con los pares ordenados mencionados.
  NOTA: Esta función puede regresar elementos repetidos en la lista.
-}
createList:: Eq a => [a] -> [a] -> [(Int, a)]
createList (x:xs) [] = []
createList [] [] = []
createList (x:xs) (y:ys) = [(findN y 0 (x:xs), y)]
          ++createList (x:xs) (borrar (apar (y:ys)) (y:ys))

{-
  Elimina todos los elmentos 'a' duplicados en una lista
  dejando únicamente una presencia de a.
  Recibe el elemento 'a' a eliminar duplicados y dos listas
  de tipo 'a': donde se hará la búsqueda y la que se recorre.
  Regresa una lista con únicamente una presencia de 'a'.
-}
deleteRepeated:: Eq a => a -> [a] -> [a]
deleteRepeated e [] = [e]
deleteRepeated e (x:xs) = if e==x then deleteRepeated e (xs)
          else [x]++deleteRepeated e (xs)

{-
  Elimina todos los elmentos repetudos en una lista de tipo 'a'.
  Recibe dos listas de tipo 'a'. Una es sobre la que se efectuarán
  las eliminaciones y la segunda la auxiliar para recorrer.
  Regresa una lista sin alguno de sus elementos repetidos.
-}
deleteX:: Eq a => [a] -> [a] -> [a]
deleteX (x:xs) [] = (x:xs)
deleteX [] [] = []
deleteX (x:xs) (y:ys) =deleteX (deleteRepeated y (x:xs)) (ys)

{-
  Determina el número máximo de ocurrencias adyacentes de un elemento
  'a' en una lista.
  Recibe el elemento a determinar sus ocurrencias adyacentes; un entero n 
  que sumula un contador; y la lista donde buscar las ocurrencias.
  Regresa un entero que es el mayor número de ocurrencias adyacentes de 'a'.
-}
findN:: Eq a => a -> Int -> [a] -> Int
findN _ n [] = n
findN a n (x:xs)=if (a==x && (apar(x:xs))>n)
          then findN a (apar(x:xs)) (borrar (apar(x:xs)) (x:xs))
          else findN a n (borrar (apar(x:xs)) (x:xs))
