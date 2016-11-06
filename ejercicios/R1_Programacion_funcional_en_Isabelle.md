```{.isabelle}
chapter {* R1: Programación funcional en Isabelle *}

theory R1_Programacion_funcional_en_Isabelle
imports Main 
begin

text {* ----------------------------------------------------------------
  Ejercicio 1. Definir, por recursión, la función
     longitud :: 'a list ⇒ nat
  tal que (longitud xs) es la longitud de la listas xs. Por ejemplo,
     longitud [4,2,5] = 3
  ------------------------------------------------------------------- *}

fun longitud :: "'a list ⇒ nat" where
  "longitud xs = undefined"
   
value "longitud [4,2,5]" -- "= 3"

text {* --------------------------------------------------------------- 
  Ejercicio 2. Definir la función
     fun intercambia :: 'a × 'b ⇒ 'b × 'a
  tal que (intercambia p) es el par obtenido intercambiando las
  componentes del par p. Por ejemplo,
     intercambia (u,v) = (v,u)
  ------------------------------------------------------------------ *}

fun intercambia :: "'a × 'b ⇒ 'b × 'a" where
  "intercambia (x,y) = undefined"

value "intercambia (u,v)" -- "= (v,u)"

text {* ---------------------------------------------------------------
  Ejercicio 3. Definir, por recursión, la función
     inversa :: 'a list ⇒ 'a list
  tal que (inversa xs) es la lista obtenida invirtiendo el orden de los
  elementos de xs. Por ejemplo,
     inversa [a,d,c] = [c,d,a]
  ------------------------------------------------------------------ *}

fun inversa :: "'a list ⇒ 'a list" where
  "inversa xs = undefined"

value "inversa [a,d,c]" -- "= [c,d,a]"

text {* --------------------------------------------------------------- 
  Ejercicio 4. Definir la función
     repite :: nat ⇒ 'a ⇒ 'a list
  tal que (repite n x) es la lista formada por n copias del elemento
  x. Por ejemplo, 
     repite 3 a = [a,a,a]
  ------------------------------------------------------------------ *}

fun repite :: "nat ⇒ 'a ⇒ 'a list" where
  "repite n x = undefined"

value "repite 3 a" -- "= [a,a,a]"

text {* --------------------------------------------------------------- 
  Ejercicio 5. Definir la función
     conc :: 'a list ⇒ 'a list ⇒ 'a list
  tal que (conc xs ys) es la concatención de las listas xs e ys. Por
  ejemplo, 
     conc [a,d] [b,d,a,c] = [a,d,b,d,a,c]
  ------------------------------------------------------------------ *}

fun conc :: "'a list ⇒ 'a list ⇒ 'a list" where
  "conc xs ys = undefined"

value "conc [a,d] [b,d,a,c]" -- "= [a,d,b,d,a,c]"

text {* --------------------------------------------------------------- 
  Ejercicio 6. Definir la función
     coge :: nat ⇒ 'a list ⇒ 'a list
  tal que (coge n xs) es la lista de los n primeros elementos de xs. Por 
  ejemplo, 
     coge 2 [a,c,d,b,e] = [a,c]
  ------------------------------------------------------------------ *}

fun coge :: "nat ⇒ 'a list ⇒ 'a list" where
  "coge n xs = undefined"

value "coge 2 [a,c,d,b,e]" -- "= [a,c]"

text {* --------------------------------------------------------------- 
  Ejercicio 7. Definir la función
     elimina :: nat ⇒ 'a list ⇒ 'a list
  tal que (elimina n xs) es la lista obtenida eliminando los n primeros
  elementos de xs. Por ejemplo, 
     elimina 2 [a,c,d,b,e] = [d,b,e]
  ------------------------------------------------------------------ *}

fun elimina :: "nat ⇒ 'a list ⇒ 'a list" where
  "elimina n xs = undefined"

value "elimina 2 [a,c,d,b,e]" -- "= [d,b,e]"

text {* --------------------------------------------------------------- 
  Ejercicio 8. Definir la función
     esVacia :: 'a list ⇒ bool
  tal que (esVacia xs) se verifica si xs es la lista vacía. Por ejemplo,
     esVacia []  = True
     esVacia [1] = False
  ------------------------------------------------------------------ *}

fun esVacia :: "'a list ⇒ bool" where
  "esVacia xs = undefined"

value "esVacia []"  -- "= True"
value "esVacia [1]" -- "= False"

text {* --------------------------------------------------------------- 
  Ejercicio 9. Definir la función
     inversaAc :: 'a list ⇒ 'a list
  tal que (inversaAc xs) es a inversa de xs calculada usando
  acumuladores. Por ejemplo, 
     inversaAc [a,c,b,e] = [e,b,c,a]
  ------------------------------------------------------------------ *}

fun inversaAcAux :: "'a list ⇒ 'a list ⇒ 'a list" where
  "inversaAcAux xs ys = undefined"

fun inversaAc :: "'a list ⇒ 'a list" where
  "inversaAc xs = undefined"

value "inversaAc [a,c,b,e]" -- "= [e,b,c,a]"

text {* --------------------------------------------------------------- 
  Ejercicio 10. Definir la función
     sum :: nat list ⇒ nat
  tal que (sum xs) es la suma de los elementos de xs. Por ejemplo,
     sum [3,2,5] = 10
  ------------------------------------------------------------------ *}

fun sum :: "nat list ⇒ nat" where
  "sum xs = undefined"

value "sum [3,2,5]" -- "= 10"

text {* --------------------------------------------------------------- 
  Ejercicio 11. Definir la función
     map :: ('a ⇒ 'b) ⇒ 'a list ⇒ 'b list
  tal que (map f xs) es la lista obtenida aplicando la función f a los
  elementos de xs. Por ejemplo,
     map (λx. 2*x) [3,2,5] = [6,4,10]
  ------------------------------------------------------------------ *}

fun map :: "('a ⇒ 'b) ⇒ 'a list ⇒ 'b list" where
  "map f xs = undefined"

value "map (λx. 2*x) [3::nat,2,5]" -- "= [6,4,10]"

end
```
