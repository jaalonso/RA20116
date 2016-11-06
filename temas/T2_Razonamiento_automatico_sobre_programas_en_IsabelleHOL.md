```{.isabelle}
chapter {* Tema 2: Razonamiento automático sobre programas en Isabelle/HOL *}

theory T2b_Razonamiento_automatico_sobre_programas_en_IsabelleHOL
imports Main 
begin

text {* 
  En este tema se demuestra con Isabelle las propiedades de los
  programas funcionales como se expone en el tema 8 del curso
  "Informática" que puede leerse en http://goo.gl/Imvyt *}

text {*
  Se usarán nombres cortos. *}
  
declare [[names_short]]

section {* Razonamiento ecuacional *}

text {* ----------------------------------------------------------------
  Ejemplo 1. Definir, por recursión, la función
     longitud :: 'a list ⇒ nat
  tal que (longitud xs) es la longitud de la listas xs. Por ejemplo,
     longitud [4,2,5] = 3
  ------------------------------------------------------------------- *}

fun longitud :: "'a list ⇒ nat" where
  "longitud []     = 0"
| "longitud (x#xs) = 1 + longitud xs"
   
value "longitud [4,2,5] = 3"

text {* --------------------------------------------------------------- 
  Ejemplo 2. Demostrar que 
     longitud [4,2,5] = 3
  ------------------------------------------------------------------- *}

lemma "longitud [4,2,5] = 3"
by simp

text {* --------------------------------------------------------------- 
  Ejemplo 3. Definir la función
     fun intercambia :: 'a × 'b ⇒ 'b × 'a
  tal que (intercambia p) es el par obtenido intercambiando las
  componentes del par p. Por ejemplo,
     intercambia (u,v) = (v,u)
  ------------------------------------------------------------------ *}

fun intercambia :: "'a × 'b ⇒ 'b × 'a" where
  "intercambia (x,y) = (y,x)"

value "intercambia (u,v) = (v,u)"

text {* --------------------------------------------------------------- 
  Ejemplo 4. (p.6) Demostrar que 
     intercambia (intercambia (x,y)) = (x,y)
  ------------------------------------------------------------------- *}

lemma "intercambia (intercambia (x,y)) = (x,y)"
by simp

text {* --------------------------------------------------------------- 
  Ejemplo 5. Definir, por recursión, la función
     inversa :: 'a list ⇒ 'a list
  tal que (inversa xs) es la lista obtenida invirtiendo el orden de los
  elementos de xs. Por ejemplo,
     inversa [a,d,c] = [c,d,a]
  ------------------------------------------------------------------ *}

fun inversa :: "'a list ⇒ 'a list" where
  "inversa []     = []"
| "inversa (x#xs) = inversa xs @ [x]"

value "inversa [a,d,c] = [c,d,a]"

text {* --------------------------------------------------------------- 
  Ejemplo 6. (p. 9) Demostrar que 
     inversa [x] = [x]
  ------------------------------------------------------------------- *}

lemma "inversa [x] = [x]"
by simp

section {* Razonamiento por inducción sobre los naturales *}

text {*
  [Principio de inducción sobre los naturales] Para demostrar una
  propiedad P para todos los números naturales basta probar que el 0
  tiene la propiedad P y que si n tiene la propiedad P, entonces n+1
  también la tiene.  
     ⟦P 0; ⋀n. P n ⟹ P (Suc n)⟧ ⟹ P m

  En Isabelle el principio de inducción sobre los naturales está
  formalizado en el teorema nat.induct y puede verse con
     thm nat.induct
*}

thm nat.induct

text {* --------------------------------------------------------------- 
  Ejemplo 7. Definir la función
     repite :: nat ⇒ 'a ⇒ 'a list
  tal que (repite n x) es la lista formada por n copias del elemento
  x. Por ejemplo, 
     repite 3 a = [a,a,a]
  ------------------------------------------------------------------ *}

fun repite :: "nat ⇒ 'a ⇒ 'a list" where
  "repite 0 x       = []"
| "repite (Suc n) x = x # (repite n x)"

value "repite 3 a = [a,a,a]"

text {* --------------------------------------------------------------- 
  Ejemplo 8. (p. 18) Demostrar que 
     longitud (repite n x) = n
  ------------------------------------------------------------------- *}

(* 1ª demostración (procedimental) *)  
lemma "longitud (repite n x) = n"
apply (induct n)
apply auto
done

(* 2ª demostración (declarativa) *)  
lemma "longitud (repite n x) = n"
by (induct n) auto

section {* Razonamiento por inducción sobre listas *}

text {*
  Para demostrar una propiedad para todas las listas basta demostrar
  que la lista vacía tiene la propiedad y que al añadir un elemento a
  una lista que tiene la propiedad se obtiene otra lista que también
  tiene la propiedad. 

  En Isabelle el principio de inducción sobre listas está formalizado
  mediante el teorema list.induct que puede verse con 
     thm list.induct
*}

thm list.induct

text {* --------------------------------------------------------------- 
  Ejemplo 9. Definir la función
     conc :: 'a list ⇒ 'a list ⇒ 'a list
  tal que (conc xs ys) es la concatención de las listas xs e ys. Por
  ejemplo, 
     conc [a,d] [b,d,a,c] = [a,d,b,d,a,c]
  ------------------------------------------------------------------ *}

fun conc :: "'a list ⇒ 'a list ⇒ 'a list" where
  "conc []     ys = ys"
| "conc (x#xs) ys = x # (conc xs ys)"

value "conc [a,d] [b,d,a,c] = [a,d,b,d,a,c]"

text {* --------------------------------------------------------------- 
  Ejemplo 10. (p. 24) Demostrar que 
     conc xs (conc ys zs) = (conc xs ys) zs
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
apply (induct xs) 
apply auto
done

(* 2ª demostración *)  
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
by (induct xs) auto

text {* --------------------------------------------------------------- 
  Ejemplo 11. Refutar que 
     conc xs ys = conc ys xs
  ------------------------------------------------------------------- *}

lemma "conc xs ys = conc ys xs"
quickcheck
oops

text {* Encuentra el contraejemplo, 
  xs = [a\<^isub>2]
  ys = [a\<^isub>1] *}

text {* --------------------------------------------------------------- 
  Ejemplo 12. (p. 28) Demostrar que 
     conc xs [] = xs
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "conc xs [] = xs"
apply (induct xs) 
apply auto
done

(* 2ª demostración *)  
lemma "conc xs [] = xs"
by (induct xs) auto

text {* --------------------------------------------------------------- 
  Ejemplo 13. (p. 30) Demostrar que 
     longitud (conc xs ys) = longitud xs + longitud ys
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "longitud (conc xs ys) = longitud xs + longitud ys"
apply (induct xs) 
apply auto
done

(* 2ª demostración *)  
lemma "longitud (conc xs ys) = longitud xs + longitud ys"
by (induct xs) auto

section {* Inducción correspondiente a la definición recursiva *}

text {* --------------------------------------------------------------- 
  Ejemplo 14. Definir la función
     coge :: nat ⇒ 'a list ⇒ 'a list
  tal que (coge n xs) es la lista de los n primeros elementos de xs. Por 
  ejemplo, 
     coge 2 [a,c,d,b,e] = [a,c]
  ------------------------------------------------------------------ *}

fun coge :: "nat ⇒ 'a list ⇒ 'a list" where
  "coge n []           = []"
| "coge 0 xs           = []"
| "coge (Suc n) (x#xs) = x # (coge n xs)"

value "coge 2 [a,c,d,b,e] = [a,c]"

text {* --------------------------------------------------------------- 
  Ejemplo 15. Definir la función
     elimina :: nat ⇒ 'a list ⇒ 'a list
  tal que (elimina n xs) es la lista obtenida eliminando los n primeros
  elementos de xs. Por ejemplo, 
     elimina 2 [a,c,d,b,e] = [d,b,e]
  ------------------------------------------------------------------ *}

fun elimina :: "nat ⇒ 'a list ⇒ 'a list" where
  "elimina n []           = []"
| "elimina 0 xs           = xs"
| "elimina (Suc n) (x#xs) = elimina n xs"

value "elimina 2 [a,c,d,b,e] = [d,b,e]"

text {* 
  La definición coge genera el esquema de inducción coge.induct:
     ⟦⋀n. P n []; 
      ⋀x xs. P 0 (x#xs); 
      ⋀n x xs. P n xs ⟹ P (Suc n) (x#xs)⟧
     ⟹ P n x

  Puede verse usando "thm coge.induct". *}

thm coge.induct

text {* --------------------------------------------------------------- 
  Ejemplo 16. (p. 35) Demostrar que 
     conc (coge n xs) (elimina n xs) = xs
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "conc (coge n xs) (elimina n xs) = xs"
apply (induct rule: coge.induct) 
apply auto
done

(* 2ª demostración *)  
lemma "conc (coge n xs) (elimina n xs) = xs"
by (induct rule: coge.induct) auto

section {* Razonamiento por casos *}

text {*
  Distinción de casos sobre listas:
  · El método de distinción de casos se activa con (cases xs) donde xs
    es del tipo lista. 
  · "case Nil" es una abreviatura de 
       "assume Nil: xs =[]".
  · "case Cons" es una abreviatura de 
       "fix ? ?? assume Cons: xs = ? # ??"
    donde ? y ?? son variables anónimas. *}

text {* --------------------------------------------------------------- 
  Ejemplo 17. Definir la función
     esVacia :: 'a list ⇒ bool
  tal que (esVacia xs) se verifica si xs es la lista vacía. Por ejemplo,
     esVacia []  = True
     esVacia [1] = False
  ------------------------------------------------------------------ *}

fun esVacia :: "'a list ⇒ bool" where
  "esVacia []     = True"
| "esVacia (x#xs) = False"

value "esVacia []  = True"
value "esVacia [1] = False"

text {* --------------------------------------------------------------- 
  Ejemplo 18 (p. 39) . Demostrar que 
     esVacia xs = esVacia (conc xs xs)
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "esVacia xs = esVacia (conc xs xs)"
apply (cases xs) 
apply auto
done

(* 2ª demostración *)  
lemma "esVacia xs = esVacia (conc xs xs)"
by (cases xs) auto

section {* Heurística de generalización *}

text {* 
  Heurística de generalización: Cuando se use demostración estructural,
  cuantificar universalmente las variables libres (o, equivalentemente,
  considerar las variables libres como variables arbitrarias). *}

text {* --------------------------------------------------------------- 
  Ejemplo 19. Definir la función
     inversaAc :: 'a list ⇒ 'a list
  tal que (inversaAc xs) es a inversa de xs calculada usando
  acumuladores. Por ejemplo, 
     inversaAc [a,c,b,e] = [e,b,c,a]
  ------------------------------------------------------------------ *}

fun inversaAcAux :: "'a list ⇒ 'a list ⇒ 'a list" where
  "inversaAcAux [] ys     = ys"
| "inversaAcAux (x#xs) ys = inversaAcAux xs (x#ys)"

fun inversaAc :: "'a list ⇒ 'a list" where
  "inversaAc xs = inversaAcAux xs []"

value "inversaAc [a,c,b,e] = [e,b,c,a]"

text {* --------------------------------------------------------------- 
  Ejemplo 20. (p. 44) Demostrar que 
     inversaAcAux xs ys = (inversa xs) @ ys
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma inversaAcAux_es_inversa:
  "inversaAcAux xs ys = (inversa xs)@ys"
apply (induct xs arbitrary: ys) 
apply auto
done

(* 2ª demostración *)  
lemma inversaAcAux_es_inversa:
  "inversaAcAux xs ys = (inversa xs)@ys"
by (induct xs arbitrary: ys) auto

text {* --------------------------------------------------------------- 
  Ejemplo 21. (p. 43) Demostrar que 
     inversaAc xs = inversa xs
  ------------------------------------------------------------------- *}

corollary "inversaAc xs = inversa xs"
by (simp add: inversaAcAux_es_inversa)

section {* Demostración por inducción para funciones de orden superior *}

text {* --------------------------------------------------------------- 
  Ejemplo 22. Definir la función
     sum :: nat list ⇒ nat
  tal que (sum xs) es la suma de los elementos de xs. Por ejemplo,
     sum [3,2,5] = 10
  ------------------------------------------------------------------ *}

fun sum :: "nat list ⇒ nat" where
  "sum []     = 0"
| "sum (x#xs) = x + sum xs"

value "sum [3,2,5] = 10"

text {* --------------------------------------------------------------- 
  Ejemplo 23. Definir la función
     map :: ('a ⇒ 'b) ⇒ 'a list ⇒ 'b list
  tal que (map f xs) es la lista obtenida aplicando la función f a los
  elementos de xs. Por ejemplo,
     map (λx. 2*x) [3,2,5] = [6,4,10]
  ------------------------------------------------------------------ *}

fun map :: "('a ⇒ 'b) ⇒ 'a list ⇒ 'b list" where
  "map f []     = []"
| "map f (x#xs) = (f x) # map f xs"

value "map (λx. 2*x) [3::nat,2,5] = [6,4,10]"

text {* --------------------------------------------------------------- 
  Ejemplo 24. (p. 45) Demostrar que 
     sum (map (λx. 2*x) xs) = 2 * (sum xs)
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "sum (map (λx. 2*x) xs) = 2 * (sum xs)"
apply (induct xs) 
apply auto
done

(* 2ª demostración *)  
lemma "sum (map (λx. 2*x) xs) = 2 * (sum xs)"
by (induct xs) auto

text {* --------------------------------------------------------------- 
  Ejemplo 25. (p. 48) Demostrar que 
     longitud (map f xs) = longitud xs
  ------------------------------------------------------------------- *}

(* 1ª demostración *)  
lemma "longitud (map f xs) = longitud xs"
apply (induct xs) 
apply auto
done

(* 2ª demostración *)  
lemma "longitud (map f xs) = longitud xs"
by (induct xs) auto

section {* Referencias *}

text {*
  · J.A. Alonso. "Razonamiento sobre programas" http://goo.gl/R06O3
  · G. Hutton. "Programming in Haskell". Cap. 13 "Reasoning about
    programms". http://bit.ly/1gMqK0X 
  · S. Thompson. "Haskell: the Craft of Functional Programming, 3rd
    Edition. Cap. 8 "Reasoning about programms". 
  · L. Paulson. "ML for the Working Programmer, 2nd Edition". Cap. 6. 
    "Reasoning about functional programs". http://bit.ly/1gMqFKI
*}

end
```
