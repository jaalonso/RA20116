```{.isabelle}
chapter {* R2: Razonamiento sobre programas en Isabelle/HOL *}

theory R2_Razonamiento_automatico_sobre_programas
imports Main 
begin

declare [[names_short]]

text {* --------------------------------------------------------------- 
  Ejercicio 1.1. Definir la función
     sumaImpares :: nat ⇒ nat
  tal que (sumaImpares n) es la suma de los n primeros números
  impares. Por ejemplo,
     sumaImpares 5  =  25
  ------------------------------------------------------------------ *}

fun sumaImpares :: "nat ⇒ nat" where
  "sumaImpares n = undefined"

value "sumaImpares 5 = 25"

text {* --------------------------------------------------------------- 
  Ejercicio 1.2. Demostrar que 
     sumaImpares n = n*n
  ------------------------------------------------------------------- *}

lemma "sumaImpares n = n*n"
oops

text {* --------------------------------------------------------------- 
  Ejercicio 2.1. Definir la función
     sumaPotenciasDeDosMasUno :: nat ⇒ nat
  tal que 
     (sumaPotenciasDeDosMasUno n) = 1 + 2^0 + 2^1 + 2^2 + ... + 2^n. 
  Por ejemplo, 
     sumaPotenciasDeDosMasUno 3  =  16
  ------------------------------------------------------------------ *}

fun sumaPotenciasDeDosMasUno :: "nat ⇒ nat" where
  "sumaPotenciasDeDosMasUno n = undefined"

value "sumaPotenciasDeDosMasUno 3 = 16"

text {* --------------------------------------------------------------- 
  Ejercicio 2.2. Demostrar que 
     sumaPotenciasDeDosMasUno n = 2^(n+1)
  ------------------------------------------------------------------- *}

lemma "sumaPotenciasDeDosMasUno n = 2^(n+1)"
oops

text {* --------------------------------------------------------------- 
  Ejercicio 3.1. Definir la función
     copia :: nat ⇒ 'a ⇒ 'a list
  tal que (copia n x) es la lista formado por n copias del elemento
  x. Por ejemplo, 
     copia 3 x = [x,x,x]
  ------------------------------------------------------------------ *}

fun copia :: "nat ⇒ 'a ⇒ 'a list" where
  "copia n x = undefined"

value "copia 3 x = [x,x,x]"

text {* --------------------------------------------------------------- 
  Ejercicio 3.2. Definir la función
     todos :: ('a ⇒ bool) ⇒ 'a list ⇒ bool
  tal que (todos p xs) se verifica si todos los elementos de xs cumplen
  la propiedad p. Por ejemplo,
     todos (λx. x>(1::nat)) [2,6,4] = True
     todos (λx. x>(2::nat)) [2,6,4] = False
  Nota: La conjunción se representa por ∧
  ----------------------------------------------------------------- *}

fun todos :: "('a ⇒ bool) ⇒ 'a list ⇒ bool" where
  "todos p xs = undefined"

value "todos (λx. x>(1::nat)) [2,6,4] = True"
value "todos (λx. x>(2::nat)) [2,6,4] = False"

text {* --------------------------------------------------------------- 
  Ejercicio 3.3. Demostrar que todos los elementos de (copia n x) son
  iguales a x. 
  ------------------------------------------------------------------- *}

lemma "todos (λy. y=x) (copia n x)"
oops

text {* --------------------------------------------------------------- 
  Ejercicio 4.1. Definir, recursivamente y sin usar (@), la función
     amplia :: 'a list ⇒ 'a ⇒ 'a list
  tal que (amplia xs y) es la lista obtenida añadiendo el elemento y al
  final de la lista xs. Por ejemplo,
     amplia [d,a] t = [d,a,t]
  ------------------------------------------------------------------ *}

fun amplia :: "'a list ⇒ 'a ⇒ 'a list" where
  "amplia xs y = undefined"

value "amplia [d,a] t = [d,a,t]"

text {* --------------------------------------------------------------- 
  Ejercicio 4.2. Demostrar que 
     amplia xs y = xs @ [y]
  ------------------------------------------------------------------- *}

lemma "amplia xs y = xs @ [y]"
oops

end
```
