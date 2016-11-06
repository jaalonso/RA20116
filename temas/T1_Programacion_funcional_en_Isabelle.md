```{.isa}
chapter {* Tema 1: Programación funcional en Isabelle *}

theory T1_Programacion_funcional_en_Isabelle
imports Main 
begin

section {* Introducción *}

text {* En este tema se presenta el lenguaje funcional que está
  incluido en Isabelle. El lenguaje funcional es muy parecido a
  Haskell. *}

section {* Números naturales, enteros y booleanos *}

text {* En Isabelle están definidos los número naturales con la sintaxis
  de Peano usando dos constructores: 0 (cero) y Suc (el sucesor).

  Los números como el 1 son abreviaturas de los correspondientes en la
  notación de Peano, en este caso "Suc 0". 

  El tipo de los números naturales es nat. 

  Por ejemplo, el siguiente del 0 es el 1. *}

value "Suc 0 = 1"  
(* ↝ "True" :: "bool"*)

text {* En Isabelle está definida la suma de los números naturales:
  (x + y) es la suma de x e y.

  Por ejemplo, la suma de los números naturales 1 y 2 es el número
  natural 3. *}

value "(1::nat) + 2" 
(* ↝ "Suc (Suc (Suc 0))" :: "nat" *)

value "(1::nat) + 2 = 3"
(* ↝ "True" :: "bool" *) 

text {* La notación del par de dos puntos se usa para asignar un tipo a
  un término (por ejemplo, (1::nat) significa que se considera que 1 es
  un número natural).   

  En Isabelle está definida el producto de los números naturales:
  (x * y) es el producto de x e y.

  Por ejemplo, el producto de los números naturales 2 y 3 es el número
  natural 6. *}

value "(2::nat) * 3" 
(* ↝ "Suc (Suc (Suc (Suc (Suc (Suc 0)))))" :: "nat"*)

value "(2::nat) * 3 = 6"
(* ↝ "True" :: "bool" *) 

text {* En Isabelle está definida la división de números naturales: 
  (n div m) es el cociente entero de x entre y.

  Por ejemplo, la división natural de 7 entre 3 es 2. *}

value "(7::nat) div 3"
(* ↝ "Suc (Suc 0)" :: "nat" *)

value "(7::nat) div 3 = 2"
(* ↝ "True" :: "bool" *)

text {* En Isabelle está definida el resto de división de números
  naturales: (n mod m) es el resto de dividir n entre m.

  Por ejemplo, el resto de dividir 7 entre 3 es 1. *}

value "(7::nat) mod 3"
(* ↝ "Suc 0" :: "nat" *)

text {* En Isabelle también están definidos los números enteros. El tipo
  de los enteros se representa por int.

  Por ejemplo, la suma de 1 y -2 es el número entero -1. *}

value "(1::int) + -2" -- "= -1" 
(* ↝ "- 1" :: "int"*)

text {* Los numerales están sobrecargados. Por ejemplo, el 1 puede ser
  un natural o un entero, dependiendo del contexto. 

  Isabelle resuelve ambigüedades mediante inferencia de tipos.

  A veces, es necesario usar declaraciones de tipo para resolver la
  ambigüedad.

  En Isabelle están definidos los valores booleanos (True y False), las
  conectivas (¬, ∧, ∨, ⟶ y ↔) y los cuantificadores (∀ y ∃). 

  El tipo de los booleanos es bool. *}

text {* La conjunción de dos fórmulas verdaderas es verdadera. *}
value "True ∧ True"  
(* ↝ "True" :: "bool" *)

text {* La conjunción de un fórmula verdadera y una falsa es falsa. *} 
value "True ∧ False"  
(* ↝ "False" :: "bool" *)

text {* La disyunción de una fórmula verdadera y una falsa es
  verdadera. *} 
value "True ∨ False" 
(* ↝ "True" :: "bool" *)

text {* La disyunción de dos fórmulas falsas es falsa. *}
value "False ∨ False" 
(* ↝ "False" :: "bool"*)

text {* La negación de una fórmula verdadera es falsa. *}
value "¬True" 
(* ↝ "False" :: "bool"*)

text {* Una fórmula falsa implica una fórmula verdadera. *}
value "False ⟶ True" 
(* ↝ "True" :: "bool"*)

text {* Un lema introduce una proposición seguida de una demostración. 

  Isabelle dispone de varios procedimientos automáticos para generar
  demostraciones, uno de los cuales es el de simplificación (llamado
  simp). 

  El procedimiento simp aplica un conjunto de reglas de reescritura, que
  inicialmente contiene un gran número de reglas relativas a los objetos
  definidos. *}

text {* Ej. de simp: Todo elemento es igual a sí mismo. *}
lemma "∀x. x = x" 
by simp

text {* Ej. de simp: Existe un elemento igual a 1. *}
lemma "∃x. x = 1" 
by simp

section {* Definiciones no recursivas *}

text {* La disyunción exclusiva de A y B se verifica si una es verdadera
  y la otra no lo es. *}

definition xor :: "bool ⇒ bool ⇒ bool" where
  "xor A B ≡ (A ∧ ¬B) ∨ (¬A ∧ B)"
  
text {* Prop.: La disyunción exclusiva de dos fórmulas verdaderas es
  falsa. 

  Dem.: Por simplificación, usando la definición de la disyunción
  exclusiva. 
*}

lemma "xor True True = False"
by (simp add: xor_def)

text {* Se añade la definición de la disyunción exclusiva al conjunto de
  reglas de simplificación automáticas. *}

declare xor_def [simp]

lemma "xor True False = True"
by simp

section {* Definiciones locales *}

text {* Se puede asignar valores a variables locales mediante 'let' y
  usarlo en las expresiones dentro de 'in'. 

  Por ejemplo, si x es el número natural 3, entonces "x*x = 9". *}

value "let x = 3::int in x * x" 
(* ↝ "9" :: "int" *)

section {* Pares *}

text {* Un par se representa escribiendo los elementos entre paréntesis
  y separados por coma.
  
  El tipo de los pares es el producto de los tipos.
  
  La función fst devuelve el primer elemento de un par y la snd el
  segundo. 

  Por ejemplo, si p es el par de números naturales (2,3), entonces la
  suma del primer elemento de p y 1 es igual al segundo elemento de
  p. *} 

value "let p = (2,3)::nat × nat in fst p + 1 = snd p" 
(* ↝ "True" :: "bool" *)

section {* Listas *}

text {* Una lista se representa escribiendo los elementos entre
  corchetes y separados por comas.
  
  La lista vacía se representa por [].
  
  Todos los elementos de una lista tienen que ser del mismo tipo.
  
  El tipo de las listas de elementos del tipo a es (a list).
  
  El término (x#xs) representa la lista obtenida añadiendo el elemento x
  al principio de la lista xs. 

  Por ejemplo, la lista obtenida añadiendo sucesivamente a la lista
  vacía los elementos z, y y x a es [x,y,z]. *}

value "x#(y#(z#[]))" 
(* ↝ "[x, y, z]" :: "'a list" *)

value "(1::int)#(2#(3#[]))"
(* ↝ "[1, 2, 3]" :: "int list" *)

text {* Funciones de descomposición de listas:
  · (hd xs) es el primer elemento de la lista xs.
  · (tl xs) es el resto de la lista xs.

  Por ejemplo, si xs es la lista [a,b,c], entonces el primero de xs es a
  y el resto de xs es [b,c]. *} 

value "let xs = [a,b,c] in hd xs = a ∧ tl xs = [b,c]" 
(* ↝ "True" :: "bool" *)

text {* (length xs) es la longitud de la lista xs. Por ejemplo, la
  longitud de la lista [1,2,5] es 3. *}

value "length [1,2,5]" 
(* ↝ "Suc (Suc (Suc 0))" :: "nat" *)

text {* En la página 8 de "What's in Main" http://bit.ly/2eyY0zI y 
  en la sesión 66 de "Isabelle/HOL — Higher-Order Logic"
  http://bit.ly/2eyYoy5 se encuentran más definiciones y propiedades de
  las listas. *}

section {* Funciones anónimas *}

text {* En Isabelle pueden definirse funciones anónimas.  

  Por ejemplo, el valor de la función que a un número le asigna su doble
  aplicada a 1 es 2. *}

value "(λx. x + x) 1::int" 
(* ↝ "2" :: "int" *)

section {* Condicionales *}

text {* El valor absoluto del entero x es x, si "x ≥ 0" y es -x en caso 
  contrario. *}

definition absoluto :: "int ⇒ int" where
  "absoluto x ≡ (if x ≥ 0 then x else -x)"

text {* Ejemplo, el valor absoluto de -3 es 3. *}

value "absoluto(-3)" 
(* ↝ "3" :: "int" *)

text {* Def.: Un número natural n es un sucesor si es de la forma 
  (Suc m). *}

definition es_sucesor :: "nat ⇒ bool" where
  "es_sucesor n ≡ (case n of 
    0     ⇒ False 
  | Suc m ⇒ True)"
  
text {* Ejemplo, el número 3 es sucesor. *}

value "es_sucesor 3" 
(* ↝ "True" :: "bool" *)

section {* Tipos de datos y definiciones recursivas *}

text {* Una lista de elementos de tipo a es la lista Vacia o se obtiene
  añadiendo, con Cons, un elemento de tipo a a una lista de elementos de
  tipo a. *} 

datatype 'a Lista = Vacia | Cons 'a "'a Lista"

text {* (conc xs ys) es la concatenación de las lista xs e ys. Por
  ejemplo, 
     conc (Cons a (Cons b Vacia)) (Cons c Vacia)
     = Cons a (Cons b (Cons c Vacia))
*}

fun conc :: "'a Lista ⇒ 'a Lista ⇒ 'a Lista" where
  "conc Vacia ys       = ys"
| "conc (Cons x xs) ys = Cons x (conc xs ys)"

value "conc (Cons a (Cons b Vacia)) (Cons c Vacia)"
(* ↝ Lista.Cons a (Lista.Cons b (Lista.Cons c Vacia)) *)

text {* Se puede declarar que acorte los nombres. *}

declare [[names_short]]

value "conc (Cons a (Cons b Vacia)) (Cons c Vacia)"
(* ↝ Cons a (Cons b (Cons c Vacia) *)

text {* (suma n) es la suma de los primeros n números naturales. Por
  ejemplo,
     suma 3 = 6
*}

fun suma :: "nat ⇒ nat" where
  "suma 0       = 0"
| "suma (Suc m) = (Suc m) + suma m"

value "suma 3" 
(* ↝ Suc (Suc (Suc (Suc (Suc (Suc 0)))) *)

text {* (sumaImpares n) es la suma de los n primeros números impares. 
  Por ejemplo, 
     sumaImpares 3 = 9
*}

fun sumaImpares :: "nat ⇒ nat" where
  "sumaImpares 0       = 0"
| "sumaImpares (Suc n) = (2 * (Suc n) - 1) + sumaImpares n"

value "sumaImpares 3" 
(* ↝ Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) *)

end
```
