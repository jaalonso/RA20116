```{.isabelle}
chapter {* Tema 3: Razonamiento estructurado sobre programas *}

theory T3_Razonamiento_sobre_programas
imports Main 
begin

text {* 
  En este tema se demuestra con Isabelle las propiedades de los
  programas funcionales como se expone en el tema 2a y se demostraron
  automáticamente en el tema 2b. A diferencia del tema 2b, ahora
  nos fijamos no sólo en el método de demostración sino en la estructura
  de la prueba resaltando su semejanza con las del tema 2a. *}

section {* Razonamiento ecuacional *}

text {* ----------------------------------------------------------------
  Ejemplo 1. Definir, por recursión, la función
     longitud :: 'a list ⇒ nat
  tal que (longitud xs) es la longitud de la listas xs. Por ejemplo,
     longitud [a,c,d] = 3
  ------------------------------------------------------------------- *}

fun longitud :: "'a list ⇒ nat" where
  "longitud []     = 0"
| "longitud (x#xs) = 1 + longitud xs"
   
value "longitud [a,c,d]" -- "= 3"

text {* --------------------------------------------------------------- 
  Ejemplo 2. Demostrar que 
     longitud [a,c,d] = 3
  ------------------------------------------------------------------- *}

lemma "longitud [a,c,d] = 3"
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

value "intercambia (u,v)" -- "= (v,u)"

text {*
  La definición de la función intercambia genera una regla de
  simplificación
  · intercambia.simps: intercambia (x,y) = (y,x)
  
  Se puede ver con 
  · thm intercambia.simps 
*}

text {* --------------------------------------------------------------- 
  Ejemplo 4. (p.6) Demostrar que 
     intercambia (intercambia (x,y)) = (x,y)
  ------------------------------------------------------------------- *}

(* Demostración aplicativa *)
lemma "intercambia (intercambia (x,y)) = (x,y)"
apply (simp only: intercambia.simps)
done

(* Demostración declarativa *)
lemma "intercambia (intercambia (x,y)) = (x,y)"
proof -
  have "intercambia (intercambia (x,y)) = intercambia (y,x)"  
    by (simp only: intercambia.simps)
  also have "... = (x,y)" 
    by (simp only: intercambia.simps)
  finally show "intercambia (intercambia (x,y)) = (x,y)" by simp
qed

text {*
  Notas sobre el lenguaje: En la demostración anterior se ha usado
  · "proof" para iniciar la prueba,
  · "-" (después de "proof") para no usar el método por defecto,
  · "have" para establecer un paso,
  · "by (simp only:  intercambia.simps)" para indicar que sólo se usa
    como regla de escritura la correspondiente a la definición de
    intercambia,
  · "also" para encadenar pasos ecuacionales,
  · "..." para representar la igualdad anterior en un razonamiento
    ecuacional,
  · "finally" para indicar el último pasa de un razonamiento ecuacional,
  · "show" para establecer la conclusión.
  · "by simp" para indicar el método de demostración por simplificación y 
  · "qed" para terminar la pruebas,
*}

(* Demostración declarativa simplificada *)
lemma "intercambia (intercambia (x,y)) = (x,y)"
proof -
  have "intercambia (intercambia (x,y)) = intercambia (y,x)"  by simp
  also have "... = (x,y)" by simp 
  finally show "intercambia (intercambia (x,y)) = (x,y)" by simp
qed

text {*
  Nota: La diferencia entre las dos demostraciones es que en los dos
  primeros pasos no se explicita la regla de simplificación.
*}

-- "La demostración automática es"
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

value "inversa [a,d,c]" -- "= [c,d,a]"

text {* --------------------------------------------------------------- 
  Ejemplo 6. (p. 9) Demostrar que 
     inversa [x] = [x]
  ------------------------------------------------------------------- *}

-- "La demostración aplicativa es"
lemma "inversa [x] = [x]"
apply simp
done

text {*
  En la demostración anterior se usaron las siguientes reglas:
  · inversa.simps(1): inversa [] = []
  · inversa.simps(2): inversa (x#xs) = inversa xs @ [x]
  · append_Nil:       [] @ ys = ys
  Vamos a explicitar su aplicación.
*}
  
-- "La demostración aplicativa detallada es"
lemma "inversa [x] = [x]"
apply (simp only: inversa.simps(2))
apply (simp only: inversa.simps(1))
apply (simp only: append_Nil)
done

-- "La demostración declarativa es"
lemma "inversa [x] = [x]"
proof -
  have "inversa [x] = inversa (x#[])" by simp
  also have "... = (inversa []) @ [x]" by (simp only: inversa.simps(2))
  also have "... = [] @ [x]" by (simp only: inversa.simps(1))
  also have "... = [x]" by (simp only: append_Nil) 
  finally show "inversa [x] = [x]" by simp
qed

-- "La demostración declarativa simplificada es"
lemma "inversa [x] = [x]"
proof -
  have "inversa [x] = inversa (x#[])" by simp
  also have "... = (inversa []) @ [x]" by simp
  also have "... = [] @ [x]" by simp
  also have "... = [x]" by simp 
  finally show "inversa [x] = [x]" by simp
qed

-- "La demostración automática es"
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

value "repite 3 a" -- "= [a,a,a]"

text {* --------------------------------------------------------------- 
  Ejemplo 8. (p. 18) Demostrar que 
     longitud (repite n x) = n
  ------------------------------------------------------------------- *}

-- "La demostración aplicativa es"
lemma "longitud (repite n x) = n"
apply (induct n)
apply auto
done

-- "La demostración estructurada es"
lemma "longitud (repite n x) = n"
proof (induct n)
  show "longitud (repite 0 x) = 0" by simp
next 
  fix n
  assume HI: "longitud (repite n x) = n"
  have "longitud (repite (Suc n) x) = longitud (x # (repite n x))" 
    by simp
  also have "... = 1 + longitud (repite n x)" by simp
  also have "... = 1 + n" using HI by simp
  finally show "longitud (repite (Suc n) x) = Suc n" by simp
qed

text {*
  Comentarios sobre la demostración anterior:
  · A la derecha de proof se indica el método de la demostración.
  · (induct n) indica que la demostración se hará por inducción en n.
  · Se generan dos subobjetivos correspondientes a la base y el paso de
    inducción:
    1. longitud (repite 0 x) = 0
    2. ⋀n. longitud (repite n x) = n ⟹ longitud (repite (Suc n) x) = Suc n
    donde ⋀n se lee "para todo n".  
  · "next" indica el siguiente subobjetivo.
  · "fix n" indica "sea n un número natural cualquiera"
  · assume HI: "longitud (repite n x) = n" indica «supongamos que 
    "longitud (repite n x) = n" y sea HI la etiqueta de este supuesto».
  · "using HI" usando la propiedad etiquetada con HI. 
*}

-- "La demostración automática es"
lemma "longitud (repite n x) = n"
by (induct n) auto

section {* Razonamiento por inducción sobre listas *}

text {*
  Para demostrar una propiedad para todas las listas basta demostrar
  que la lista vacía tiene la propiedad y que al añadir un elemento a una
  lista que tiene la propiedad se obtiene otra lista que también tiene la
  propiedad. 

  En Isabelle el principio de inducción sobre listas está formalizado
  mediante el teorema list.induct 
     ⟦P []; 
      ⋀x xs. P xs ⟹ P (x#xs)⟧ 
     ⟹ P xs
*}

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

value "conc [a,d] [b,d,a,c]" -- "= [a,d,b,d,a,c]"

text {* --------------------------------------------------------------- 
  Ejemplo 10. (p. 24) Demostrar que 
     conc xs (conc ys zs) = (conc xs ys) zs
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
proof (induct xs)
  show "conc [] (conc ys zs) = conc (conc [] ys) zs" by simp
next
  fix x xs
  assume HI: "conc xs (conc ys zs) = conc (conc xs ys) zs" 
  have "conc (x # xs) (conc ys zs) = x # (conc xs (conc ys zs))" by simp
  also have "... = x # (conc (conc xs ys) zs)" using HI by simp
  also have "... = conc (conc (x # xs) ys) zs" by simp
  finally show "conc (x # xs) (conc ys zs) = conc (conc (x # xs) ys) zs" by simp
qed

text {*
  Comentario sobre la demostración anterior
  · (induct xs) genera dos subobjetivos:
    1. conc [] (conc ys zs) = conc (conc [] ys) zs
    2. ⋀a xs. conc xs (conc ys zs) = conc (conc xs ys) zs ⟹
              conc (a#xs) (conc ys zs) = conc (conc (a#xs) ys) zs
*}

-- "La demostración automática es"
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
  xs = [a2]
  ys = [a1] *}

text {* --------------------------------------------------------------- 
  Ejemplo 12. (p. 28) Demostrar que 
     conc xs [] = xs
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma "conc xs [] = xs"
proof (induct xs)
  show "conc [] [] = []" by simp
next 
  fix x xs
  assume HI: "conc xs [] = xs" 
  have "conc (x # xs) [] = x # (conc xs [])" by simp
  also have "... = x # xs" using HI by simp
  finally show "conc (x # xs) [] = x # xs" by simp
qed

-- "La demostración automática es"
lemma "conc xs [] = xs"
by (induct xs) auto

text {* --------------------------------------------------------------- 
  Ejemplo 13. (p. 30) Demostrar que 
     longitud (conc xs ys) = longitud xs + longitud ys
  ------------------------------------------------------------------- *}

-- "La demostración automática es"
lemma "longitud (conc xs ys) = longitud xs + longitud ys"
proof (induct xs)
  show "longitud (conc [] ys) = longitud [] + longitud ys" by simp
next
  fix x xs
  assume HI: "longitud (conc xs ys) = longitud xs + longitud ys"
  have "longitud (conc (x # xs) ys) = longitud (x # (conc xs ys))" 
    by simp
  also have "... = 1 + longitud (conc xs ys)" by simp
  also have "... = 1 + longitud xs + longitud ys" using HI by simp
  also have "... = longitud (x # xs) + longitud ys" by simp
  finally show "longitud (conc (x # xs) ys) = 
                longitud (x # xs) + longitud ys" by simp
qed

-- "La demostración automática es"
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

value "coge 2 [a,c,d,b,e]" -- "= [a,c]"

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

value "elimina 2 [a,c,d,b,e]" -- "= [d,b,e]"

text {* 
  La definición coge genera el esquema de inducción coge.induct:
     ⟦⋀n. P n []; 
      ⋀x xs. P 0 (x#xs); 
      ⋀n x xs. P n xs ⟹ P (Suc n) (x#xs)⟧
     ⟹ P n x

  Puede verse usando "thm coge.induct". *}

text {* --------------------------------------------------------------- 
  Ejemplo 16. (p. 35) Demostrar que 
     conc (coge n xs) (elimina n xs) = xs
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma "conc (coge n xs) (elimina n xs) = xs"
proof (induct rule: coge.induct)
  fix n
  show "conc (coge n []) (elimina n []) = []" by simp
next
  fix x xs
  show "conc (coge 0 (x#xs)) (elimina 0 (x#xs)) = x#xs" by simp
next
  fix n x xs
  assume HI: "conc (coge n xs) (elimina n xs) = xs"
  have "conc (coge (Suc n) (x#xs)) (elimina (Suc n) (x#xs)) = 
        conc (x#(coge n xs)) (elimina n xs)" by simp
  also have "... = x#(conc (coge n xs) (elimina n xs))" by simp
  also have "... = x#xs" using HI by simp  
  finally show "conc (coge (Suc n) (x#xs)) (elimina (Suc n) (x#xs)) = 
                x#xs"
    by simp
qed

text {*
  Comentario sobre la demostración anterior:
  · (induct rule: coge.induct) indica que el método de demostración es
    por el esquema de inducción correspondiente a la definición de la
    función coge.
  · Se generan 3 subobjetivos:
    · 1. ⋀n. conc (coge n []) (elimina n []) = []
    · 2. ⋀x xs. conc (coge 0 (x#xs)) (elimina 0 (x#xs)) = x#xs
    · 3. ⋀n x xs. 
            conc (coge n xs) (elimina n xs) = xs ⟹
            conc (coge (Suc n) (x#xs)) (elimina (Suc n) (x#xs)) = x#xs
*}

-- "La demostración automática es"
lemma "conc (coge n xs) (elimina n xs) = xs"
by (induct rule: coge.induct) auto

section {* Razonamiento por casos *}

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

value "esVacia []"  -- "= True"
value "esVacia [1]" -- "= False"

text {* --------------------------------------------------------------- 
  Ejemplo 18 (p. 39) . Demostrar que 
     esVacia xs = esVacia (conc xs xs)
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma "esVacia xs = esVacia (conc xs xs)"
proof (cases xs)
  assume "xs = []"
  then show "esVacia xs = esVacia (conc xs xs)" by simp
next
  fix y ys
  assume "xs = y#ys"
  then show "esVacia xs = esVacia (conc xs xs)" by simp
qed

text {*
  Comentarios sobre la demostración anterior:
  · "(cases xs)" es el método de demostración por casos según xs.
  · Se generan dos subobjetivos  correspondientes a los dos
    constructores de listas:
    · 1. xs = [] ⟹ esVacia xs = esVacia (conc xs xs)
    · 2. ⋀y ys. xs = y#ys ⟹ esVacia xs = esVacia (conc xs xs)
  · "then" indica "usando la propiedad anterior"
*}

-- "La demostración estructurada simplificada es"
lemma "esVacia xs = esVacia (conc xs xs)"
proof (cases xs)
  case Nil
  then show "esVacia xs = esVacia (conc xs xs)" by simp
next
  case Cons
  then show "esVacia xs = esVacia (conc xs xs)" by simp
qed

text {*
  Comentarios sobre la demostración anterior:
  · "case Nil" es una abreviatura de "assume xs = []"
  · "case Cons" es una abreviatura de "fix y ys assume xs = y#ys"
  · "thus" es una abreviatura de "then show".
*}

-- "La demostración automática es"
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

value "inversaAc [a,c,b,e]" -- "= [e,b,c,a]"

text {* --------------------------------------------------------------- 
  Ejemplo 20. (p. 44) Demostrar que 
     inversaAcAux xs ys = (inversa xs) @ ys
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma inversaAcAux_es_inversa:
  "inversaAcAux xs ys = (inversa xs) @ ys"
proof (induct xs arbitrary: ys)
  show "⋀ys. inversaAcAux [] ys = inversa [] @ ys" by simp
next
  fix a xs 
  assume HI: "⋀ys. inversaAcAux xs ys = inversa xs@ys"
  show "⋀ys. inversaAcAux (a#xs) ys = inversa (a#xs)@ys"
  proof -
    fix ys
    have "inversaAcAux (a#xs) ys = inversaAcAux xs (a#ys)" by simp
    also have "… = inversa xs@(a#ys)" using HI by simp
    also have "… = inversa (a#xs)@ys" by simp 
    finally show "inversaAcAux (a#xs) ys = inversa (a#xs)@ys" by simp
  qed
qed

text {*
  Comentarios sobre la demostración anterior:
  · "(induct xs arbitrary: ys)" es el método de demostración por
    inducción sobre xs usando ys como variable arbitraria.
  · Se generan dos subobjetivos:
    · 1. ⋀ys. inversaAcAux [] ys = inversa [] @ ys
    · 2. ⋀a xs ys. (⋀ys. inversaAcAux xs ys = inversa xs @ ys) ⟹
                    inversaAcAux (a # xs) ys = inversa (a # xs) @ ys
  · Dentro de una demostración se pueden incluir otras demostraciones.
  · Para demostrar la propiedad universal "⋀ys. P(ys)" se elige una
    lista arbitraria (con "fix ys") y se demuestra "P(ys)". 
*}

-- "La demostración automática es"
lemma "inversaAcAux xs ys = (inversa xs)@ys"
by (induct xs arbitrary: ys) auto

text {* --------------------------------------------------------------- 
  Ejemplo 21. (p. 43) Demostrar que 
     inversaAc xs = inversa xs
  ------------------------------------------------------------------- *}

-- "La demostración automática es"
corollary "inversaAc xs = inversa xs"
by (simp add: inversaAcAux_es_inversa)

text {*
  Comentario de la demostración anterior:
  · "(simp add: inversaAcAux_es_inversa)" es el método de demostración
    por simplificación usando como regla de simplificación la propiedad
    inversaAcAux_es_inversa. 
*}

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

value "sum [3,2,5]" -- "= 10"

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

value "map (λx. 2*x) [3::nat,2,5]" -- "= [6,4,10]"

text {* --------------------------------------------------------------- 
  Ejemplo 24. (p. 45) Demostrar que 
     sum (map (λx. 2*x) xs) = 2 * (sum xs)
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma "sum (map (λx. 2*x) xs) = 2 * (sum xs)"
proof (induct xs)
  show "sum (map (λx. 2*x) []) = 2 * (sum [])" by simp
next
  fix a xs
  assume HI: "sum (map (λx. 2*x) xs) = 2 * (sum xs)"
  have "sum (map (λx. 2*x) (a#xs)) = sum ((2*a)#(map (λx. 2*x) xs))" 
    by simp
  also have "... = 2*a + sum (map (λx. 2*x) xs)" by simp
  also have "... = 2*a + 2*(sum xs)" using HI by simp
  also have "... = 2*(a + sum xs)" by simp
  also have "... = 2*(sum (a#xs))" by simp
  finally show "sum (map (λx. 2*x) (a#xs)) = 2*(sum (a#xs))" by simp
qed

-- "La demostración automática es"
lemma "sum (map (λx. 2*x) xs) = 2 * (sum xs)"
by (induct xs) auto

text {* --------------------------------------------------------------- 
  Ejemplo 25. (p. 48) Demostrar que 
     longitud (map f xs) = longitud xs
  ------------------------------------------------------------------- *}

-- "La demostración estructurada es"
lemma "longitud (map f xs) = longitud xs"
proof (induct xs)
  show "longitud (map f []) = longitud []" by simp
next
  fix a xs
  assume HI: "longitud (map f xs) = longitud xs"
  have "longitud (map f (a#xs)) = longitud (f a # (map f xs))" by simp
  also have "... = 1 + longitud (map f xs)" by simp
  also have "... = 1 + longitud xs" using HI by simp
  also have "... = longitud (a#xs)" by simp
  finally show "longitud (map f (a#xs)) = longitud (a#xs)" by simp
qed

-- "La demostración automática es"
lemma "longitud (map f xs) = longitud xs"
by (induct xs) auto

section {* Referencias *}

text {*
  · J.A. Alonso. "Razonamiento sobre programas" http://goo.gl/R06O3
  · G. Hutton. "Programming in Haskell". Cap. 13 "Reasoning about
    programms". 
  · S. Thompson. "Haskell: the Craft of Functional Programming, 3rd
    Edition. Cap. 8 "Reasoning about programms". 
  · L. Paulson. "ML for the Working Programmer, 2nd Edition". Cap. 6. 
    "Reasoning about functional programs". 
*}

end
```
