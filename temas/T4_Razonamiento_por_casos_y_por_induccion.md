```{.isabelle}
chapter {* Tema 4: Razonamiento por casos y por inducción *}

theory T4_Razonamiento_por_casos_y_por_induccion
imports Main Parity
begin

text {*
  En este tema se amplían los métodos de demostración por casos y por
  inducción iniciados en el tema anterior.
*}

section {* Razonamiento por distinción de casos *}

subsection {* Distinción de casos booleanos *}

text {*
  Ejemplo de demostración por distinción de casos booleanos:
  Demostrar "¬A ∨ A".
*}

-- "La demostración estructurada es"
lemma "¬A ∨ A" 
proof cases
  assume "A" 
  then show "¬A ∨ A" ..
next
  assume "¬A" 
  then show "¬A ∨ A" ..
qed

text {*
  Comentarios de la demostración anterior:
  · "proof cases" indica que el método de demostración será por
    distinción de casos. 
  · Se generan 2 casos:
       1. ?P ⟹ ¬A ∨ A
       2. ¬?P ⟹ ¬A ∨ A
    donde ?P es una variable sobre las fórmulas.
  · (assume "A") indica que se está usando "A" en lugar de la variable
    ?P.
  · "then" indica usando la fórmula anterior.
  · ".." indica usando la regla lógica necesaria (las reglas lógicas se
    estudiarán en los siguientes temas).
  · "next" indica el siguiente caso (se puede observar cómo ha
    sustituido ¬?P por ¬A.
*}

-- "La demostración automática es"
lemma "¬A ∨ A" 
by auto

text {*
  Ejemplo de demostración por distinción de casos booleanos con nombres: 
  Demostrar "¬A ∨ A".
*}

-- "La demostración estructurada es"
lemma "¬A ∨ A" 
proof (cases "A")
  case True 
  then show "¬A ∨ A" ..
next
  case False 
  thus "¬A ∨ A" .. 
qed

text {*
  Comentarios sobre la demostración anterior:
  · (cases "A") indica que la demostración se hará por casos según los
    distintos valores de "A".
  · Como "A" es una fórmula, sus posibles valores son verdadero o falso.
  · "case True" indica que se está suponiendo que A es verdadera. Es
    equivalente a "assume A".
  · "case False" indica que se está suponiendo que A es falsa. Es
    equivalente a "assume ¬A".
  · En general, 
    · el método (cases F) es una abreviatura de la aplicación de la regla
         ⟦F ⟹ Q; ¬F ⟹ Q⟧ ⟹ Q  
    · La expresión "case True" es una abreviatura de F.
    · La expresión "case False" es una abreviatura de ¬F.
  · Ventajas de "cases" con nombre: 
    · reduce la escritura de la fórmula y
    · es independiente del orden de los casos.
*}

subsection {* Distinción de casos sobre otros tipos de datos *}

text {*
  Ejemplo de distinción de casos sobre listas: 
  Demostrar que la longitud del resto de una lista es la longitud de la
  lista menos 1. 
*}

-- "La demostración detallada es"
lemma "length (tl xs) = length xs - 1" 
proof (cases xs)
  assume "xs = []"
  then show "length (tl xs) = length xs - 1" by simp
next
  fix y ys
  assume "xs = y#ys"
  then show "length(tl xs) = length xs - 1" by simp 
qed

text {*
  Comentarios sobre la demostración anterior:
  · "(cases xs)" indica que la demostración se hará por casos sobre los
    posibles valores de xs.
  · Como xs es una lista, sus posibles valores son la lista vacía ([]) o
    una lista no vacía (de la forma (y#ys)).
  · Se generan 2 casos:
       1. xs = [] ⟹ length (tl xs) = length xs - 1
       2. ⋀a list. xs = a # list ⟹ length (tl xs) = length xs - 1
*}

-- "La demostración simplificada es"
lemma "length (tl xs) = length xs - 1" 
proof (cases xs)
  case Nil 
  then show ?thesis by simp
next
  case Cons 
  then show ?thesis by simp 
qed

text {*
  Comentarios sobre la dmostración anterior:
  · "case Nil" es una abreviatura de 
       "assume xs =[]".
  · "case Cons" es una abreviatura de 
       "fix y ys assume xs = y#ys"
  · ?thesis es una abreviatura de la conclusión del lema.
*}

-- "La demostración automática es"
lemma "length (tl xs) = length xs - 1" 
by auto

text {*
  Een el siguiente ejemplo vamos a demostrar una propiedad de la función
  drop que está definida en la teoría List de forma que (drop n xs) la
  lista obtenida eliminando en xs} los n primeros elementos. Su
  definición es la siguiente   
     drop_Nil:  "drop n []     = []" 
     drop_Cons: "drop n (x#xs) = (case n of 
                                    0 => x#xs | 
                                    Suc(m) => drop m xs)"
*}

text {*
  Ejemplo de análisis de casos:
  Demostrar que el resultado de eliminar los n+1 primeros elementos de
  xs es el mismo que eliminar los n primeros elementos del resto de xs.  
*}

-- "La demostración detallada es"
lemma "drop (n + 1) xs = drop n (tl xs)"
proof (cases xs)
  case Nil 
  then show ?thesis by simp
next
  case Cons 
  then show ?thesis by simp
qed

-- "La demostración automática es"
lemma "drop (n + 1) xs = drop n (tl xs)"
by (cases xs) auto

section {* Inducción matemática *}

text {*
  [Principio de inducción matemática]
  Para demostrar una propiedad P para todos los números naturales basta
  probar que el 0 tiene la propiedad P y que si n tiene la propiedad P,
  entonces n+1 también la tiene. 
     ⟦P 0; ⋀n. P n ⟹ P (Suc n)⟧ ⟹ P m

  En Isabelle el principio de inducción matemática está formalizado en
  el teorema nat.induct y puede verse con
     thm nat.induct
*}

text {*  
  Ejemplo de demostración por inducción: Usaremos el principio de
  inducción matemática para demostrar que 
     1 + 3 + ... + (2n-1) = n^2

  Definición. [Suma de los primeros impares] 
  (suma_impares n) la suma de los n números impares. Por ejemplo,
     suma_impares 3  =  9
*}

fun suma_impares :: "nat ⇒ nat" where
  "suma_impares 0 = 0" 
| "suma_impares (Suc n) = (2*(Suc n) - 1) + suma_impares n"

value "suma_impares 3"

text {*
  Ejemplo de demostración por inducción matemática:
  Demostrar que la suma de los n primeros números impares es n^2.
*}

-- "Demostración del lema anterior por inducción y razonamiento ecuacional"
lemma "suma_impares n = n * n"
proof (induct n)
  show "suma_impares 0 = 0 * 0" by simp
next
  fix n assume HI: "suma_impares n = n * n"
  have "suma_impares (Suc n) = (2 * (Suc n) - 1) + suma_impares n" 
    by simp
  also have "… = (2 * (Suc n) - 1) + n * n" using HI by simp
  also have "… = n * n + 2 * n + 1" by simp
  finally show "suma_impares (Suc n) = (Suc n) * (Suc n)" by simp
qed

-- "Demostración del lema anterior con patrones y razonamiento ecuacional"
lemma "suma_impares n = n * n" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n 
  assume HI: "?P n"
  have "suma_impares (Suc n) = (2 * (Suc n) - 1) + suma_impares n" 
    by simp
  also have "… = (2 * (Suc n) - 1) + n * n" using HI by simp
  also have "… = n * n + 2 * n + 1" by simp
  finally show "?P (Suc n)" by simp
qed

text {*
  Comentario sobre la demostración anterior:
  · Con la expresión
       "suma_impares n = n * n" (is "?P n")
    se abrevia "suma_impares n = n * n" como "?P n". Por tanto, 
       "?P 0"       es una abreviatura de "suma_impares 0 = 0 * 0"
       "?P (Suc n)" es una abreviatura de "suma_impares (Suc n) = (Suc n) * (Suc n)"
  · En general, cualquier fórmula seguida de (is patrón) equipara el
    patrón con la fórmula. 
*}

-- "La demostración usando patrones es"
lemma "suma_impares n = n * n" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n 
  assume "?P n"
  then show "?P (Suc n)" by simp
qed

-- "La demostración automática es"
lemma "suma_impares n = n * n"
by (induct n) auto

text {* 
  Ejemplo de definición con existenciales. 
  Un número natural n es par si existe un natural m tal que n=m+m.   
*}

definition par :: "nat ⇒ bool" where
  "par n ≡ ∃m. n=m+m"

text {* 
  Ejemplo de inducción y existenciales: 
  Demostrar que para todo número natural n, se verifica que n*(n+1) par. 
*}

-- "Demostración detallada por inducción"
lemma 
  fixes n :: "nat"
  shows "par (n*(n+1))"
proof (induct n)
  show "par (0*(0+1))" by (simp add: par_def)
next
  fix n 
  assume "par (n*(n+1))"
  then have "∃m. n*(n+1) = m+m" by (simp add:par_def)
  then obtain m where m: "n*(n+1) = m+m" ..
  then have "(Suc n)*((Suc n)+1) = (m+n+1)+(m+n+1)" by auto
  then have "∃m. (Suc n)*((Suc n)+1) = m+m" ..
  then show "par ((Suc n)*((Suc n)+1))" by (simp add:par_def)
qed

text {*
  Comentarios sobre la demostración anterior:
  · (fixes n :: "nat") es una abreviatura de "sea n un número natural".
*}

text {*
  En Isabelle puede demostrarse de manera más simple un lema equivalente
  usando en lugar de la función "par" la función "even" definida en la
  teoría Parity por
     even x ⟷ x mod 2 = 0"
*}

lemma 
  fixes n :: "nat"
  shows "even (n*(n+1))"
by auto

text {*
  Comentarios sobre la demostración anterior:
  · Para poder usar la función "even" de la librería Parity es necesario
    importar dicha librería. Por ello, antes del inicio de la teoría
    aparece 
       imports Main Parity
*}

text {*
  Para completar la demostración basta demostrar la equivalencia de las
  funciones "par" y "even". 
*}

lemma 
  fixes n :: "nat"
  shows "par n = even n"
proof - 
  have "par n = (∃m. n = m+m)" by (simp add:par_def)
  then show "par n = even n" by presburger
qed

text {*
  Comentarios sobre la demostración anterior:
  · "by presburger" indica que se use como método de demostración el
    algoritmo de decisión de la aritmética de Presburger.
*}

section {* Inducción estructural *}

text {*
  Inducción estructural:
  · En Isabelle puede hacerse inducción estructural sobre cualquier tipo
    recursivo.
  · La inducción matemática es la inducción estructural sobre el tipo de
    los naturales.
  · El esquema de inducción estructural sobre listas es
    · list.induct: ⟦P []; ⋀x ys. P ys ⟹ P (x # ys)⟧ ⟹ P zs
  · Para demostrar una propiedad para todas las listas basta demostrar
    que la lista vacía tiene la propiedad y que al añadir un elemento a una
    lista que tiene la propiedad se obtiene una lista que también tiene la
    propiedad. 
  · En Isabelle el principio de inducción sobre listas está formalizado
    mediante el teorema list.induct que puede verse con 
       thm list.induct
*}

text {*
  Concatenación de listas:
  En la teoría List.thy está definida la concatenación de listas (que
  se representa por @) como sigue
     append_Nil:  "[]@ys     = ys"
     append_Cons: "(x#xs)@ys = x#(xs@ys)"
*}

text {*
  Lema. [Ejemplo de inducción sobre listas]
  Demostrar que la concatenación de listas es asociativa.
*}

-- "La demostración estructurada es"
lemma conc_asociativa: "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  show "[] @ (ys @ zs) = ([] @ ys) @ zs"
  proof -
    have "[] @ (ys @ zs) = ys @ zs" by simp
    also have "… = ([] @ ys) @ zs" by simp
    finally show ?thesis .
  qed
next
  fix x xs
  assume HI: "xs @ (ys @ zs) = (xs @ ys) @ zs"
  show "(x#xs) @ (ys @ zs) = ((x#xs) @ ys) @ zs"
  proof -
    have "(x#xs) @ (ys @ zs) = x#(xs @ (ys @ zs))" by simp
    also have "… = x#((xs @ ys) @ zs)" using HI by simp
    also have "… = (x#(xs @ ys)) @ zs" by simp
    also have "… = ((x#xs) @ ys) @ zs" by simp
    finally show ?thesis .
  qed
qed

-- "La demostración automática es"
lemma conc_asociativa_1: "xs @ (ys @ zs) = (xs @ ys) @ zs"
by (induct xs) auto

text {* 
  Ejemplo de definición de tipos recursivos:
  Definir un tipo de dato para los árboles binarios.
*}

datatype 'a arbolB = Hoja "'a" 
                   | Nodo "'a" "'a arbolB" "'a arbolB"

text {* 
  Ejemplo de definición sobre árboles binarios:
  Definir la función "espejo" que aplicada a un árbol devuelve su imagen
  especular.  
*}

fun espejo :: "'a arbolB ⇒ 'a arbolB" where
  "espejo (Hoja x) = (Hoja x)"
| "espejo (Nodo x i d) = (Nodo x (espejo d) (espejo i))"

value "espejo (Nodo a (Nodo b (Hoja c) (Hoja d)) (Hoja e))"
-- "= Nodo a (Hoja e) (Nodo b (Hoja d) (Hoja c))"

text {* 
  Ejemplo de demostración sobre árboles binarios:
  Demostrar que la función "espejo" es involutiva; es decir, para
  cualquier árbol a, se tiene que 
     espejo(espejo(a)) = a.
*}

-- "La demostración estructurada es"
lemma espejo_involutiva:
  fixes a :: "'b arbolB" 
  shows "espejo (espejo a) = a" (is "?P a")
proof (induct a)
  fix x 
  show "?P (Hoja x)" by simp 
next
  fix x
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (Nodo x i d)" 
  proof -
    have "espejo(espejo(Nodo x i d)) = 
          espejo(Nodo x (espejo d) (espejo i))" by simp
    also have "… = Nodo x (espejo (espejo i)) (espejo (espejo d))" 
      by simp
    also have "… = Nodo x i d" using h1 h2 by simp 
    finally show ?thesis .
 qed
qed

text {*
  Comentarios sobre la demostración anterior:
  · (fixes a :: "'b arbolB") es una abreviatura de "sea a1 un árbol binario
    cuyos elementos son de tipo b". 
  · (induct a) indica que el método de demostración es por inducción
    en el árbol binario a.
  · Se generan dos casos:
    1. ⋀a. espejo (espejo (Hoja a)) = Hoja a
    2. ⋀a1 a2 a3. ⟦espejo (espejo a2) = a2; 
                   espejo (espejo a3) = a3⟧
                  ⟹ espejo (espejo (Nodo a1 a2 a3)) = Nodo a1 a2 a3
*}

-- "La demostración automática es"
lemma espejo_involutiva_1: 
  "espejo (espejo a ) = a"
by (induct a) auto

text {* 
  Ejemplo. [Aplanamiento de árboles]
  Definir la función "aplana" que aplane los árboles recorriéndolos en
  orden infijo.  
*}

fun aplana :: "'a arbolB ⇒ 'a list" where
  "aplana (Hoja x)     = [x]"
| "aplana (Nodo x i d) = (aplana i) @ [x] @ (aplana d)"

value "aplana (Nodo a (Nodo b (Hoja c) (Hoja d)) (Hoja e))"
-- "= [c, b, d, a, e]"

text {* 
  Ejemplo. [Aplanamiento de la imagen especular] Demostrar que
     aplana (espejo a) = rev (aplana a)
*}

-- "La demostración estructurada es"
lemma 
  fixes a :: "'b arbolB"
  shows "aplana (espejo a) = rev (aplana a)" (is "?P a")
proof (induct a)
  fix x
  show "?P (Hoja x)" by simp 
next
  fix x 
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  show "?P (Nodo x i d)" 
  proof -
    have "aplana (espejo (Nodo x i d)) = 
          aplana (Nodo x (espejo d) (espejo i))" by simp
    also have "… = (aplana(espejo d))@[x]@(aplana(espejo i))" by simp
    also have "… = (rev(aplana d))@[x]@(rev(aplana i))" 
      using h1 h2 by simp
    also have "… = rev((aplana i)@[x]@(aplana d))" by simp
    also have "… = rev(aplana (Nodo x i d))" by simp
    finally show ?thesis .
 qed
qed

-- "La demostración automática es"
lemma "aplana (espejo a) = rev (aplana a)"
by (induct a) auto

section {* Heurísticas para la inducción *}

text {*
  Definición. [Definición recursiva de inversa]
  (inversa xs) la inversa de la lista xs. Por ejemplo,
     inversa [a,b,c] = [c,b,a] 
*}

fun inversa :: "'a list ⇒ 'a list" where
  "inversa [] = []" 
| "inversa (x#xs) = (inversa xs) @ [x]"

value "inversa [a,b,c]"

text {* 
  Definición. [Definición de inversa con acumuladores]
  (inversaAc xs) es la inversa de la lista xs calculada con
  acumuladores. Por ejemplo,
     inversaAc [a,b,c]       = [c,b,a] 
     inversaAcAux [a,b,c] [] = [c,b,a] 
*}

fun inversaAcAux :: "'a list ⇒ 'a list ⇒ 'a list" where
  "inversaAcAux [] ys     = ys" 
| "inversaAcAux (x#xs) ys = inversaAcAux xs (x#ys)"

definition inversaAc :: "'a list ⇒ 'a list" where
  "inversaAc xs ≡ inversaAcAux xs []"

value "inversaAcAux [a,b,c] []"
value "inversaAc [a,b,c]"

text {* 
  Lema. [Ejemplo de equivalencia entre las definiciones]
  La inversa de [a,b,c] es lo mismo calculada con la primera definición
  que con la segunda.
*}

lemma "inversaAc [a,b,c] = inversa [a,b,c]"
by (simp add: inversaAc_def)

text {*
  Nota. [Ejemplo fallido de demostración por inducción]
  El siguiente intento de demostrar que para cualquier lista xs, se
  tiene que  "inversaAc xs = inversa xs" falla.
*}

lemma "inversaAc xs = inversa xs"
proof (induct xs)
  show "inversaAc [] = inversa []" by (simp add: inversaAc_def)
next
  fix a xs assume HI: "inversaAc xs = inversa xs"
  have "inversaAc (a#xs) = inversaAcAux (a#xs) []" 
    by (simp add: inversaAc_def)
  also have "… = inversaAcAux xs [a]" by simp
  also have "… = inversa (a#xs)"
  -- "Problema: la hipótesis de inducción no es aplicable."
oops

text {* 
  Nota. [Heurística de generalización]
  Cuando se use demostración estructural, cuantificar universalmente las 
  variables libres (o, equivalentemente, considerar las variables libres
  como variables arbitrarias).

  Lema. [Lema con generalización]
  Para toda lista ys se tiene 
     inversaAcAux xs ys = (inversa xs) @ ys
*}

-- "La demostración estructurada es"
lemma inversaAcAux_es_inversa:
  "inversaAcAux xs ys = (inversa xs)@ys"
proof (induct xs arbitrary: ys)
  show "⋀ys. inversaAcAux [] ys = (inversa [])@ys" by simp
next
  fix a xs 
  assume HI: "⋀ys. inversaAcAux xs ys = inversa xs@ys"
  show "⋀ys. inversaAcAux (a#xs) ys = inversa (a#xs)@ys"
  proof -
    fix ys
    have "inversaAcAux (a#xs) ys = inversaAcAux xs (a#ys)" by simp
    also have "… = inversa xs@(a#ys)" using HI by simp
    also have "… = inversa (a#xs)@ys" using [[simp_trace]] by simp 
    finally show "inversaAcAux (a#xs) ys = inversa (a#xs)@ys" by simp
  qed
qed

-- "La demostración automática es"
lemma inversaAcAux_es_inversa_1:
  "inversaAcAux xs ys = (inversa xs)@ys"
by (induct xs arbitrary: ys) auto

text {*
  Corolario.  Para cualquier lista xs, se tiene que
     inversaAc xs = inversa xs
*}

corollary "inversaAc xs = inversa xs"
by (simp add: inversaAcAux_es_inversa inversaAc_def)

text {*
  Nota. En el paso "inversa xs@(a#ys) = inversa (a#xs)@ys" se usan
  lemas de la teoría List. Se puede observar, insertano 
     using [[simp_trace]]
  entre la igualdad y by simp, que los lemas usados son 
  · List.append_simps_1: []@ys = ys
  · List.append_simps_2: (x#xs)@ys = x#(xs@ys)
  · List.append_assoc:   (xs @ ys) @ zs = xs @ (ys @ zs)
  Las dos primeras son las ecuaciones de la definición de append.

  En la siguiente demostración se detallan los lemas utilizados.
*}

lemma "(inversa xs)@(a#ys) = (inversa (a#xs))@ys"
proof -
  have "(inversa xs)@(a#ys) = (inversa xs)@(a#([]@ys))" 
    by (simp only: append.simps(1))
  also have "… = (inversa xs)@([a]@ys)" by (simp only: append.simps(2))
  also have "… = ((inversa xs)@[a])@ys" by (simp only: append_assoc)
  also have "… = (inversa (a#xs))@ys" by (simp only: inversa.simps(2))
  finally show ?thesis .
qed

section {* Recursión general. La función de Ackermann *}

text {* 
  El objetivo de esta sección es mostrar el uso de las definiciones
  recursivas generales y sus esquemas de inducción. Como ejemplo se usa la
  función de Ackermann (se puede consultar información sobre dicha función en
  http://en.wikipedia.org/wiki/Ackermann_function).

  Definición.  La función de Ackermann se define por
    A(m,n) = n+1,             si m=0,
             A(m-1,1),        si m>0 y n=0,
             A(m-1,A(m,n-1)), si m>0 y n>0
  para todo los números naturales. 

  La función de Ackermann es recursiva, pero no es primitiva recursiva. 
*}

fun ack :: "nat ⇒ nat ⇒ nat" where
  "ack 0       n       = n+1" 
| "ack (Suc m) 0       = ack m 1" 
| "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"

-- "Ejemplo de evaluación"
value "ack 2 3" (* devuelve 9 *)

text {*
  Esquema de inducción correspondiente a una función:
  · Al definir una función recursiva general se genera una regla de
    inducción. En la definición anterior, la regla generada es
    ack.induct: 
       ⟦⋀n. P 0 n; 
        ⋀m. P m 1 ⟹ P (Suc m) 0;
        ⋀m n. ⟦P (Suc m) n; P m (ack (Suc m) n)⟧ ⟹ P (Suc m) (Suc n)⟧
       ⟹ P a b
*}

text {*
  Ejemplo de demostración por la inducción correspondiente a una función:
  Demostrar que para todos m y n, A(m,n) > n.
*} 

-- "La demostración detallada es"
lemma "ack m n > n"
proof (induct m n rule: ack.induct)
  fix n
  show "ack 0 n > n" by simp
next
  fix m 
  assume "ack m 1 > 1"
  then show "ack (Suc m) 0 > 0" by simp
next  
  fix m n
  assume "n < ack (Suc m) n" and 
         "ack (Suc m) n < ack m (ack (Suc m) n)"
  then show "Suc n < ack (Suc m) (Suc n)" by simp
qed

text {*
  Comentarios sobre la demostración anterior:
  · (induct m n rule: ack.induct) indica que el método de demostración
    es el esquema de recursión correspondiente a la definición de 
    (ack m n).
  · Se generan 3 casos:
    1. ⋀n. n < ack 0 n
    2. ⋀m. 1 < ack m 1 ⟹ 0 < ack (Suc m) 0
    3. ⋀m n. ⟦n < ack (Suc m) n; 
              ack (Suc m) n < ack m (ack (Suc m) n)⟧
             ⟹ Suc n < ack (Suc m) (Suc n)
*}

-- "La demostración automática es"
lemma "ack m n > n"
by (induct m n rule: ack.induct) auto

section {* Recursión mutua e inducción *}

text {*
  Nota. [Ejemplo de definición de tipos mediante recursión cruzada]
  · Un árbol de tipo a es una hoja o un nodo de tipo a junto con un
    bosque de tipo a.
  · Un bosque de tipo a es el boque vacío o un bosque contruido añadiendo
    un árbol de tipo a a un bosque de tipo a.
*}

datatype 'a arbol = Hoja | Nodo "'a" "'a bosque"
     and 'a bosque = Vacio | ConsB "'a arbol" "'a bosque"

text {*
  Regla de inducción correspondiente a la recursión cruzada:
  La regla de inducción sobre árboles y bosques es arbol_bosque.induct:
     ⟦P1 Hoja; 
      ⋀x b. P2 b ⟹ P1 (Nodo x b); 
      P2 Vacio;
      ⋀a b. ⟦P1 a; P2 b⟧ ⟹ P2 (ConsB a b)⟧ 
     ⟹ P1 a ∧ P2 b
*}

text {* 
  Ejemplos de definición por recursión cruzada:
  · aplana_arbol a) es la lista obtenida aplanando el árbol a.   
  · (aplana_bosque b) es la lista obtenida aplanando el bosque b.   
  · (map_arbol a h) es el árbol obtenido aplicando la función h a
    todos los nodos del árbol a.   
  · (map_bosque b h) es el bosque obtenido aplicando la función h a
    todos los nodos del bosque b. 
*}

fun aplana_arbol :: "'a arbol ⇒ 'a list" and 
    aplana_bosque :: "'a bosque ⇒ 'a list" where
  "aplana_arbol Hoja = []"
| "aplana_arbol (Nodo x b) = x#(aplana_bosque b)"
| "aplana_bosque Vacio = []"
| "aplana_bosque (ConsB a b) = (aplana_arbol a) @ (aplana_bosque b)"

fun map_arbol :: "('a ⇒ 'b) ⇒ 'a arbol ⇒ 'b arbol" and
    map_bosque :: "('a ⇒ 'b) ⇒ 'a bosque ⇒ 'b bosque" where
  "map_arbol  f Hoja        = Hoja"
| "map_arbol  f (Nodo x b)  = Nodo (f x) (map_bosque f b)"
| "map_bosque f Vacio       = Vacio"
| "map_bosque f (ConsB a b) = ConsB (map_arbol f a) (map_bosque f b)"

text {*
  Ejemplo de demostración por inducción cruzada:
  Demostrar que:
  · aplana_arbol  (map_arbol  f a) = map f (aplana_arbol a)
  · aplana_bosque (map_bosque f b) = map f (aplana_bosque b)
*}

-- "La demostración detallada es"
lemma "aplana_arbol  (map_arbol  f a) = map f (aplana_arbol a)
     ∧ aplana_bosque (map_bosque f b) = map f (aplana_bosque b)"
proof (induct_tac a and b)
  show "aplana_arbol (map_arbol f Hoja ) = map f (aplana_arbol Hoja)" 
    by simp
next
  fix x b
  assume HI: "aplana_bosque (map_bosque f b) = map f (aplana_bosque b)"
  have "aplana_arbol (map_arbol f (Nodo x b)) = 
        aplana_arbol (Nodo (f x) (map_bosque f b))" by simp
  also have "… = (f x)#(aplana_bosque (map_bosque f b))" by simp
  also have "… = (f x)#(map f (aplana_bosque b))" using HI by simp
  also have "… = map f (aplana_arbol (Nodo x b))" by simp
  finally show "aplana_arbol (map_arbol f (Nodo x b))
                = map f (aplana_arbol (Nodo x b))" .
next
  show "aplana_bosque (map_bosque f Vacio) = map f (aplana_bosque Vacio)" 
    by simp
next
  fix a b
  assume HI1: "aplana_arbol (map_arbol f a) = map f (aplana_arbol a)"
     and HI2: "aplana_bosque (map_bosque f b) = map f (aplana_bosque b)"
  have "aplana_bosque (map_bosque f (ConsB a b)) = 
        aplana_bosque (ConsB (map_arbol f a) (map_bosque f b))" by simp
  also have "… = aplana_arbol(map_arbol f a)@aplana_bosque(map_bosque f b)" 
    by simp
  also have "… = (map f (aplana_arbol a))@(map f (aplana_bosque b))" 
    using HI1 HI2 by simp
  also have "… = map f (aplana_bosque (ConsB a b))" by simp
  finally show "aplana_bosque (map_bosque f (ConsB a b)) 
                = map f (aplana_bosque (ConsB a b))" by simp
qed

text {*
  Comentarios sobre la demostración anterior:
  · (induct_tac a and b) indica que el método de demostración es por
    inducción cruzada sobre a y b.
  · Se generan 4 casos:
    1. aplana_arbol (map_arbol arbol.Hoja h) = map h (aplana_arbol arbol.Hoja)
    2. ⋀a bosque.
          aplana_bosque (map_bosque bosque h) = map h (aplana_bosque bosque) ⟹
          aplana_arbol (map_arbol (arbol.Nodo a bosque) h) =
          map h (aplana_arbol (arbol.Nodo a bosque))
    3. aplana_bosque (map_bosque Vacio h) = map h (aplana_bosque Vacio)
    4. ⋀arbol bosque.
          ⟦aplana_arbol (map_arbol arbol h) = map h (aplana_arbol arbol);
           aplana_bosque (map_bosque bosque h) = map h (aplana_bosque bosque)⟧
          ⟹ aplana_bosque (map_bosque (ConsB arbol bosque) h) =
             map h (aplana_bosque (ConsB arbol bosque))
*}

-- "La demostración automática es"
lemma "aplana_arbol  (map_arbol  f a) = map f (aplana_arbol a)
     ∧ aplana_bosque (map_bosque f b) = map f (aplana_bosque b)"
by (induct_tac a and b) auto

end
```
