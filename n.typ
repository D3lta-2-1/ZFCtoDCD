#set text(
  lang: "fr"
)

#set heading(numbering: "1.")

#let proof(name, result, content) = {
  underline(text(name + ":"))
  linebreak()
  result
  linebreak()
  box(stroke: black,
    inset: 5pt,
    content
  )
  linebreak()
}



*Axiome:*
- axiome d'extensionnalité : $forall A, forall B, A = B <=> A subset B and B subset A$
- axiome de la paire : $forall a, forall b, exists E, forall x, x in E <=> x = a or x = b$
- axiome de réunion : $forall E, exists U, forall x, x in U <=> exists X in E, x in X$
- axiome des parties : $forall E, exists P, forall X, X in P <=> X subset E$
- axiome de l'infini : $exists I, emptyset in I and forall n, n in I => S(n) in I$
- axiome de compréhension (schéma) : $forall E, exists A, forall x, x in A <=> x in E and P(x)$
- axiome de l'ensemble de vide : $exists E, forall x, x in.not E$

= Résultats d'unicité

Rour pouvoir nommer les objets crées à l'aide de ces axiomes, il est nécessaire d'établir un résultat d'unicité. 


#proof("Unicité de l'ensemble vide",
  $exists! E, forall x, x in.not E$,
  [
    Posons $X$ un ensemble vide\
    Soit $Y slash forall y in Y, z in.not Y$ \
    Alors $forall y in Y, (y in Y <=> y in X) $\
    Par l'axiome d'exentsionalité, $Y = X$, 
  ] 
)

On note $emptyset$ l'ensemble vide.

#proof("Unicité de la paire",
  $forall a, forall b, exists! E, forall x, x in E <=> x = a or x = b$,
  [
    Soit  a, b. L'axiome de la paire donne l'existence d'un tel E, il reste à démontrer l'unicité. Soit E, F tels que :
    $forall x, x in E <=> x = a or x = b$\
    $forall x, x in F <=> x = a or x = b$\
    Soit $x in E$, $x = a or x = b$ donc $x in F$. Ainsi : $E subset F$. De même $F subset E$. Finalement, E = F, d'où l'unicité.
  ]
)

On note ${a, b}$ cet objet. Et, ${a, a}$ est noté ${a}$.

#proof("Unicité de l'ensemble des parties",
  $forall E, exists! P, forall X, X in P <=> X subset E$,
  [
    On fait de même pour avoir l'unicité, l'existence étant donnée par l'axiome des parties.
  ]
)
Cet objet est noté $cal(P)(e)$.


#proof("Uncité de la réunion",
  $forall E, exists! U, forall x, x in U <=> exists X in E, x in X$,
  [Même idée.]
)
Cet objet est noté $union.big_(X in E) X$ 

#proof("Unicité de la paire",
  $forall A, forall B, exists !E, forall x, x in E <=> x in A or x in B$,
  [
    Soit A, B. Posons $U = {A, B}$ puis $E  = union.big_(X in U) X$.
    Soit $x in E$. Par définition : $exists X in U, x in X$. Fixons un tel $X$.\
    Comme $x in U$ : $X  = A or X = B$ donc $x in A or x in B$.\ 
    Ainsi : $forall x, x in E => x in A or x in B$.\
    Réciproquement, soit $x in A$. Comme $A in U$, $exists X in U, x in X$. Ainsi, $x in E$. De même pour B.\
    Ainsi : $forall x, x in A or x in B => x in E$. D'où finalement l'existence. L'unicité se montre de la même manière que précédemmment.
  ]
  
)

Cet objet est noté $A union B$
On définit alors le successeur de n par l'operation suivante: $S(n) = n union {n}$
//todo  : Unicité pour schéma d'axiome de compréhension et notation 

= Construction de $bb(N)$
#let Pinf = $P_(infinity)$
On définit $Pinf$ par :
$ forall I, Pinf(I) <=>  emptyset in I and forall n, n in I => S(n) in I $\

$exists! N, (forall I, Pinf(I) => N subset I) and Pinf(N)$
// Preuve 
  Posons I tel que $Pinf(I)$, il nous est donné par l'axiome de l'infini.
Posons $N  = {n in I | forall J, Pinf(J) => n in J}$. Par construction, $forall J, Pinf(J) => N subset J$
Soit N, M vérifiants :\
$ (forall I, Pinf(I) => N subset I) and Pinf(N) $\
$ (forall I, Pinf(I) => M subset I) and Pinf(M) $\
On a alors : $N subset M and M subset N$, d'où $M = N$. On a ainsi l'unicité.
// Preuve
Cet objet est noté $bb(N)$


Récurrence :
Soit $P$ une propriété. 
$P(emptyset)  and (forall n in bb(N), P(n) => P(S(n)) => forall n in bb(N), P(n)$
//Preuve
Supposons $P(emptyset)  and (forall n in bb(N), P(n) => P(S(n)))$. Posons :
$ H = {n in bb(N) | P(n)} $. $P(emptyset)$ et $emptyset in N$ assurent que emptyset in H. Soit $n in H$. $P(n)$ et $n in bb(N)$. Ainsi, on a $P(S(n))$ et $S(n) in bb(N)$ d'où $S(n) in H$.\
On  a ainsi montré que $Pinf(H)$. Par définitions : $NN subset H et H subset  
//preuve


