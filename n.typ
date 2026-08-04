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
- axiome d'extensionnalité : $forall A, forall B, A = B <=> A subset B and B subset A <=> forall x, [x in A <=> x in B] $
- axiome de la paire : $forall a, forall b, exists E, forall x, x in E <=> x = a or x = b$
- axiome de réunion : $forall E, exists U, forall x, x in U <=> exists X in E, x in X$
- axiome des parties : $forall E, exists P, forall X, X in P <=> X subset E$
- axiome de l'infini : $exists I, emptyset in I and forall n, n in I => S(n) in I$
- axiome de compréhension (schéma) : $forall E, exists A, forall x, x in A <=> x in E and P(x)$
- axiome de l'ensemble de vide : $exists E, forall x, x in.not E$

= Résultats d'unicités et opérations élémentaires.

Rour pouvoir nommer les objets crées à l'aide de ces axiomes, il est nécessaire d'établir un résultat d'unicité. La plupart de ces preuves se rapportent à utiliser la définition pour faire apparaître l'axiome d'extensionnalité.


#proof("Unicité de l'ensemble vide",
  $exists! E, forall x, x in.not E$,
  [
    L'existence d'un tel ensemble est assuré par l'axime de l'ensemble vide\
    Posons $X$ et $Y$ deux ensembles vide\
    Alors $forall z, z in.not Y$ et $z in.not X$ \
    donc $forall z, (z in Y <=> z in X) $\
    Par l'axiome d'extensionalité, $Y = X$, 
  ] 
)

On note $emptyset$ l'ensemble vide.

#proof("l'ensemble vide est inclus dans tout autre ensemble.",
  $forall E, forall x in emptyset, x in E $,
  [

    Soit $E$ un ensemble.\
    Raisonnons par contraposée:\
    $x in.not E => x in.not emptyset$ vrai car $forall x, x in.not emptyset$ \
    D'où $forall E, emptyset subset E$
  ] 
)

#proof("Unicité de la paire",
  $forall a, forall b, exists! E, forall x, x in E <=> x = a or x = b$,
  [
    Soit  a, b. L'axiome de la paire donne l'existence d'un tel E, il reste à démontrer l'unicité.\
     Soit E, F tels que : $ cases(
      forall x\, x in E <=> x = a or x = b,
      forall x\, x in F <=> x = a or x = b
      ) $\
    Soit $x in E$, $x = a or x = b$\ 
    donc $x in F$. 
    Ainsi : $E subset F$. De même $F subset E$. Finalement, E = F, d'où l'unicité.
  ]
)

On note ${a, b}$ cet objet. Et, ${a, a}$ est noté ${a}$.

#proof("Unicité de l'ensemble des parties",
  $forall E, exists! P, forall X, X in P <=> X subset E$,
  [
    Soit E un ensemble.
    Soit P, Q deux ensembles tels que: 
    $ cases(
      forall X\, X in P <=> X subset E,
      forall X\, X in Q <=> X subset E,
      )
    $
    Leur existence est assuré par l'axiome des parties. \ 
    Soit X
    $ X in P &<=> X subset E\
          &<=> X in Q $
    Par l'axiome d'extensionabilité, P = Q
  ]
)
L'ensemble des Parties d'un ensemble est unique, cet objet se note $cal(P)(e)$.


#proof("Uncité de la réunion",
  $forall E, exists! U, forall x, x in U <=> exists X in E, x in X$,
  [
    Soit U, V deux ensembles tel que:
    $ cases(
      forall x\, x in U <=> exists X in E\, x in X,
      forall x\, x in V <=> exists X in E\, x in X,
      )
    $
    Leur existence est assuré par l'axiome de réunion. \ 
    Soit $x$
    $
      x in U &<=> exists X in E\, x in X\
          &<=> X in V
    $
  ]
)
Cet objet est noté: $ union.big_(X in E) X $ 

#proof("Union de deux ensembles",
  $forall A, forall B, exists !E, forall x, x in E <=> x in A or x in B$,
  [
    Soit A, B.\
    Posons $U = $ puis $E  = union.big_(X in {A, B}) X$.\
    Soit $x in E$. Par définition : $exists X in U, x in X$. Fixons un tel $X$.\
    Comme $x in U$ : $X  = A or X = B$ donc $x in A or x in B$.\ 
    Ainsi : $forall x, x in E => x in A or x in B$.\
    Réciproquement, soit $x in A$. Comme $A in U$, $exists X in U, x in X$. Ainsi, $x in E$. De même pour B.\
    Ainsi : $forall x, x in A or x in B => x in E$.\
    \
    Soit U, V tel que: 
    $ cases(
      forall x\, x in U <=> x in A or x in B,
      forall x\, x in V <=> x in A or x in B,
      )
    $
    Soit x,

    $ x in U &<=> x in A or x in B\
          &<=> x in V $
    Par l'axiome d'extensionabilité, P = Q
  ]
)

Cet objet est noté $A union B$.\
Par définition, l'union "commute", c'est-à-dire: $A union B = B union A$\
\
On définit alors le successeur de n , l'operation utilisé dans l'axiome de l'infini, par l'operation suivante: $S(n) = n union {n}$

#proof("unicité d'un ensemble généré à l'aide d'un schéma de compréhension",
  $forall E, exists !A, forall x, x in A <=> x in E and P(x)$,
  [
    Soit P(x) un propriété, c'est-à-dire une formule propositionnelle de la logique classique.\
    Soit A, B deux ensembles tel que:
    $ cases(
      forall x\, x in A <=> x in E and P(x),
      forall x\, x in B <=> x in E and P(x),
      )
    $
    Leur existence est assuré par l'axiome de réunion. \ 
    Soit $x$
    $
      x in A &<=> x in E and P(x)
      &<=> X in B
    $
  ]
)

L'ensemble engendré à l'aide d'un schéma de compréhension par l'ensemble E et la propriété P est unique et se note $ { x in E slash P(x) }$.
Cela permet de définir l'intersection de la manière suivante: 
$ A inter B = { x in A slash x in B} $

#proof("l'intersection commute",
  $A inter B = B inter A$,
  [
    $
      x in A inter B &<=> x in { y in A slash y in B}\
      &<=> x in A and x in B "(défintion du schéma de compréhension)"\
      &<=> x in B and x in A "(commutativité du et en logique classique)"\
      &<=> x in { y in B slash y in A}\
      &<=> x in B inter A
    $
  ]
)

//todo  : produit cartésien 
//todo  : application

= Relations
Soit E. Une relation sur E est une application de $E times E$ dans ${0, 1}$ où $0 = emptyset$ et $1 = {emptyset}$. 
Soit $R$ une relation. On note : $forall a in E, forall b in E,  a R b <=>  R((a,b)) = 1  $.
Définissons plusieurs termes. Soit R une relation sur E. R est :\
  - Réflexive lorsque : $forall a in E, a R a $
  - Transitive lorsque : $forall a in E, forall b in E, forall c in E, (a R b and b R c) => a R c$
  - Symétrique lorsque : $forall a in E, forall b in E, a R b => b R a$
  - Antisymétrique lorsque : $forall a in E, forall b in E, (a R b and b R a) => a = b $\

Une relation d'ordre est une relation réflexive, transitive et antisymétrique.\
Une relation d'équivalence est une relation réflexive, symétrique et transitive.\
Une relation d'ordre $<=$ est dite totale sur un ensemble E lorsque :\
  $ forall a in E, forall b in E, a <= b or b <= a $ 
Un ordre sur E est un bon ordre lorque : \
  $ forall F, F subset E => exists m in F, forall x in F, m <= x $
  La relation R sur E définie par : $forall a in E, forall b in E, a R b <=> a subset b$ est notée $subset$.\
  De même la relation R définie par : $forall a in E, forall b in E, a R b <=> a = b$ est notée $=$.\

#proof(
  [L'inclusion est une relation d'ordre.],
  [], 
  [
    _Réflexive_ :
    Soit $A in E$. Soit $x in A$. $x in A$. Ainsi, $A subset A$ \  
    _Transitive_ :
    Soit $A, B$ et $C$ dans $E$. Supposons $A subset B$ et $B subset C$. Soit $x in A$. $x in B$. $x in C$.
     Ainsi,$A subset C$.
    _Antisymétrique_  :
    Soit $A, B in E$. Supposons $A subset B and B subset A$. Par axiome d'extensionnalité, $A = B$.
  ]



)
//todo : bon ordre implique ordre total.

= Construction de $bb(N)$
#let Pinf = $P_(infinity)$
On définit la propriété $Pinf$ par :
$ forall I, Pinf(I) <=>  emptyset in I and forall n, n in I => S(n) in I $\

#proof([Existence de $NN$],
  $exists! N, (forall I, Pinf(I) => N subset I) and Pinf(N)$,
  [
Posons I tel que $Pinf(I)$, il nous est donné par l'axiome de l'infini.
  Posons $N  = {n in I | forall J, Pinf(J) => n in J}$. Par construction, $forall J, Pinf(J) => N subset J$.
Soit N, M vérifiants :\
$ (forall I, Pinf(I) => N subset I) and Pinf(N) $\
$ (forall I, Pinf(I) => M subset I) and Pinf(M) $\
  On a alors : $N subset M and M subset N$, d'où $M = N$, d'où l'unicité.
  ]
  
)
Cet objet est noté $bb(N)$

#proof("Récurrence",
  [
    Soit $P$ une propriété. $P(emptyset)  and (forall n in bb(N), P(n) => P(S(n))) => forall n in bb(N), P(n)$
  ], 
  [
Supposons $P(emptyset)  and (forall n in bb(N), P(n) => P(S(n)))$. Posons :
    $ H = {n in bb(N) | P(n)} $ $P(emptyset)$ et $emptyset in N$ assurent que $emptyset$ in H. Soit $n in H$. $P(n)$ et $n in bb(N)$. Ainsi, on a $P(S(n))$ et $S(n) in bb(N)$ d'où $S(n) in H$.\
    On  a ainsi montré que $Pinf(H)$. Par définitions : $NN subset H and H subset NN$. Ainsi, $H = NN$ d'où la propriété.
  ]
  
)
#proof(
    "L'appartenance implique l'inclusion pour les entiers naturels",
    $forall a in NN, forall b in NN, a in b => a subset b$, [
      //todo : récurrence sur b.
    ]
)
 #proof(
    "Réciproque partielle",
    $forall a in NN, forall b in NN, a subset b => (a in b or a = b)$,
    [
        Soit $a in NN$.
        On procède par récurrence sur $b$.\
        Supposons $b = emptyset$ : $a subset b => a  = b => (a in b or a = b)$.\
        Soit $b in NN$.\
        Supposons que $(a subset b => (a in b or a = b))$.\
        #h(1em) Supposons $a subset S(b)$. $a subset b union {b}$.\
        #h(2em) Si $b in a$ : $b subset a$.\
        #h(3em) On a alors $S(b) subset a$ :\
        #h(4em) Soit $n in S(b)$. Si $n in b $ : $n in a$, sinon :  $n = b$, $n in a$ aussi.\
        #h(3em) Ainsi $a = S(b)$\
        #h(2em) Sinon : $a subset b$. Ainsi, $a in b or a = b$. Dans les deux cas $a in S(b)$\
        #h(1em) Finalement, $a subset S(b) => (a in S(b) or a = S(b))$\
        Par récurrence, la propriété est vraie pour tout $b in NN$.
    ]
 )

 Notons $<=$, relation sur N définie par : $ forall a in NN, forall b in NN, a<=b <=> a subset b $.
On a déjà montré que $<=$ était une relation d'ordre.
#proof(
  [Sur $NN$, $<=$ est une relation d'ordre totale.],
  [$forall a in NN, forall b in NN, a <=b or b <= a$],
  [
    Soit $a in NN$.
    On procède par récurrence sur $b$.\
    Si $b = emptyset$ : $b <= a$.\
    Soit $b in NN$. Supposons que $a<=b or b <= a$.\
    #h(1em) Si $a <= b$ :\
    #h(2em) $b subset b union {b} = S(b)$. On en déduit que $a <= S(b)$ par transitivité.\
    #h(1em) Si $b <= a$ : \
    #h(2em) $b in a or b = a$. \
    #h(2em) Si $b in a$ :\
    #h(3em) On a aussi : $b subset a$ donc $S(b) = b union {b} subset a$.\
    #h(2em) Si $b = a$ :\
    #h(3em) $a <= S(b)$\
    #h(1em) Dans tous les cas : $a <= S(b) or S(b) <= a$.\
  ]
)

//todo : construction des suites définies par récurrence.