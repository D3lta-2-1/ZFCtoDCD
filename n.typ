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

Pour pouvoir nommer les objets crées à l'aide de ces axiomes, il est nécessaire d'établir un résultat d'unicité. La plupart de ces preuves se rapportent à utiliser la définition pour faire apparaître l'axiome d'extensionnalité.


#proof("Unicité de l'ensemble vide",
  $exists! E, forall x, x in.not E$,
  [
    L'existence d'un tel ensemble est assuré par l'axime de l'ensemble vide\
    Posons $X$ et $Y$ deux ensembles vide\
    Alors $forall z, z in.not Y$ et $z in.not X$ \
    donc $forall z, (z in Y <=> z in X) $\
    Par l'axiome d'extensionnalité, $Y = X$, 
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
    Par l'axiome d'extensionnalité, P = Q
  ]
)
L'ensemble des parties d'un ensemble $E$ est unique, cet objet se note $cal(P)(E)$.


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
    Soient U, V tels que: 
    $ cases(
      forall x\, x in U <=> x in A or x in B,
      forall x\, x in V <=> x in A or x in B,
      )
    $
    Soit x,

    $ x in U &<=> x in A or x in B\
          &<=> x in V $
    Par l'axiome d'extensionnalité, U = V
  ]
)

Cet objet est noté $A union B$.\
Par définition, l'union "commute", c'est-à-dire: $A union B = B union A$\
\
On définit alors le successeur de n, l'operation utilisé dans l'axiome de l'infini, par l'operation suivante: $S(n) = n union {n}$

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
    Leur existence est assurée par le schéma d'axiome de compréhension. \ 
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

//todo*  : produit cartésien 
//todo**  : application

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
  $ forall F, (F subset E and F != emptyset) => exists m in F, forall x in F, m <= x $
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
//todo* : bon ordre implique ordre total.

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
      //todo* : récurrence sur b.
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

 Notons $<=$, relation sur N définie par : $ forall a in NN, forall b in NN, a<=b <=> a subset b $
On a déjà montré que $<=$ était une relation d'ordre.
#proof([Sur $NN$, $<=$ est une relation d'ordre totale.],
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
#proof("Lemme pour la propriété suivante",
    $forall n in NN, n  in.not n$, [
      On procède par récurrence. \
      $ emptyset in.not emptyset $\
      Soit $n in NN$. Supposons que $n in.not n$.\
      #h(1em) Supposons que $S(n) in S(n)$\
      #h(2em) $S(n) in n union {n}$\
      #h(2em) Si $S(n) =  n$ : $n in n$, c'est absurde. \
      #h(2em) Si $S(n) in n$ alors $ S(n) subset n$ d'où $n in n$, c'est absurde aussi.\
      #h(1em) Par l'absurde, $S(n) in.not S(n)$
    ]

 , )
#proof("Caractérisation de <",
 $forall a in NN, forall b in NN, a < b <=> a + 1 <= b$, 
 [
  //todo* : preuve (utiliser prop précédente pour avoir n != S(n))

 ])


//todo*** : construction des suites définies par récurrence.
//todo* : définition loi de composition interne ??
= Addition \

Soit $a in NN$. Posons :
$ f_a : cases(NN -> NN, b |-> f_(a)(b) ) $
Définie par :
$ cases(f_(a)(0) = a, forall b in NN\, f_(a)(S(b)) = S(f_(a)(b))) $.

Puis :
$ + : cases(NN times NN -> NN, (a\, b) |-> f_(a)(b) ) $
On notera : $+(a,b) = a + b$.

#proof("Propriétés fondamentales de l'addition",
  $(forall a in NN, a + 0 = a) and (forall a in NN, forall b in NN, S(a + b) = a + S(b))$,
  [
    Soit $a in NN$. $a + 0 = f_a(0) = a$\
    Soit $a in NN, b in NN$. $S(a + b) = S(f_(a)(b)) = f_(a)(S(b)) = a + S(b)$
  ]
)

#proof(
  "Associativité et commutativité de l'addition",[
    $forall a in NN, forall b in NN, forall c in NN, (a + b) + c = a + (b + c)$
    $forall a in NN, forall b in NN, a + b = b + a$
  ], [
    Récurrences //todo*** : voir multiplication si besoin.
  ]
)
On notera, pour a, b et c des entiers naturels $a + b + c = ( a + b ) + c = a + ( b+ c )$.\
On remarque que : $ forall n in NN, S(n) = S(n + 0) = n + S(0) = n + 1 $
Où $1 = S(0)$. On utilisera cette notation pour les récurrences notamment.

#proof(
  "Compatibilité de l'ordre avec l'addition",
  $forall a in NN, forall b in NN, forall c in NN, a <= b => a + c <= b + c$,
  [
    Soit $a, b$ des entiers naturels. O procède par récurrence sur $c$.\
    $ a <= b => a + 0 <= b + 0 $
    Soit $c in NN$. Supposons que $a <= b => a + c <= b +c$.\
    #h(1em) Supposons que $a <= b$.\
    #h(2em) $a  + c <= b + c$\  
    #h(2em) Soit $x in S(a+c)$. \
    #h(3em) Si $x in a + c$ alors $x in b + c$ donc $x in S(b+c)$. 
    #h(3em) Sinon $x = a + c = b + c in S(b +c)$
    #h(2em) $S(a + c) <= S(b + c)$  
  ]
)
 #proof("Caractérisation de la relation d'ordre", 
  $forall a in NN, forall b in NN, a <= b <=> exists c, a + c = b$,
  [
    //todo** : par l'absurde : récurrence sur c pour a + c < b
  ]
 )



#proof("Simplification de l'addition", 
  $forall a in NN, forall b in NN, forall c in NN, a + c = b + c => a = b$,
  [
    Soit $a, b, c in NN$. On raisonne par contraposée.\
    Supposons $a != b$. Ainsi, $a < b$ ou $b < a$.
    Par symétrie supposons que $(a < b)$. Ainsi, $(a + 1 <= b)$ donc $(a + c + 1 <= b + c)$ donc $(a + c < b + c)$ 
    donc $(a + c != b +c)$. 
  ]
)


#proof("L'inclusion est une relation de bon ordre sur les entiers naturels.",
$forall F, (F subset N and F != emptyset) => exists m in F, forall x in F, m <= x$
,
[
  //todo** : récurrence.
]
)

= Multiplication \

La méthode employée est similaire à celle pour l'addition.

// todo* : défnir mult en adaptant addition

#proof("propriétés fondamentales de la multiplication",
  $(forall a in NN, a times 0 = 0) and (forall a in NN, forall b in NN, a times (b+1) = (a times b) + a)$
  ,[
    //todo* : preuve, devrait découler de la définition.
  ]
)
#proof("0 est absorbant pour la multiplication",
  $forall n in NN, 0 times n = 0$,
  [
      On procède par récurrence sur $n$.\
      $0 times 0 = 0$\
      Soit $n in NN$ supposons que $0 times n = 0$ : 
      $ 0 times (n + 1) = (0 times n) + 0 =  0 + 0 = 0 $
  ]
)
#proof(
  "Commutativité de la multiplication",[
    $forall a in NN, forall b in NN, a times b = b times a$
  ], [
    On procède par récurrence sur $a$.\
    $forall b in NN b times 0 = 0 = 0 times b$.\
    Soit $a in NN$. Supposons que $forall b in NN, a times b = b times a$.\
    #h(1em) On procède par récurrence sur b pour montrer que $forall b in NN, (a+1)times b = b times (a+1)$.\
    #h(1em) $a times 0 = 0 = 0 times a$ \
    #h(1em) Soit $b in NN$. Supposons que $(a + 1) times b = b times (a + 1)$.
    $
      (a + 1) times (b + 1) 
        &= ((a  + 1) times b) + a + 1\
        &= (b times (a +1)) + a + 1\
        &= (b times a) + a + b +1\
        &= (a times b) + a + b +1\
        &= (a times (b +1)) + b + 1\
        &= ((b +1) times a) + (b + 1)\
        &= ((b + 1) times (a +1))
    $
    Ceci conclut la récurrence sur $b$ puis celle sur $a$.\
  ]
)

#proof(
  "Distributivité", 
  $forall a in NN, forall b in NN,forall n in NN,  n times (a + b) = n times a  + n times b $, 
  [
      Soit $a in NN, b in NN$. On procède par récurrence sur $n$. 
      //todo* : rédiger la récurrence
  ]
)


#proof(
  "Associativité de la multiplication",[
    $forall a in NN, forall b in NN, forall c in NN, (a times b) times c = a times (b times c)$
  ], 
  [
    Soit $a in NN, b in NN$. On procède par récurrence sur $c$.\
    $(a times b) times 0 = 0 = a times 0 = a times (b times 0)$\
    Soit $c in NN$. Supposons que $(a times b) times c = a times (b times c)$\
    $
      (a times b) times (c + 1)
          &=(a times b) times c + a times b\
          &= a times (b times c) + a times b\
          &= a times (b times c + b)\
          &= a times (b times (c + 1))
    $
  ]
  
)
