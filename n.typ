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
//todo**  : application // ligne 465 : injective, surjective : peut être ramené ici
//todo* : image directe, image réciproque.

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
On a déjà montré que $<=$ était une relation d'ordre. \
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

= Cardinaux

Soient $E, F$ et. $f in F^E$  est dite :
- Injective lorsque : $forall x in E, forall x' in E, f(x) = f(x') => x = x'$.
- Surjective lorsque : $forall y in F, exists x in E, f(x) = y$
- Bijective lorsque $f$ est injective et surjective.

On notera :
- $E -> F$ lorqu'il existe une injection de E dans F.
- $E <-> F$ lorqu'il existe une bijection de E dans F.

#proof(
  [Transitivité de $->$.],$forall A, forall B, forall C, A->B and B->C => A -> C$ ,
   [
    Soient $A, B, C$. Supposons que $A->B$ et $B->C$. On dispose de $f in B^A$ et de $g in C^B$ injectives.
    Posons $h in C^A$ définie par  $h : x |-> g(f(x))$.\
    Soient $x in A$ et $x' in A$. Supposons que $h(x) = h(x')$. $g(f(x)) = g(f(x'))$ donc
    $f(x) = f(x')$ par injectivité de $g$ puis $x = x'$ par injectivité de $f$. 
    Ainsi, $h$ est injective donc $A->C$.
   ]
)
#proof(
  [Transitivité de $<->$.],$forall A, forall B, forall C, A<->B and B<->C => A <-> C$ ,
   [
    Soient $A, B, C$. Supposons que $A<->B$ et $B<->C$. On dispose de $f in B^A$ et de $g in C^B$ bijectives.
    Posons $h in C^A$ définie par  $h : x |-> g(f(x))$.\
    Injectivité de $h$ : \
    #h(1em) Soient $x in A$ et $x' in A$. Supposons que $h(x) = h(x')$. $g(f(x)) = g(f(x'))$ donc
    $f(x) = f(x')$ par injectivité de $g$ puis $x = x'$ par injectivité de $f$. 
    Surjectivité de $h$ : \
    #h(1em) Soit $z in C$. On dispose de $y in B$ tel que $g(y) = z$ par surjectivité de $g$.
    On dispose de $x in A$ tel que $y = f(x)$ par surjectivité de $f$. $h(x)=g(f(x)) = g(y) =z$
   ]
)
#proof(
  "Propriété" //pas d'idée de nom
  ,$forall A, forall B,  A<->B  => A -> B$ ,
   [
    Soient $A, B$. Supposons que $A <-> B$. On dispose alors de $f in B^A$ bijective. En particulier
    $f$ est injective donc $A->B$.
   ]
)

#proof(
  "Propriété" //pas d'idée de nom
  ,$forall A, forall B,  A subset B  => A -> B$ ,
   [
    Soient $A, B$. Supposons que $A subset B$. Posons alors $f in B^A$ définie par :
    $ f : x |-> x $
    $f$ est injective donc $A -> B$
   ]
)
#proof(
  "Caractérisation de la bijectivité.",
  [Soit $E, F$ et $f in F^E$. $f$ est bijective si et seulement si : 
    $ exists g in E^F, (forall x in E, g(f(x)) = x) and (forall y in F, f(g(y)) = y) $
    Dans ce cas, $g$ est unique.
  ],
  [
      Supposons que f est bijective. \
      Soit $y in F$. Montrons que : $exists ! x in E, f(x) = y$. \
      #h(1em) L'existence est donnée par la surjectivité de $f$. \
      #h(1em) L'unicité est donnée par l'injectivité. \
      On pose alors $g(y)$ cet unique élément $x$, ceci définit $g in E^F$.\
      Soit $y in F$. $f(g(y)) =  y$ par construction de $g$.\
      Soit $x in E$. $g(f(x))$ est tel que $f(g(f(x))) = f(x)$ puis, par injectivité de f : $g(f(x)) = x$.\
      Réciproquement, supposons l'existence de $g$ tel que : \
      $ (forall x in E, g(f(x)) = x) and (forall y in F, f(g(y)) = y) $
      Injectivité : \
      #h(1em) Soient $x in E, x' in E$. Supposons que $f(x) = f(x')$. Alors : $x = g(f(x)) = g(f(x')) = x'$ \
      Surjectivité : \
      #h(1em) Soit $y in F$. $f(g(y)) = y$. \ 
      Unicité de $g$ : \
      #h(1em) Supposons qu'il existe $g'$ vérifiant la même propriété. Soit $y in F$. $f(g'(y)) = y = f(g(y))$. \
      #h(1em) Par injectivité de $f$ : $g'(y) = g(y)$
  ]
)
On notera $g = f^(-1)$. Soient A, B; On note$A -> B$ ou $B <- A$ lorsqu'il existe une 
injection de A dans B et $A<->B$ lorsqu'il existe une bijection de A dans B. La propriété
précédente donne que $forall A, forall B, A<->B <=> B<->A$ \ // todo* : pas nécessaire 
#proof("Théorème de Cantor Bernstein",$forall A, forall B, A->B and B->A => A<->B$,
[
  Soient E, F supposons que : $F subset E and E -> F$. Montrons que $F <-> E$. Pour cela fixons $f in F^E$
  injective. Posons ensuite : 
  $ A_0 = E backslash F $
  $ forall n in NN, A_(n+1) = f(A_n) $
  C'est une suite définie par récurrence sur $cal(P)(E)$. On pose alors 
  $U = {X in cal(P)(E) : exists n in NN, X = A_n}$ que l'on notera plus simplement $U = {A_n | n in NN}$.
  On pose finalement : $ A = union.big_(X in U) X = union.big_(n in NN) A_n $ Finalement, définissons $g in F^E$ par :
  $ g : x |-> cases( f(x) "si" x in A, x "sinon") $
  Montrons que g est bijective : \
  Injectivité : \
  #h(1em) Soient $x, x'$ dans $E$. Supposons que $g(x) = g(x')$.\
  #h(2em) Si $x in A and x' in.not A$ : \
    $ f(x) = g(x) = g(x') = x' $
  #h(3em) On dispose de $n in NN$ tel que $x in A_n$ Ainsi, $x' = f(x) in A_(n+1)$ par contruction de $(A_n)$.
  On alors $x' in A$ ce qui est absurde. \
  #h(2em) Si $x in A and x' in A$ :
    $ f(x) = g(x) = g(x') = f(x') $
    $ x = x' "par injectivité" $
  #h(2em) Si $x in.not A and x' in.not A$ : 
    $ x = g(x) = g(x') = x' $
  #h(2em) Si $x in A and x' in.not A$ : \
  #h(3em) Symétrique du premier cas \
  Surjectivité : \
  #h(1em) Soit $y in F$.\
  #h(1em) Si $y in A$ : \
  #h(2em)  On dispose de $n in NN$ tel que $y in A_n$. \
  #h(2em) Si n < 1, $n in 1$ donc $n = 0$ donc $y in.not F$ : absurde \
  #h(2em) Si $n >= 1$ alors $n = k + 1$ avec $k in NN$ donc $A_n = f(A_k)$ ainsi $y in f(A_k)$. \
  #h(2em) On dispose alors de $x in A_k$ tel que $f(x) = y$.  $x in A$ par construction de $A$. Ainsi, $g(x)=f(x)=y $. \
  #h(1em) Si $y in.not A$ : g(y) = y. \
  On a ainsi montré que $E <-> F$.\

  Soient $A, B$. Supposons que $A->B$ et $B->A$. On dispose de $f in B^A$ injective. Posons $A' = f(A)$.
  $f$ est bijective de $A$ dans $A'$.// Il faudrait poser f' avec un ensemble d'arrivé restreint 
  Ainsi, $A <-> A'$. Mais $B->A$ et $A->A'$ car $A<->A'$, ainsi : $B->A'$.
  Comme $A' subset B$, $A' <-> B$ par la propriété précédente. Finalement, $A <-> B$ par transitivité. 
])
Soient $k in NN$ et $n in NN$. On note $[|k, n|] = {a in NN, k <= a <= n}$ \
#proof("Lemme", $forall A, forall x in A, forall y in A, A\\{x}<-> A\\{y}$,
 [
  Soit A. Soient $x in A$, $y in A$. Posons :
  $ f : A\\{x} & -> A\\{y} \ a &|-> cases(x "si" a = y, a "sinon")  $
  Injectivité : \
    #h(1em) Soient $a in A\\{x}$ et $a' in A\\{x}$. Supposons que $f(a) = f(a')$. \
    #h(2em) Si $a = y and a' = y$ : $a = y =  a'$ \
    #h(2em) Si $a != y and a' != y$ : $a = f(a) = f(a') = a'$ \
    #h(2em) Si $a = y and a' != y$ : $x = f(a) = f(a') = a'$, c'est absurde. \
    #h(2em) Si $a != y and a' = y$ : symétrique \
  Surjectivité : \
    #h(1em) Soit $b in A\\{y}$. \
    #h(2em) Si $b = x$ : $y != x$ donc $y in A\\{x}$. $f(y) = x = b$ \
    #h(2em) Si $b != x$ : $b in A\\{x}$. $f(b) = b$ 
  ])
#proof("Cas des entiers naturels",
  $forall a in NN, forall b in NN, [|1, a|] <-> [|1, b|] <=> a = b$,
  [
    Montrons tout d'abord que : \
    $ forall k in NN, k != 0 => forall n in NN, not ([|1, n|] <-> [|1, n + k|]) $ 
    Soit $k in NN$. Supposons que $k != 0$.\
    Initialisation : \
    #h(1em) $k > 0$, donc $k >= 1$. \
    #h(1em)  On en déduit que $1 in [|1, k|]$. \
    #h(1em)  Supposons que [|1, k|] <-> [|1, 0|]. Ainsi, on dispose de f bijective de $[|1, k|]$ dans $[|1, 0|]$.\
    $ f(1) in [|1, 0|] $
    $ f(1) <= 0 and f(1) >= 1 $
    $ 0 >= 1 $
    $ 0 = 1$
    #h(2em) C'est absurde donc  $not ([|1, 0|] <-> [|1, 0 + k|])$ \
    Hérédité : \
    #h(1em) Soit $n in NN$. Supposons que $not ([|1, n|] <-> [|1, n + k|])$. \
    #h(2em) Supposons que $[|1, n + 1|] <-> [|1, n + 1 + k|]$. \
    #h(3em) On dispose de $f : [|1, n + 1 |] ->[|1, n + 1 + k|]$ bijective. \
    #h(3em) Posons $ f' : [|1, n|] & -> [|1, n + 1 + k|]\\{f(n+1)} \ a &|-> f(a) $
    #h(3em)$f'$ est bien définie.\
    #h(3em) Comme $f$ est injective, $f'$ l'est aussi. \
    #h(3em) Montrons qu'elle est aussi surjective: \
    #h(4em) Soit $y in [|1, n + 1 + k|]\\{f(n+1)}$. \
    #h(4em) On dispose de $x in [|1, n+1|]$ tel que $f(x) =  y$.\
    #h(4em) Si $x = n + 1$, $y = f(n+1)$ : c'est absurde.\
    #h(4em) Sinon : $f'(x) = y$\
    $ [|1, n|] &<-> [|1, n + 1 + k|]\\{f(n+1)} \
               &<-> [|1, n + 1 + k|]\\{n+1+k} "lemme précédent"  \
               &<-> [|1, n + k|] 
        $
    #h(3em) C'est absurde. \
    #h(2em) Ainsi, $not ([|1, n + 1|] <-> [|1, n + 1 + k|])$
    \ \
    Soient $a in NN$ et $b in NN$. Supposons que $a != b$. Ainsi, $a < b$ ou $b < a$. Quitte
    à les renommer, on suppose que $a < b$. On dipose de $ k in NN$ tel que $a + k = b$ et $k !=0$.
    Ainsi, $not ([|1, a|] <-> [|1, a + k|] = [|1, b|])$. \
    La réciproque est évidente.
  ])
#proof("Définition du cardinal", 
$forall E, exists n in NN, E <-> [|1, n|] => exists! n in NN, E <-> [|1, n|]$,
[
  Soit $E$. Supposons que $exists n in NN, E <-> [|1, n|]$. Montrons l'unicité. \
  Soient $n in NN$ et $k in NN$. Supposons que $E <-> [|1, n|]$ et $E<->[|1, k|]$. \ 
  On a alors $[|1, n|] <-> [|1, k|]$ d'où $n = k$.
] )
Soit $E$. Dans le cas où $exists n in NN, E <-> [|1, n|]$, ce $n$ est unique et on le note  $\#E$.
$E$ est alors dit fini. Dans le cas contraire, il est infini. \ 
#let Pfin = $P_(< infinity)$
On note $Pfin$ la propriété d'être fini.\

#proof(
  "Caractérisation des ensembles infinis",
  $forall E, not Pfin(E) <=> forall n in NN, [|1, n|] -> E$ ,
  [
    Soit $E$. Supposons que $forall n in NN, [|1, n|] -> E$. \
    #h(1em) Supposons que $E$ est fini. \
    #h(2em) On dispose de $k in NN$ tel que $E <-> [|1, k|]$.\
    #h(2em) Ainsi, [|1, k +1|] -> E -> [|1, k|] -> [|1, k+1|]\
    #h(2em) C'est absurde car $k != k +1$. \
    #h(1em) Ainsi, $E$ est infini

    Réciproquement, soit $E$. Supposons que $E$ est infini. \
    On procède par récurrence.\
    #h(1em) $emptyset subset E$ donc $emptyset -> E$ donc $[|1, 0|] -> E$. \ 
    #h(1em) Soit $n in NN$. Supposons que $[|1, n|] -> E$. \
    #h(2em) On dispose de $f : [|1, n|] -> E$, injective. \
    #h(2em) $E$ est infini donc $f$ n'est pas surjective. On dipose ainsi de $y in E$ tel que :
    $ forall k in [|1, n|], f(k) != y $
    #h(2em)Posons alors :
    $ g : [|1, n+1|] &-> E\ k &|-> cases(f(k) "si" k <=n, y "sinon") $
    #h(2em) Montrons que $g$ est injective. \
    #h(2em) Soient $k, k'$ dans $[|1, n+1|]$. Supposons que $g(k) = g(k')$.\
    #h(3em) Si $k <= n$ and $k' = n +1$ : $f(k) != y = f(k')$ : impossible\
    #h(3em) Si $k = n +1$ and $k' <= n$ : symétrique du précédent\
    #h(3em) Si $k <= n$ and $k' <= n$ : $k = g(k) = g(k') = k'$\
    #h(3em) Si $k = n +1$ and $k' = n+1$ : $k = n+1 = k'$\
    #h(2em) Ainsi, $[|1, n + 1|] -> E$
  ]
)
#proof("Outil pour montrer qu'un ensemble est fini", //pas sûr du nom
  $forall E, (exists n in NN, E -> [|1, n|]) => Pfin(E)$,
  [
      Soit E. Supposons qu'il existe $n in NN$ tel que $E -> [|1, n|]$.\
      Supposons que E est infini. $[|1, n +1|] -> E -> [|1, n|] -> [|1, n+1|]$. \
      Ainsi $E <-> [|1, n+1|]$, donc E est fini. C'est abusrde donc E est fini. 
  ]
)

#proof("Croissance du cardinal", 
  $forall A, forall B, (Pfin(B) and A ->B) => (Pfin(A) and \#A <= \#B)$,
  [
    Soient $A, B$. Supposons que $(Pfin(B) and A -> B)$. \
    $B <-> [|1,\#B|]$. Ainsi,$ A -> B -> [|1, \#B|]$.\
    $A$ est donc fini. De plus, supposons que $\#A > \#B$. Ainsi :
    $ B -> [|1, \#B|] -> [|1, \#A|] -> A -> B $
    #h(1em) On a alors $\#A = \#B$, c'est absurde.\
     Ainsi, $\#A <=\#B$
  ]
)

#proof(
  "Lien avec l'addition", 
  $forall A, forall B, Pfin(A) and Pfin(B) ^ (A inter B = emptyset) => Pfin(A union B) and \#A union B = \#A + \#B$
  ,
  [
    Soient $A, B$ finis. Supposons que $(A inter B = emptyset)$. Notons $p = \#A$ et $q = \#B$. \
    On dispose de $f : A -> [|1, p|]$ et $g : B -> [|1, q|]$ bijectives. Posons :
    $ h : A union B &-> [|1, p + q|] \ x &|-> cases(f(x) "si" x in A, p + g(x) "sinon. ("x in B")") $
    Injectivité de $h$ : \
    #h(1em) Soient $x in A union B, x' in A union B$.\
    #h(1em)  Supposons que $h(x) = h(x')$ \
    #h(2em) Si $x in A and x' in.not A$ : 
    $h(x') = p + g(x') >= p + 1 > p >= f(x) = h(x)$, c'est impossible \ 
    #h(2em) Si $x in.not A and x' in A$ : symétrique du précédent. \
    #h(2em) Si $x in A and x' in A$ : $f(x) = h(x) = h(x') = f(x')$ donc $x = x'$ par injectivité de $f$.\
    #h(2em) Si $x in.not A and x' in.not A$ : $g(x) = h(x) = h(x') = g(x')$ donc $x = x'$ par injectivité de $g$.\

    Surjectivité de $h$ :
    Soit $y in [|1, p + q|]$.
    Si $y in [|1, p|]$ : $g(f^(-1)(y)) = f(f^(-1)(y)) = y$
    Sinon : \
    #h(1em) $y > p$. On dispose de $k in NN, k >=1$ tel que $p + k = y$. \
    #h(1em) De plus, $p + k < p + q + 1$ donc $k < q + 1$ donc $k <= q$. \
    #h(1em) Par surjectivité de $g$, on dispose de $x in B$ tel que $g(x) = k$.\
    #h(1em) $x in B$ donc $x in.not A$ donc $h(x) = p + k = y$

    Ainsi, $A union B <-> [|1, p + q|]$.
  ]
)
#proof("Lien avec la multiplication", 
  $forall A, forall B, Pfin(A) and Pfin(B) => Pfin(A times B) and \#A times B = \#A times \#B$
  ,[
      //todo*** Récurrence sur lecardinal de B en utilisant l'addition. 
  ])