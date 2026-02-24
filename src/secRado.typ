#import "../lib/lib.typ": *

= Théorème de Radó
Comme première application de la théorie des fonctions harmoniques, on établit
le #ref(<thRado>, supplement: "théorème de Radó"), qui affirme que la topologie de
toute surface de Riemann est à base dénombrable.

== Espaces topologiques à Base Dénombrable et Théorème de Poincaré-Volterra
#definition[
  On dit qu'un espace topologique $X$ est à base dénombrable s'il existe
  un ensemble dénombrable $cal(B)$ de parties ouvertes de $X$ tel que tout
  ouvert de $X$ s'écrive comme réunion d'éléments de $cal(B)$. On dit que
  $X$ est localement à base dénombrable si tout point de $X$ admet un
  voisinage dont la topologie induite par celle de $X$ est à base dénombrable.
]

On adopte la terminologie anglosaxonne pour la compacité ;
un espace topologique est dit compact s'il vérifie la propriété de Borel-Lebesgue.
On ne demande pas qu'il soit séparé.

#lemma[
  Soit $f : X --> Y$ une application continue surjective et ouverte entre deux
  espaces topologiques. Si $X$ est à base dénombrable d'ouverts, alors il en est de même de $Y$.
]<lemImageBaseDenom>

#proof[
  Soit $cal(B)$ une base dénombrable d'ouverts de $X$. Alors
  $
    cal(B) prime = { f(U) | U in cal(B) }
  $
  est un ensemble dénombrable d'ouverts de $Y$ car $f$ est ouverte. Soit $y in V subset Y$
  avec $V$ ouvert. Comme $f$ est surjective, il existe $x in X$ tel que $f(x) = y$. Il existe
  par continuité de $f$ un ouvert $U in cal(B)$ tel que $x in U subset f^(-1)(V)$. On a
  donc $y in f(U) subset V$ avec $f(U) in cal(B) prime$.
]

#lemma[
  Soit $K$ un espace compact dans lequel tout point admet un voisinage
  à base dénombrable. Alors $X$ est à base dénombrable.
]<lemCompactBaseDenom>

#proof[
  On recouvre $K$ par une famille finie d'ouverts $U_i$ admettant
  chacun une base dénombrable $cal(B_i)$.
  Alors la réunion des $cal(B_i)$ est un ensemble
  dénombrable de parties ouvertes de $K$, et forme une base de la
  topologie de $K$.
]

#lemma[
  Soit $X$ un espace topologique et $A subset X$. Alors toute partie
  de $X$ qui rencontre à la fois $A$ et son complémentaire
  mais pas sa frontière $partial A$ est non connexe.
]<lemFrontiereConnexite>

#proof[
  Soit $B subset X$ une telle partie. On a par hypothèse
  $
    B = (B inter circle(A)) union.sq B inter (overline(A)without circle(A)) union.sq
    (B inter (X without overline(A)))
    = (B inter circle(A)) union.sq (B inter (X without overline(A)))
  $
  ce qui montre que $B$ est réunion disjointe de deux ouverts non vides.
]

#theorem(title: "Poincaré-Volterra")[
  Soit $X$ un espace topologique séparé, connexe,
  localement connexe, localement compact et localement à base dénombrable.
  Soit $Y$ un espace topologique séparé à base dénombrable et soit $f : X --> Y$
  une application continue dont les fibres sont des sous-espaces discrets de $X$.
  Alors $X$ est à base dénombrable.
]<lemPoincVolt>

#proof[
  Soit $cal(B)$ une base dénombrable d'ouverts de $Y$. On dit que
  $U subset X$ est distingué s'il existe $V in cal(B)$ tel que $U$ est
  une composante connexe de $f^(-1)(V)$. On note $cal(A)$ l'ensemble
  des ouverts distingués de $X$ dont la topologie est à base dénombrable.

  #lemma[
    L'ensemble $cal(A)$ est une base de la topologie de $X$.
  ]<lemBasePoincVolt>

  #proof[
    Soit $x in X$ et $D$ un voisinage ouvert de $x$. La fibre $f^(-1)(f(x))$
    étant discrète, il existe un ouvert $U$ de $X$ tel que
    $U inter f^(-1)(f(x)) = { x }$. Comme $X$ est localement compact,
    il existe un voisinage compact $K$ de $x$, tel
    que $K subset U inter D$. L'application $f$ étant continue
    $f(partial K)$ est compact. Comme $Y$ est séparé, $f(partial K)$
    est fermé dans $Y$. On se donne donc $W in cal(B)$ tel que $f(x) in W$
    et $W inter f(partial K) = emptyset$. Soit $V$ la composante connexe
    de $f^(-1)(W)$ contenant $x$. Comme $X$ est localement connexe,
    $V$ est un ouvert de $X$. Par définition, $V$ est connexe, rencontre l'intérieur
    de $K$ car les deux contiennent $x$, et ne rencontre pas $partial K$ car
    $f(partial K) inter W = emptyset$. Par le @lemFrontiereConnexite, on a
    $V subset circle(K) subset K$. Or $K$ est compact, et localement à base dénombrable,
    donc à base dénombrable par le @lemCompactBaseDenom. Il en est donc de même de $V$.
    On a montré que $V in cal(A)$ et $x in V subset D$.
  ]

  #lemma[
    Étant donné $U_(0) in cal(A)$, l'ensemble des éléments de $cal(A)$ qui intersectent $U$
    est dénombrable.
  ]<lemDenomPoincVolt>

  #proof[
    La base $cal(B)$ étant dénombrable, il suffit de montrer que, pour un ouvert
    $V in cal(B)$, l'ensemble $cal(C)$ des composantes connexes de $f^(-1)(V)$ qui intersectent
    $U_(0)$ est dénombrable. . Or $U_0$ est à base dénombrable $cal(B)_(0)$,
    et l'application qui à $U in cal(B)_(0)$ tel que $U inter U_(0) eq.not emptyset$
    associe la composante connexe de $f^(-1)(V)$ contenant $U inter U_(0)$
    est surjective. En effet, si $W in cal(C)$, alors $W$ est ouvert car $X$ est localement
    connexe, donc il existe $U in cal(B)_(0)$ tel que $U subset W inter U_(0) eq.not emptyset$.
  ]

  #emph[Fin de la preuve du @lemPoincVolt.] Ces lemmes étant établis, considérons la relation $R$ sur $X$ définie par
  "$x R y$ si et seulement si il existe $U_0, ..., U_n in cal(A)$
  tels que $x in U_0$, $y in U_n$ et $U_i inter U_(i+1) eq.not emptyset$ pour
  $0 lt.eq.slant i lt.eq.slant n-1$". La relation $R$ est réflexive en vertu
  du @lemBasePoincVolt, et on vérifie immédiatement qu'elle est symétrique et transitive.
  D'autre part, chaque classe d'équivalence est ouverte par définition de $R$ ; comme $X$ est
  connexe, deux points quelconques de $X$ sont donc équivalents modulo $R$. Fixons $U^(*) in cal(A)$,
  et définissons pour tout $n in NN$, $cal(A)_(n)subset cal(A)$ comme l'ensemble des $U in cal(A)$
  tels qu'il existe $U_0, ..., U_n in cal(A)$ avec $U_0 = U^(*)$, $U_n = U$ et $U_i inter U_(i+1) eq.not emptyset$
  pour $0 lt.eq.slant i lt.eq.slant n-1$. Le fait que $R$ n'ait qu'une seule classe d'équivalence
  implique que $cal(A) = union_(n in NN) cal(A)_(n)$. Or, $A_(0) = { U^(*) }$ est dénombrable,
  et si $A_(n)$ est dénombrable pour un certain $n in NN$, alors
  $ A_(n+1) = union.big_(U in cal(A)_(n)) { V in cal(A) mid(|) V inter U eq.not emptyset } $
  est dénombrable par le @lemDenomPoincVolt. On conclut par récurrence que chaque $cal(A)_(n)$,
  et donc $cal(A)$, est dénombrable. Ainsi, $cal(A)$ est une base dénombrable de la topologie de $X$.
]

== Démonstration du théorème de Rado


#theorem(title: [Radó])[
  Toute surface de Riemann connexe $X$ a une topologie à base dénombrable.
]<thRado>

#proof[
  Soit $U subset X$ un ouvert de carte. On se donne $K_0, K_1 subset U$ deux disques
  compacts disjoints. On pose $Y := X without (K_0 union K_1)$. Alors $partial Y$ est une
  union de deux cercles disjoints, donc $overline(Y)$ est une sous-variété à bord lisse non vide
  de $X$. Le @thDirichletSurfaceRiemann assure l'existence d'une fonction continue
  $u : overline(Y) --> [0, 1]$, harmonique sur $Y$, telle que $u|_(partial K_0) eq 0$
  et $u|_(partial K_1) eq 1$. On se place dans la surface de Riemann $Y$,
  sur laquelle $u$ est harmonique non constante.
  L'opérateur différentiel $partial$ sur $Y$ n'est autre que $partial_(z)$
  dans une carte locale $z$. D'après @eqHarmoniqueZ, la $1$-forme différentielle
  $omega := partial u$ est donc holomorphe sur $Y$ et non identiquement nulle. Maintenant,
  considérons le revêtement universel $pi : tilde(Y) --> Y$ de $Y$. La tirée en arrière
  $pi^(*) omega$ est donc une $1$-forme holomorphe sur $tilde(Y)$, non identiquement nulle.
  Comme $tilde(Y)$ est simplement connexe, il existe une fonction holomorphe
  non constante $f : tilde(Y) --> CC$ telle que $dif f = pi^(*) omega$. D'après le
  principe des zéros isolés, les fibres de $f$ sont discrètes. $CC$ admet comme
  base dénombrable d'ouverts l'ensemble des disques dont les coordonnées du centre
  sont rationnelles et dont le rayon est rationnel. De plus, $tilde(Y)$ vérifie les hypothèses
  du #ref(<lemPoincVolt>, supplement: [Théorème de Poincaré-Volterra]) comme toute variété.
  On en déduit que $tilde(Y)$ est à base dénombrable. On applique alors le @lemImageBaseDenom
  au revêtement $pi$ pour conclure que $Y$ est à base dénombrable. Enfin, $X = Y union U$, où
  $Y$ et $U$ sont deux ouverts à base dénombrable (car $U$ est homéomorphe à un ouvert de $CC$),
  donc $X$ est également à base dénombrable.
]
