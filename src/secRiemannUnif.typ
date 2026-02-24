#import "../lib/lib.typ": *

= Uniformisation des surfaces de Riemann

== Deux énoncés équivalents du théorème d'uniformisation
#definition[
  Une surface de Riemann est un espace topologique non vide, séparé et
  tel que tout point possède un voisinage ouvert homéomorphe à un ouvert de $CC$,
  de sorte que les changements de cartes sont des fonctions biholomorphes.
]
#theorem(title: "Uniformisation")[
  Toute surface de Riemann simplement connexe est isomorphe soit à
  la sphère de Riemann $PP^(1)$, soit au plan complexe $CC$, soit au disque unité
  $DD subset CC$.
]<thUnif>

La première observation est que ces trois surfaces sont distinctes. En effet, la sphère de Riemann est compacte,
donc topologiquement différente des deux autres. D'après le théorème de Liouville, toute fonction holomorphe
bornée sur le plan complexe est constante, donc $CC$ n'est pas isomorphe au disque unité $DD$.

On va démontrer une version différente du théorème d'uniformisation.

#theorem[
  Toute surface de Riemann connexe non compacte dont le premier groupe d'homologie est trivial est isomorphe
  soit au plan complexe $CC$, soit au disque unité $DD$.
]<thUnifNonCompact>


En fait, le cas compact se déduit du second énoncé, qui est donc plus fort puisqu'il
suppose seulement que le premier groupe d'homologie est trivial et non la simple connexité.

#theorem[
  Soit $X$ une surface de Riemann connexe compacte de premier groupe d'homologie
  trivial. Alors $X$ est isomorphe à $PP^(1)$.
]

#proof[
  Soit $x in X$. Alors $x$ admet un voisinage euclidien de
  dimension complexe $1$, donc n'est pas isolé. On en déduit que
  $X without { x }$ est une surface de Riemann connexe non
  compacte. Comme $X$ est compacte et orientable (car c'est une
  variété complexe), la suite exacte longue associée à la paire
  $(X, X without { x })$ contient la portion suivante
  $
    H_(2)(X) arrowTildeLong H_(2)(X, X without { x })
    arrow.r.long^(0) H_1(X without { x }) arrow.r.long H_(1)(X) = 0.
  $
  On en déduit que $H_1(X without { x }) = 0$, donc le @thUnifNonCompact s'applique. Supposons
  par l'absurde que l'on ait un biholomorphisme $f : X without { x } arrowTildeLong DD$. Soit
  $phi : U arrowTildeLong DD$ une carte de $X$ centrée en $x$. Alors
  $ f compose phi^(-1)|_(DD without { 0 }) : DD without { 0 } --> DD $
  est holomorphe et bornée, donc s'étend en une fonction holomorphe sur $DD$.
  On a construit une application holomorphe $X --> DD$ non constante, ce qui est absurde
  car $X$ est compacte. On en déduit qu'il existe $g : X without { x } arrowTildeLong CC$. Soit $K subset CC$ un
  compact. Alors $g^(-1)(K) subset X without { x }$ est compact par continuité de $g^(-1)$, et $g$ envoie
  son complémentaire dans $CC without K$. Ainsi,
  $
    g(y) stretch(arrow.r.long)_(y -> x\ y eq.not x) infinity,
  $
  donc $g$ se prolonge en un homéomorphisme, donc un biholomorphisme
  $tilde(g) : X arrowTildeLong PP^(1)$.
]

== Collets

#definition(title: [Collet])[
  Soit $M$ une variété topologique à bord. Un _collet_ de $M$ est un
  voisinage $V$ de $partial M$ muni d'un isomorphisme
  $
    phi : V --> partial M times [0, 1[
  $
  dont la restriction à $partial M$ est l'application canonique
  $partial M --> partial M times { 0 }.$
]

On fixe désormais une variété lisse à bord compact $M$, de dimension $n$.
Par variété lisse, on entend ici un espace séparé muni d'une structure lisse,
sans hypothèse de paracompacité. On note $H := { x in RR^(n) mid(|) x_n gt.eq.slant 0 }$.

#lemma[
  Il existe un champ de vecteurs lisse $X : V --> T M$ défini sur un voisinage $V$ de
  $partial M$ tel que pour $X$ pointe vers l'intérieur de $M$ en tout point de $partial M$.
]<lemInwardVectorField>

#proof[
  Par compacité de $partial M$, on peut trouver un recouvrement fini $(U_i)$ de
  $partial M$ muni de cartes $phi_i : U_i --> H$ telles que $phi_i (U_i) = H
  inter \]-1, 1\[^(n) =: W$ pour tout $i$ ; on note $V$ la réunion des $U_i$. On
  considère alors le champ de vecteurs constant $Y = (0, ..., 0, 1)$ défini sur
  $W$. Cela définit un champ de vecteurs lisse $X_i = phi_i^(*)Y : U_i --> T M$
  pour chaque $i$. Soit $(chi_i)$ une partition de l'unité subordonnée au
  recouvrement $(U_i)$ de la variété $V$. Autrement dit, chaque $chi_i$
  est une fonction lisse à support compact inclus dans $U_i$ et à valeurs dans
  $[0, 1]$, et pour tout $x in V$, on a $sum_(i) chi_i(x) = 1$. Alors, le champ de
  vecteurs $X := sum_(i) chi_i X_i : V --> T M$ est bien défini --- par $chi_i X_i$,
  on entend l'application $V --> T M$ qui envoie $x$ sur $chi_i (x) X_i (x)$ si $x
  in U_i$, et sur $0$ sinon. Il est lisse comme somme finie de champs de vecteurs lisses.
  De plus, il suit des définitions que si $a in partial M$,
  $
    dif_a phi (X(a)) = sum_(i) chi_i (a) dif_a phi (X_i (a)) = Y(phi_i (a)) = (0, ..., 0, 1),
  $
  ce qui signifie que $X(a)$ pointe vers l'intérieur de $M$.
]


#theorem(title: [Existence d'un collet])[
  Soit $M$ une variété lisse à bord compact. Alors $M$ admet un collet.
]

#proof[
  Soit $X : V --> T M$ un champ de vecteurs lisse donné par le @lemInwardVectorField.
  D'après le théorème fondamental des flots pour une variété à bord, il existe
  une application lisse $delta : partial M --> \]0, +infinity\[$ et un plongement
  $
    Phi : cal(D) --> M, quad "où" quad cal(D) := { (x, t) in partial M times \]0, +infinity\[ thick mid(|) t lt delta(x) },
  $
  tel que l'image de $Phi$ soit un voisinage de $partial M$, et pour tout $x in partial M$,
  l'application $t arrow.r.long.bar Phi(x, t)$ soit une courbe intégrale de $X$ en $x$. Or,
  on a un difféomorphisme
  $
    Psi : partial M times \[0, 1\[ --> cal(D), quad (x, t) arrow.r.long.bar (x, t delta(x)),
  $
  donc $Phi compose Psi : partial M times \[0, 1\[ --> Phi(cal(D))$ est un collet de $M$.
]

== Remplissage et pièces <secRemplissagePieces>
Soit $X$ une surface de Riemann connexe non compacte.

#definition(title: [Remplissage])[
  Soit $Y subset X$ un sous-ensemble. On appelle _remplissage_ de $Y$,
  et l'on note $cal(h)(Y)$, la réunion de $Y$ et de toutes les composantes
  connexes $X without Y$ dont l'adhérence dans $X$ est compacte.
]

#proposition[
  Le remplissage $cal(h)$ vérifie les propriétés suivantes
  #ilist[
    + Pour tout $Y subset X$, on a $cal(h)(cal(h)(Y)) = cal(h)(Y)$ ;
    + Pour tous $Y subset Z subset X$, on a $cal(h)(Y) subset cal(h)(Z)$ ;
    + Le remplissage d'un fermé $Y subset X$ est fermé ;
  ]
]<propProprietesRemplissage>

#proof[
  #ilist[
    + Par définition, $X without cal(h)(Y)$ est la réunion des composantes connexes
      non compactes de $X without Y$, donc ne possède pas de composante connexe compacte.
    + Soit $x in cal(h)(Y) without Z$. Alors la composante connexe de $X without Z$ contenant
      $x$ est incluse dans la composante connexe de $X without Y$ contenant $x$.
      Par hypothèse, cette dernière est relativement compacte dans $X$, donc la première
      également.
    + Par définition, $X without cal(h)(Y)$ est une réunion de composantes connexes
      de $X without Y$. Comme $X without Y$ est localement connexe, celles-ci sont
      des ouverts de $X without Y$, donc de $X$ car $Y$ est fermé, donc $X without cal(h)(Y)$
      est ouvert.
  ]
]

#lemma[
  Soit $K subset X$ un compact non vide, et $U$ un voisinage ouvert relativement compact de $K$ dans $X$.
  Notons $(C_j)_(j in J)$ les composantes connexes de $X without K$. Alors tous les $C_j$ rencontrent
  $U$, et seul un nombre fini de $C_j$ rencontre $partial U$.
]<lemRemplissageCompact>

#proof[
  La surface $X$ étant en particulier séparée, $K$ est un fermé de $X$. On en déduit que les $C_j$ sont
  des ouverts de $X$. Si $C_j$ ne rencontre pas $U$, alors il est fermé dans $X$. Comme $X$ est connexe, on
  en déduit $C_j = X$, donc $C_j inter K eq.not emptyset$, absurde. La deuxième assertion vient du
  fait que $partial U$ est un compact recouvert par l'union disjointe des $C_j$.
]

#theorem[
  Soit $K subset X$ un compact. Alors $cal(h)(K)$ est un compact.
]<thRemplissageCompact>

#proof[
  Comme $X$ est non compact, $h(emptyset) = emptyset$. On peut donc supposer que $K$ est non vide.
  Par locale compacité de $X$, on trouve un voisinage ouvert relativement compact $U$ de $K$.
  D'après le @lemRemplissageCompact,
  toutes les composantes connexes de $X without K$ rencontrent $U$. Donc celles
  qui ne rencontrent pas $partial U$ sont incluses dans $U$. De plus, celles
  qui rencontrent $partial U$ sont en nombre fini.
  Ainsi, $cal(h)(K)$ est un fermé inclus dans la réunion de $U$ et d'un nombre fini
  de composantes relativement compactes, donc compact.
]

#definition(title: "Pièce")[
  On appelle _pièce_ de $X$ toute sous-surface compacte connexe à bord lisse de $X$. Une
  pièce $P$ de $X$ est dite _pleine_ si $cal(h)(P) = P$ ; autrement dit, si
  $X without P$ ne possède pas de composante connexe relativement compacte dans $X$.
]

#lemma[
  Soit $P$ une pièce de $X$. Alors $partial cal(h)(P)$ est un
  ouvert de $partial P$. En particulier, $cal(h)(P)$ est une sous-surface
  à bord lisse de $X$.
]<lemRemplissagePieceLisse>

#proof[
  Soit $x in partial cal(h)(P)$. On sait que $cal(h)(P)$ est un fermé de $X$, donc $x in cal(h)(P)$.
  Mais $x$ n'est dans aucune composante connexe relativement compacte de $X without P$ car celles-ci
  sont ouvertes. On en déduit que $x in P without circle(P) = partial P$. Soit $phi : U --> CC$ une carte
  _lisse_ centrée en $x$ d'image le disque unité $DD$, et telle que $phi(U inter partial P) = DD inter overline(cal(H)^(-))$,
  où $cal(H)^(-)$ (resp. $cal(H)^(+)$) désigne le demi plan inférieur (resp. supérieur).
  Une telle carte existe car $P$ est une sous-surface lisse à bord. On voit alors que
  $phi^(-1)(DD inter RR) = U inter partial P subset partial cal(h)(P)$
]

#corollary[
  Le remplissage d'une pièce $P$ de $X$ est une pièce pleine.
]<thRemplissagePieceEstPleine>

#proof[
  D'après le @thRemplissageCompact, $cal(h)(P)$ est un compact. Le @lemRemplissagePieceLisse
  assure alors que celui-ci est une pièce, et la @propProprietesRemplissage qu'elle est pleine.
]

#theorem[
  Tout compact $K subset X$ est contenu dans l'intérieur d'une pièce pleine $P subset X$.
]<thPiecePleineContenantCompact>

#proof[
  Quitte à ajouter des chemins entre chaque composante de $K$, supposons
  qu'il est connexe. Pour tout $x in K$, on se donne une carte $(U, phi)$,
  où $phi$ envoie $U$ sur le disque $DD(2)$. On extrait de cette collection
  de cartes une famille finie $(U_i, phi_i)_(1 lt.eq.slant i lt.eq.slant n)$, telle
  que
  $
    K subset union.big_(1 lt.eq.slant i lt.eq.slant n) V_i subset
    union.big_(1 lt.eq.slant i lt.eq.slant n) U_i =: U,
    quad "avec" V_i := phi^(-1)(DD(1)).
  $
  Soit $f : DD(2) --> [0, 1]$ une fonction lisse à support compact,
  valant identiquement $1$ sur le disque unité. On considère la fonction
  $chi : U --> RR$, donnée par
  $ chi = 1 - product_(i = 1)^(n) (1 - f compose phi_(i)). $
  Alors $chi$ est une fonction lisse, à support compact inclus dans $U$, et valant identiquement
  $1$ sur la réunion $V$ des $V_i$. D'après le théorème de Sard, l'ensemble des valeurs
  critiques de $f$ est de mesure nulle. On en déduit que l'ensemble des valeurs
  critiques de $chi$, qui est une réunion finie de sous-ensembles de $[0, 1]$ de mesure nulle, est également
  de mesure nulle. On se donne donc $0 < c < 1$ une valeur régulière de $chi$.
  Alors, la composante connexe de $chi^(-1)([c, +infinity[)$ qui contient $K$ est une pièce de $X$ 
  par inversion locale, contenant $K$ dans son intérieur. Il suffit de remplir $P$ et d'appliquer le
  @thRemplissagePieceEstPleine pour conclure.
]

#theorem[
  On suppose que $H_(1)(X) = 0$ et que $P$ est une pièce pleine de $X$.
  Alors $H_(1)(P) = 0$
]<thPiecePleineHomologieTriviale>

#proof[
  Soit $(V, phi)$ un collet de la variété $M := X without circle(P)$. Notons
  $W := phi^(-1)(partial M times [0, 1/2[)$. C'est un ouvert de $M$ relativement compact.
  Soient $A$ une composante connexe de $F := M without W$, et $B$ la composante connexe
  de $X without P$ contenant $A$. Alors $B subset A union overline(W)$. En effet,
  on a une rétraction continue $r : X without P --> F$ qui fixe $F$, donc
  $B inter F subset r(B) = A$. La pièce $P$ étant pleine, $B$ n'est pas relativement compacte,
  donc $A$ non plus. Ainsi, $F$ n'a pas de composante connexe compacte. On en déduit que
  $
    H_(2)(M without partial M, W without partial M) =
    H_(2)(M without partial M, (M without partial M) without F)
    tilde.equiv Gamma_(c)(F, tilde(M without partial M)) = 0
  $
  où $Gamma_(c)(F, tilde(M without partial M))$ désigne le groupe des sections à support
  compact définies sur $F$ du revêtement d'orientation de $M without partial M$. L'homologie
  étant un invariant homotopique, on a
  $
    H_(2)(X, P) tilde.equiv H_(2)(X, P union W),
  $
  puis, par excision de $P$, on obtient
  $
    H_(2)(X, P) tilde.equiv H_(2) (X, P union W)
    tilde.equiv H_(2) (M without partial M, W without partial M) = 0.
  $
  Enfin, la paire $(X, P)$ fournit la suite exacte
  $
    0 = H_(2)(X, P) --> H_(1)(P) --> H_(1)(X) = 0,
  $
  permettant de conclure que $H_(1)(P) = 0$.
]


== Uniformisation d'une pièce
Soient $X$ une surface de Riemann connexe non compacte, $P$ une pièce de $X$ telle que
$H_(1)(P) = 0$ et $a in circle(P)$. On se donne une carte locale $phi : U --> CC$
centrée en $a$, avec $U subset circle(P)$, et $Delta$ un voisinage de $a$ tel que
$phi(Delta) = overline(DD)(r)$. Comme $Delta$ et $P$ ont tous les deux une composante
connexe, l'inclusion $Delta arrowHookLong P$ induit un isomorphisme
$H_(0)(Delta) arrowTildeLong H_(0)(P)$. La paire $(Delta, P)$ donne donc une suite exacte
$
  0 = H_(1)(P) --> H_(1)(P, Delta) --> H_(0)(Delta) arrowTildeLong H_(0)(P),
$
de laquelle on tire $H_1 (P, Delta) = 0$. Comme $Delta$ est un voisinage de $a$,
on en déduit par excision que
#equation(id: "eqHomologieExision")[
  $
    H_(1)(P without { a }, Delta without { a }) = H_(1)(P, Delta) = 0.
  $
]
Le cercle $partial Delta$ étant un rétract de $Delta without { a }$,
l'inclusion $partial Delta arrowHookLong Delta without { a }$ induit un isomorphisme
#equation(id: "eqIsoHomologieCercle")[
  $
    H_(1)(Delta without { a }) tilde.equiv H_(1)(partial Delta).
  $
]
D'autre part, la paire $(P without { a }, Delta without { a })$ donne lieu à la suite exacte
#equation(id: "eqSuiteExactePaireEpointee")[
  $
    H_(1)(Delta without { a }) --> H_(1)(P without { a }) --> H_(1)(P without { a }, Delta without { a }) = 0.
  $
]
On déduit de @eqIsoHomologieCercle et @eqSuiteExactePaireEpointee que l'inclusion
$iota : partial Delta arrowHookLong P without { a }$ induit un morphisme surjectif
$
  H_(1)(partial Delta) --> H_(1)(P without { a }).
$

#lemma[
  Soit $omega$ une $1$-forme différentielle fermée sur $circle(P) without { a }$. Alors, pour tout
  chemin fermé lisse $gamma$ dans $circle(P) without { a }$, 
  il existe un entier $d in ZZ$ tel que
  $
    integral_(gamma) omega = d integral_(partial Delta) omega.
  $
]<lemIntegraleFormeFermee>

#proof[
  Soit
  $
    delta : [0, 1] --> partial Delta, quad t arrow.r.long.bar phi^(-1)(r e^(2i pi t))
  $
  la paramétrisation usuelle de $partial Delta$. Alors, $[delta]$ engendre
  $H_(1)(partial Delta)$, donc son image $iota_(*) [delta] in H_(1)(P without { a })$
  est également un générateur par la discussion précédente. Ainsi, si $gamma$ 
  est un chemin fermé lisse dans $P without { a }$, il existe un entier 
  $d in ZZ$ tel que $[gamma] = d iota_(*)[delta] in H_(1)(P without { a })$. 
  Or, $gamma - d iota_(*) delta$ est une $1$-chaine lisse dont la classe dans le groupe
  d'homologie singulière lisse $H_(1)^(infinity)(P without { a })$ est nulle par isomorphisme
  naturel entre l'homologie singulière continue et lisse.
  On en déduit que $gamma - d delta$ est le bord d'une $2$-chaîne singulière lisse $sigma$ dans
  $P without { a }$. On peut alors appliquer la formule de Stokes, qui donne
  $
    integral_(gamma) omega - d integral_(delta) omega = integral_(sigma) dif omega = 0
  $
  puisque $omega$ est fermée.
]

#theorem(title: [Uniformisation d'une pièce])[
  Il existe un biholomorphisme $phi.alt : circle(P) --> DD$ tel que $phi.alt(a) = 0$.
]<thUniformisationPiece>

#proof[
  Appliquons ce qui précède à une carte $phi : U --> CC$ centrée en $a$ de $X$
  telle que, $U subset circle(P)$, et sur $U without { a }$, la fonction de Green $G$ associée à $(P, a)$ vérifie
  $
    G = -ln abs(phi) + h, quad "avec" h : U --> RR "harmonique".
  $
  On note encore $Delta subset U$ l'image par $phi^(-1)$ d'un disque fermé $overline(DD)(r)$.
  Notons également $Y := circle(P) without { a }$. On considère la forme différentielle $omega := 2 partial G$ sur $Y$.
  C'est une $1$-forme holomorphe sur $Y$ car $G$ est harmonique sur ce domaine.
  Soit $p : tilde(Y) --> Y$ le revêtement universel de $Y$.
  La tirée en arrière $p^(*) omega$ est une $1$-forme holomorphe sur $tilde(Y)$.
  Comme $tilde(Y)$ est simplement connexe, il existe une fonction holomorphe
  $F : tilde(Y) --> CC$ telle que $dif F = p^(*) omega$ et $Re(F) = G compose p$. On pose alors
  $
    tilde(Theta) := q compose Im(F) : tilde(Y) --> RR slash 2pi ZZ,
  $
  où $q : RR --> RR slash 2pi ZZ$ est la projection canonique. Montrons que $tilde(Theta)$
  passe au quotient en une fonction $Theta : Y --> RR slash 2pi ZZ$.
  Soient $y in Y$ et $y_1, y_2 in tilde(Y)|_(y)$. Comme $tilde(Y)$ est connexe, il existe un
  chemin lisse $gamma : [0, 1] --> tilde(Y)$ de $y_1$ à $y_2$. On a
  $
    F(y_2) - F(y_1) = integral_(gamma) dif F = integral_(gamma) p^(*) omega = integral_(p compose gamma) omega.
  $
  Or, $p compose gamma$ est un chemin fermé lisse par morceaux (d'extrémité $y$) dans $Y$. 
  D'après le @lemIntegraleFormeFermee, il existe un entier $d in ZZ$ tel que
  $
    integral_(p compose gamma) omega = d integral_(partial Delta) omega
    = d integral_(partial Delta) 2 partial G = 2d integral_(partial Delta) partial (-ln abs(phi) + h).
  $
  Or, $partial h$ est holomorphe sur un voisinage simplement connexe de $Delta$, donc elle
  ne contribue pas à l'intégrale. De plus, si l'on se donne une détermination $ln : CC without RR_(-) --> CC$
  du logarithme complexe, on obtient, pour $z$ dans ce domaine
  $
    2 partial ln abs(z) = 2 partial Re(ln z) = partial (ln z + overline(ln z)) = (dif z)/z.
  $
  De là, il vient
  $
    F(y_2) - F(y_1) = - d integral_(partial Delta) (dif phi) / phi = - d integral_(partial DD(r)) (dif z) / z = - 2i pi d in 2 i pi ZZ.
  $
  Cela montre comme attendu qu'il existe $Theta : Y --> RR slash 2 pi ZZ$ telle que
  $tilde(Theta) = Theta compose p$. On définit alors
  $
    phi.alt = exp(-(G + i Theta)) : Y --> CC.
  $
  On a $G tilde_(a) - ln abs(phi) arrow.r.long_(a) + infinity$, donc $phi.alt arrow.r.long_(a) 0$.
  Ainsi, $phi.alt$ se prolonge en une fonction continue sur $circle(P)$, encore notée $phi.alt$,
  telle que $phi.alt(a) = 0$. Montrons que $phi.alt$ est holomorphe. D'après le théorème
  de la singularité effaçable, il suffit de vérifier que c'est le cas sur $Y$. Soit $y in Y$,
  et $psi : V --> DD$ une carte centrée en $y$ dans $Y$. Comme $V$ est simplement connexe, on peut
  relever $Theta|_V$ en une fonction $H : V --> RR$ telle que $q compose H = Theta|_(V)$. On a
  donc $phi.alt = exp(-(G + i H))$ sur $V$. Par construction, on a sur $tilde(Y)|_(V)$
  $ q compose H compose p = tilde(Theta) = q compose Im(F). $
  On en déduit par connexité de $V$ qu'il existe $k in ZZ$ tel que, sur $V$,
  $
    H compose p = Im(F) + 2 k pi.
  $
  Ainsi, la fonction
  $
    (G + i H) compose p = F + 2 i k pi : tilde(Y)|_(V) --> CC
  $
  est holomorphe. Comme $p$ est un biholomorphisme local, on en déduit que $G + i H$
  est holomorphe au voisinage de $y$. Ainsi, $phi.alt$ est holomorphe sur $circle(P)$. Comme
  $G|_(partial P) equiv 0$, la fonction $abs(phi.alt)$ se prolonge en une fonction continue
  sur $P$, valant identiquement $1$ sur $partial P$. Cela entraîne d'une part, d'après le principe du maximum,
  que $phi.alt$ est donc à valeurs dans $DD$, et d'autre part que $phi.alt$ est propre. En effet,
  soit $K subset D$ un compact de $DD$. Soit $overline(DD)(R)$ un disque fermé de $DD$ contenant $K$ dans son intérieur.
  Alors,
  $
    phi.alt^(-1)(K) subset abs(phi.alt)^(-1)([0, R]).
  $
  L'ensemble $abs(phi.alt)^(-1)([0, R])$ est un fermé de $P$, donc compact,
  ce qui montre que $phi.alt^(-1)(K)$ est également compact.
  Ainsi, $phi.alt : circle(P) --> DD$ est un revêtement ramifié fini. Comme $G tilde_(a) ln abs(phi)$,
  on en déduit que $abs(phi.alt) tilde_(a) abs(phi)$. Donc $phi.alt$ est d'ordre $1$ en $a$. Comme
  $phi.alt$ ne s'annule pas ailleurs qu'en $a$, on en déduit que son degré est $1$. C'est donc un biholomorphisme.
]

== Démonstration du théorème d'uniformisation
Soient $X$ une surface de Riemann connexe non compacte telle que $H_(1)(X) = 0$
et $a in X$.
D'après le @thPiecePleineContenantCompact, l'ensemble $cal(P)_(a)(X)$
des pièces pleines de $X$ dont l'intérieur contient $a$, est non vide.

#lemma[
  Soit $v in T_(a)X$ un vecteur tangent non nul. Alors, pour tout
  $P in cal(P)_(a)(X)$, il existe un unique
  biholomorphisme $Phi_(P) : circle(P) --> DD(R_(P))$ avec $R_P > 0$ tel que
  $Phi_(P)(a) = 0$ et $dif_(a) Phi_(P)(v) = 1$
]

#proof[
  Soit $P in cal(P)_(a)(X)$. D'après le @thPiecePleineHomologieTriviale, on a $H_(1)(P) = 0$.
  Le @thUniformisationPiece s'applique et fournit un biholomorphisme
  $phi.alt : circle(P) --> DD$ tel que $phi.alt (a) = 0$. Notons $w := dif_(a) phi.alt(v) in CC^(*)$
  et $R_P = abs(w)^(-1)$. Alors, l'application
  $
    Phi_(P) : circle(P) --> DD(R_(P)), quad z arrow.r.long.bar w^(-1) phi.alt(z)
  $
  satisfait les conditions requises. Si $Psi : circle(P) --> DD(R)$ est un autre
  biholomorphisme convenable, alors l'application $f : DD --> DD$ définie par
  $
    f(z) = (Psi compose Phi_(P)^(-1)(R_P z)) / R
  $
  est un biholomorphisme de $DD$ vérifiant $f(0) = 0$ et
  $
    f^(prime)(0) = dif_(0)f (1) = R_P / R quad "et" quad (f^(-1))^(prime)(0) = R / R_P.
  $
  Le #ref(<thSchwarz>, supplement: "Théorème de Schwarz") montre que $f^(prime)(0) = abs(f^(prime)(0)) = 1$ et $f$ est une rotation,
  donc $R = R_P$ et $f$ est l'identité.
]

#definition(title: [Rayon])[
  On appelle _rayon_ de $X$ en $a$ le réel
  $
    R_(a)(X) := sup_(P in cal(P)_(a)(X)) R_P.
  $
  On note $R(X)$ à la place de $R_(a)(X)$ s'il n'y a pas d'ambiguïté.
]

#remark[
  Comme $cal(P)_(a)(X) eq.not emptyset$, on a $R(X) in ]0, infinity[$.
]

#lemma[
  Notons $cal(V)_(a)(X)$ l'ensemble des voisinages ouverts de $a$ dans $X$. Alors
  les applications
  $
    cal(P)_(a)(X) --> ]0, infinity[, quad P arrow.r.long.bar R_P
      quad "et" quad
      cal(V)_(a)(X) --> ]0, infinity], quad U arrow.r.long.bar R(U)
  $
  sont croissantes. La première est strictement croissante.
]<lemCroissanceRayons>

#proof[
  La deuxième assertion résulte du fait que si $U subset V in cal(V)_(a)(X)$,
  alors $P_(a)(U) subset P_(a)(V)$ et de la croissance de la borne supérieure.
  Soient $P subset.neq Q in P_(a)(X)$. Comme $P, Q$ sont des fermés de $X$, on a
  $circle(P) subset.neq circle(Q)$. Il suffit alors d'appliquer le @thSchwarz à
  $
    f : DD --> DD, quad z arrow.r.long.bar (Phi_(Q) compose Phi_(P)^(-1)(R_P z))/R_Q,
  $
  qui n'est pas l'identité, sans quoi on aurait $circle(P) = circle(Q)$.
]

#remark[
  Si $P in cal(P)_(a)(X)$, on note pour alléger $R(P) := R(circle(P))$.
  Il résulte du @lemCroissanceRayons que $R(P) lt.eq.slant R_P$. De plus, si
  $R lt R_P$, le compact $K := Phi_(P)^(-1)(overline(DD)(R))$ est un élément de
  $cal(P)_(a)(circle(P))$ tel que $R_K = R$.
  En utilisant le @thPiecePleineContenantCompact, on trouve $Q in cal(P)_(a)(circle(P))$
  telle que $K subset circle(Q)$. Le @lemCroissanceRayons assure alors que
  $R = R_K lt R_Q lt.eq.slant R(P)$. Ainsi, $R_P = R(P)$.
]

#lemma[
  Il existe une suite $(P_n)_(n in NN)$ d'éléments de $cal(P)_(a)(X)$ telle que
  #ilist[
    + Pour tout $n in NN$, on a $P_n subset circle(P)_(n+1)$ ;
    + La suite $R(P_n)$ converge vers $R(X)$.
  ]
]<lemSuiteRayonsConvergents>

#proof[
  On construit la suite par récurrence. Soit $(r_n)_(n in NN)$ une suite de
  réels strictement croissante qui tend vers $R(X)$. Soit $P_0 in cal(P)_(a)(X)$ telle
  que $R_(P_0) > r_0$.
  Supposons les pièces $P_0, ..., P_n$ construites, vérifiant
  la condition _(i)_ de l'énoncé, et telles que pour tout $0 lt.eq.slant k lt.eq.slant n$,
  on ait $R_(P_k) > r_k$. Comme $X$ est non compacte, on sait par le @thPiecePleineContenantCompact
  qu'il existe $P in cal(P)_(a)(X)$ telle que $P_n subset circle(P)$. D'après le
  @lemCroissanceRayons, on a $R_(P_n) lt R_P lt.eq.slant R(X)$. On se donne également
  $Q in cal(P)_(a)(X)$ telle que $R_Q > r_(n+1)$. On applique une nouvelle fois
  le @thPiecePleineContenantCompact, cette fois au compact $P union Q$. On trouve
  ainsi une pièce pleine $P_(n+1)$ de $X$ contenant $P union Q$ dans son intérieur.
  A fortiori, on a $a in P_n subset circle(P_(n+1))$ et $R_(P_(n+1)) > R_Q > r_(n+1)$.
  On a ainsi construit une suite $(P_n)_(n in NN)$ qui vérifie _(i)_ et telle que
  pour tout $n in NN$, on ait $R_(P_n) > r_n$, ce qui montre que
  $R(P_n) = R_(P_n) stretch(arrow)_(n -> infinity) R(X)$.
]

#lemma[
  Soient $R > 0$ un réel et $D subset.neq DD(R)$ un ouvert simplement connexe contenant $0$.
  Alors il existe un réel $r < R$ et une application holomorphe $g : D --> DD(r)$ telle que
  $g(0) = 0$ et $g^(prime)(0) = 1$.
]<lemApplicationHoloDomainePropre>

#proof[
  Supposons d'abord que $R = 1$. Soit $a in DD without D$. On considère le biholomorphisme
  $
    phi_(a) : CC without { overline(a)^(-1) } --> CC without { - overline(a)^(-1) },
    quad z arrow.r.long.bar (z - a) / (1 - overline(a) z)
  $
  introduit à la @secAutomorphismesDisque. Alors $phi_a$ est bien définie sur $D$
  et $phi_(a)(D) subset DD^(*)$. On peut donc relever $phi_(a)$ en une application holomorphe
  $psi : D --> DD^(*)$ telle que $psi^(2) = phi_(a)|_(D)$. On considère alors
  la composée
  $
    g := phi_b compose psi : D --> DD, quad "avec" b := psi(0) in DD^(*).
  $
  On a $g(0) = 0$. De plus, $2 b psi^(prime)(0) = phi_(a)^(prime)(0) = 1 - abs(a)^(2)$, donc
  $
    g^(prime)(0) = phi_(b)^(prime)(b) psi^(prime)(0)
    = 1 / (1 - abs(b)^(2)) (1 - abs(a)^(2)) / (2 b)
    = (1 + abs(b)^(2)) / (2b)
  $
  car $b^(2) = -a$. On a donc
  $
    abs(g^(prime)(0)) - 1 gt.eq.slant (1 - 2abs(b) + abs(b)^(2)) / (2abs(b)) gt 0
  $
  car $b eq.not 0$. On pose alors $r = abs(g^(prime)(0))^(-1)$ et la fonction
  $
    abs(g^(prime)(0))^(-1) g : D --> DD(r)
  $
  répond aux conditions requises. Pour $R > 0$ quelconque, on trouve par ce qui précède
  une application holomorphe $h : 1/R D --> DD(r)$ avec $r < 1$ telle que
  $h(0) = 0$ et $h^(prime)(0) = 1$. La fonction
  $ D --> DD(R r), quad z arrow.r.long.bar R h(z / R) $
  convient.
]

#lemma[
  Soit $Y$ un espace topologique qui est la réunion croissante d'une suite
  d'ouverts simplement connexes $(U_n)_(n in NN)$. Alors $Y$ est simplement connexe.
]<lemUnionSimplementConnexe>

#proof[
  Soit $gamma : [0, 1] --> Y$ un lacet. Comme $[0, 1]$ est compact, il existe par croissance
  de la suite $(U_n)_(n in NN)$, un entier $N$ tel que $gamma([0, 1]) subset U_N$.
  Comme $U_N$ est simplement connexe, on en déduit que $gamma$ est homotope à
  l'application constante dans $U_N$, donc dans $Y$.
]

#lemma[
  Soit $(P_n)_(n in NN) in cal(P)_(a)(X)^(NN)$ une suite de pièces pleines vérifiant
  les conditions (i) et (ii) du @lemSuiteRayonsConvergents. Notons
  $Phi_(n) := Phi_(P_n) : circle(P_n) --> DD(R_n)$ l'isomorphisme associé à $P_n$.
  On considère également l'ouvert
  $ Y := union.big_(n in NN) circle(P_n). $
  Alors, pour tout compact $K subset Y$, il existe $N in NN$ tel
  que la suite $(Phi_(n)|_K)_(n gt.eq.slant N)$ soit bien définie et de Cauchy
  pour la norme de la convergence uniforme. De plus, l'application limite $Phi : Y --> DD(R)$
  est un biholomorphisme, où l'on note $R := R(X)$ et $DD(infinity) := CC$.
]<lemConvergenceUniforme>

#proof[
  Soit $K subset Y$ un compact. La collection des $circle(P_n)$ est un recouvrement ouvert
  de $K$, donc il existe $N in NN$ tel que
  $ K subset union.big_(0 lt.eq.slant n lt.eq.slant N) circle(P_n) = circle(P_N). $
  La suite $(Phi_(n)|_K)_(n gt.eq.slant N)$ est donc bien définie. Soient $n gt.eq.slant m gt.eq.slant N$
  deux entiers. Considérons l'application
  $
    f := Phi_(n) compose Phi_(m)^(-1) : DD(R_m) --> DD(R_n),
  $
  qui vérifie $f(0) = 0$ et $f^(prime)(0) = 1$ par construction. On note également
  $r := max (abs(Phi_(m))(K)) < R_N$. Si $R < infinity$, on
  applique le @corBorneSchwarzPick, qui donne, pour tout $z in Phi_(m)(K)$
  $
    abs(f(z) - z) lt.eq.slant abs(z)^(2)/R_(m)^(2) (R_(n)^(2) - R_(m)^(2)) / (R_(n) - abs(z))
    lt.eq.slant r^(2)/R_(m)^(2) (R_(n)^(2) - R_(m)^(2)) / (R_(n) - r)
    lt.eq.slant (2 R r^(2)) / (R_(N)^(2)(R_(N) - r)) (R_n - R_m).
  $
  Si $R = infinity$ et $m$ est suffisamment grand, on a
  $r < R_m /16$. On applique alors l'inégalité d'uniformisation d'Erdős (@corInegaliteErdos)
  à $f$. On obtient, pour tout $z in Phi_(m)(K)$,
  $
    abs(f(z) - z) lt.eq.slant 80 r^(2) / R_(m).
  $
  Dans les deux cas, on conclut que pour tout $epsilon > 0$, il existe $M gt.eq.slant N$ tel
  que pour tous $n gt.eq.slant m gt.eq.slant M$ et tout $x in K$,
  $
    abs(Phi_(n)(x) - Phi_(m)(x)) = abs(f(Phi_(m)(x)) - Phi_(m)(x)) lt.eq.slant epsilon.
  $
  Ainsi, la suite $(Phi_(n)|_K)_(n gt.eq.slant N)$ est de Cauchy pour la norme de la convergence uniforme.
  Comme $CC$ est complet, cela implique la convergence uniforme. On en déduit que
  la suite des $Phi_(n)$ prolongées par $0$ sur le complémentaire
  de $circle(P_(n))$ dans $Y$, converge uniformément sur les compacts
  vers une application $Phi : Y --> CC$. Par locale
  compacité de $Y$, $Phi$ est holomorphe. Elle est non constante car
  $
    dif_(a) Phi (v) = lim_(n -> infinity) dif_(a) Phi_(n) (v) = 1.
  $
  Son image est donc un ouvert de $CC$ inclus dans $overline(DD)(R)$, donc dans $DD(R)$.
  Montrons que $Phi$ est injective. Soit $m in NN$. Alors, la suite
  de fonctions injectives $(Phi_(n) compose Phi_(m)^(-1) : DD(R_m) --> CC)_(n gt.eq.slant m)$
  converge uniformément sur les compacts de $DD(R_m)$ vers la fonction holomorphe
  $Phi compose Phi_(m)^(-1)$. On en déduit que celle-ci est injective ou constante (résultat sur la convergence
  de suites de fonctions holomorphes). Comme sa dérivée en $0$ vaut $1$, elle est injective.
  Donc $Phi|_(circle(P_m))$ l'est également.
  Comme $Y$ est la réunion croissante des $circle(P_m)$, on en déduit que $Phi$ est injective.
  Montrons que $Phi : Y --> DD(R)$ est surjective.
  Si $R = infinity$, il suffit d'appliquer le @thKoebeQuart à $Phi compose Phi_(n)^(-1)$,
  dont l'image contient donc $DD(R_n slash 4)$ pour tout $n in NN$. Comme
  $R_n stretch(arrow)_(n -> infinity) infinity$, on en déduit que tout disque est contenu dans l'image
  de $Phi$, donc que $Phi$ est surjective. Supposons maintenant que $R lt infinity$ et que
  $Z := Phi(Y) subset.neq DD(R).$ Comme les $circle(P)_(n)$ sont homéomorphes
  au disque, ils sont simplement connexes, donc $Y$ également d'après le
  @lemUnionSimplementConnexe. L'application $Phi : Y --> Z$ est holomorphe
  et bijective, donc c'est un biholomorphisme. Par le @lemApplicationHoloDomainePropre,
  il existe un réel $r < R$ et une application holomorphe
  $g : Z --> DD(r)$ telle que $g(0) = 0$
  et $g^(prime)(0) = 1$. Soit $n in NN$ tel que $R_n gt r$. Alors, l'application
  $
    h := g compose Phi compose Phi_(n)^(-1) : DD(R_n) --> DD(r)
  $
  vérifie $h(0) = 0$ et $h^(prime)(0) = 1$. Le @thSchwarz entraine $R_n lt.eq.slant r$,
  une contradiction. Ainsi, $Phi : Y --> DD(R)$ est une bijection holomorphe, donc
  un biholomorphisme.
]


Nous sommes maintenant en mesure de démontrer la reformulation suivante du @thUnifNonCompact.

#theorem(title: [Uniformisation de $X$])[
  Si $R(X) = infinity$, alors $X$ est isomorphe à $CC$ ; sinon, $X$ est isomorphe à $DD(R(X))$.
]<thUniformisationSurfacesRiemann>

#proof[
  On se donne une suite $(P_n)_(n in NN) in cal(P)_(a)(X)^(NN)$
  satisfaisant les conditions du @lemSuiteRayonsConvergents. On reprend les notations
  du @lemConvergenceUniforme, qui assure l'existence d'un biholomorphisme
  $ Phi : Y --> DD(R) quad "tel que" quad Phi(a) = 0 "et" dif_(a)Phi(v) = 1. $
  Supposons que $Y subset.neq X$. Soit $b in X without Y$. On construit une suite
  $(Q_n)_(n in NN) in (cal(P)_(a)(X) inter cal(P)_(b)(X))^(NN)$ par récurrence de la
  manière suivante. On se donne par le @thPiecePleineContenantCompact une pièce pleine
  $Q_0$ de $X$ contenant $P_0 union { b }$ dans son intérieur. Supposons $Q_0, ..., Q_n$
  construites. On applique le @thPiecePleineContenantCompact au compact
  $P_(n+1) union Q_n$ pour obtenir une pièce pleine $Q_(n+1)$ de $X$ contenant
  $P_(n+1) union Q_n$ dans son intérieur. La suite ainsi construite
  vérifie $P_n subset circle(Q)_n, Q_n subset circle(Q)_(n+1)$ et $P_0 union { b } subset circle(Q)_n$
  pour tout $n in NN$. En particulier, la suite $(R(Q_n))_(n in NN)$ croît vers $R$.
  Appliquons le @lemConvergenceUniforme à la suite $(Q_(n))_(n in NN)$.
  On obtient un biholomorphisme
  $
    Psi : Z := union.big_(n in NN) circle(Q)_(n) --> DD(R) quad "tel que" quad Psi(a) = 0 "et" dif_(a)Psi(v) = 1.
  $
  On a $Y subset.neq Z$ puisque $circle(P_n) subset P_n subset circle(Q)_n$ et $b in circle(Q)_0$.
  Alors, l'application
  $
    Psi compose Phi^(-1) : DD(R) --> DD(R)
  $
  est holomorphe, envoie $0$ sur $0$ et a pour dérivée $1$ en $0$, qui n'atteint pas
  $Psi(b)$. Le @thSchwarz fournit une contradiction. On en déduit que $Y = X$, et
  que $Phi : X --> DD(R)$ est un biholomorphisme.
]

