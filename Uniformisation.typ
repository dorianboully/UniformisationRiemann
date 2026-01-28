#import "lib/lib.typ": *

#show: mathdoc.with(
  title: [Fonctions harmoniques\ ---\ Théorème de Radó et  Uniformisation],
  author: "Dorian Boully",
  thstyle: "article",
  date: auto,
)

#[
  #set heading(numbering: none)
  #show heading: align.with(center)
  = Résumé
]

Ce document introduit la théorie élémentaire des fonctions harmoniques
en dimension $2$ et donne deux applications fondamentales en géométrie
des surfaces de Riemann. Le Théorème de Radó, qui dit que toute surface
de Riemann connexe est à base dénombrable d'ouverts, ainsi que le Théorème
d'Uniformisation de Riemann, qui classifie les surfaces de Riemann simplement connexes
en trois types d'isomorphisme : la sphère, le disque et le plan complexe.

Le texte est divisé en trois parties.
La première introduit les fonctions harmoniques dans $CC$ et
sur les surfaces de Riemann. Elle couvre les propriétés
fondamentales telles que la propriété de la moyenne, le
principe du maximum, et la formule de Poisson. La construction des
fonctions de Green via les familles de Perron est
détaillée. Cette section s'appuie principalement sur les
ouvrages @cartan_theorie_1985 pour le cas euclidien et,
@forster_lectures_1981, @farkas_riemann_1980,
@hubbard_teichmuller_2006 pour l'extension aux surfaces de
Riemann.
La deuxième partie est consacrée à la démonstration du Théorème de Radó,
qui repose sur la résolution du problème de Dirichlet et le théorème
de Poincaré-Volterra. La preuve est essentiellement tirée de @forster_lectures_1981.
La troisième partie présente une démonstration du Théorème d'Uniformisation
de Riemann, indépendante du théorème de Radó. On a suivi pour l'essentiel les indications
de #cite(<douady_algebre_2005>, supplement: "Exercice 8 page 393"). Les points cruciaux
de la preuve sont l'existence de fonctions de Green, la construction d'une exhaustion
par des domaines compacts simplement connexes à bord lisse ainsi que les inégalités
de distorsion de Koebe.

La compréhension de ce texte demande une certaine familiarité avec
les notions suivantes.
/ Analyse complexe.: Fonctions holomorphes élémentaires
  (séries entières, formule intégrale de Cauchy, principe du
  maximum), séries de fonctions holomorphes (convergence
  uniforme sur les compacts, théorème de Weierstrass, théorème
  de Hurwitz), théorème de l'application ouverte, formes
  normales pour les applications holomorphes, ordre
  d'un zéro. Le livre @cartan_theorie_1985 est excellent.
/ Surfaces de Riemann.: Cartes, atlas, applications holomorphes,
  revêtements ramifiés. Les livres @forster_lectures_1981
  @farkas_riemann_1980,@douady_algebre_2005 couvrent largement ces aspects.
/ Théorie des revêtements.: Revêtements universels,
  relèvement, groupe fondamental. L'ouvrage @douady_algebre_2005
  fournit un traitement détaillé.
/ Calcul différentiel et Géométrie différentielle.:
  Théorème de Sard, variétés topologiques et différentielles,
  variétés à bord, champs de vecteurs, flots, intégration des
  formes différentielles, théorème de Stokes. On renvoie pour cela
  à @lee_introduction_2013, très détaillé.
/ Homologie.: Excision, suites exactes de paires, revêtement d'orientation.
  Le livre @bredon_topology_1993 est une excellente référence.

Ces prérequis étant satisfaits, le texte qui suit est entièrement autonome.

#outline()

= Fonctions harmoniques et compléments d'analyse complexe
== Fonctions harmoniques dans $CC$
Fixons dans cette section un ouvert $D$ de $CC$.

=== Notations et fonctions holomorphes dans $CC$
On identifie $RR^(2)$ avec $CC$ via l'application
$
  (x, y) in RR^(2) arrow.r.long.bar x + i y in CC.
$

Notons $dif x, dif y, dif z, dif overline(z) : CC --> CC$ les applications $RR$-linéaires respectivement
données par la partie réelle, la partie imaginaire, l'identité et la conjugaison complexe.
Alors $(dif x, dif y)$ et $(dif z, dif overline(z))$ forment deux $CC$-bases de l'espace
des applications $RR$-linéaires de $CC$ dans lui-même. En effet, c'est clair pour la première,
et l'on a
$
  dif x = 1/2 (dif z + dif overline(z)), quad dif y = 1/(2i) (dif z - dif overline(z)), quad
  dif z = dif x + i dif y, quad dif overline(z) = dif x - i dif y.
$
De là, si $u : CC --> CC$ est une application $RR$-linéaire, on a
$
  u & = alpha dif x + beta dif y \
    & = 1/2 alpha (dif z + dif overline(z)) + 1/(2i) beta (dif z - dif overline(z)) \
    & = 1/2 (alpha - i beta) dif z + 1/2 (alpha + i beta) dif overline(z).
$
Si $f : D --> CC$ est une fonction différentiable en $a in D$,
on a par définition des dérivées partielles
$
  dif f_(a) & = partial_(x) f(a) dif x + partial_(y) f(a) dif y
              = [1/2(partial_(x) - i partial_(y)) f](a) dif z + [1/2(partial_(x) + i partial_(y)) f](a) dif overline(z) \
            & = partial_(z) f(a) dif z + partial_(overline(z)) f(a) dif overline(z),
$
où l'on a posé
#equation(id: "eqExprDifferentielle")[
  $
    partial_(z) := 1/2 (partial_(x) - i partial_(y)), quad
    partial_(overline(z))f := 1/2 (partial_(x) + i partial_(y)).
  $
]
On a donc en outre
$
  partial_(x) = partial_(z) + partial_(overline(z)), quad
  partial_(y) = i (partial_(z) - partial_(overline(z))).
$

#definition[
  Une fonction $f : D --> CC$ est holomorphe
  en $a in D$ si elle est différentiable en $a$ et $dif f_(a)$ est $CC$-linéaire.
]

D'après @eqExprDifferentielle, $f$ est holomorphe en $a$ si et seulement si
#equation(id: "eqCauchy")[
  $
    dif f_(a)(i) = i dif f_(a) (1) & arrow.l.r.double.long partial_(y) f(a) = i partial_(x) f(a)\
    & arrow.l.r.double.long i (partial_(z)f(a) - partial_(overline(z))f(a)) = i (partial_(z) f(a) + partial_(overline(z)) f(a))\
    & arrow.l.r.double.long partial_(overline(z)) f(a) = 0.
  $
]

On appelle équation de Cauchy-Riemann la condition @eqCauchy.
On admet ici la théorie élémentaire des fonctions holomorphes. En particulier, on sait
que les fonctions holomorphes sont $CC$-analytiques et vérifient la formule intégrale
de Cauchy.

=== Fonctions harmoniques dans $CC$

#definition(title: "Fonction Harmonique")[
  Une fonction $f : D --> CC$ est dite harmonique
  si elle est de classe $scr(C)^(2)$ en tant que fonction de deux variables réelles
  et satisfait
  #equation(id: "eqHarmonique")[
    $
      Delta f := partial^(2)_(x) f + partial^(2)_(y) f = 0.
    $
  ]
]

Exprimons le laplacien en fonction des dérivées par rapport à $z$ et $overline(z)$.
On a
#grid(
  columns: (1fr, auto, 1fr),
  // Gauche, Milieu (taille du texte), Droite
  column-gutter: 1em,
  align: horizon,
  $
    partial^(2)_(x) & = (partial_(z) + partial_(overline(z))) compose (partial_(z) + partial_(overline(z))) \
                    & = partial^(2)_(z) + 2 partial^(2)_(z overline(z)) + partial^(2)_(overline(z))
  $,
  [et],
  // Le texte au milieu
  $
    partial^(2)_(y) & = i^(2) (partial_(z) - partial_(overline(z))) compose (partial_(z) - partial_(overline(z))) \
                    & = - (partial^(2)_(z) - 2 partial^(2)_(z overline(z)) + partial^(2)_(overline(z))).
  $,
)
De là, il vient
$
  Delta = 4 partial^(2)_(z overline(z)),
$
et par suite la condition @eqHarmonique est équivalente à
#equation(id: "eqHarmoniqueZ")[
  $ partial^(2)_(z overline(z)) f = 0. $
]

#remark[
  Si $f : D --> CC$ est une fonction différentiable,
  c'est aussi le cas de sa conjuguée $overline(f)$, et l'on a
  $
    partial_(z) overline(f) & = 1/2 (partial_(x) - i partial_(y)) overline(f) \
                            & = 1/2 (overline(partial_(x) f) - i overline(partial_(y) f)) \
                            & = overline(1/2 (partial_(x) + i partial_(y)) f) \
                            & = overline(partial_(overline(z)) f).
  $
  De même, $partial_(overline(z)) overline(f) = overline(partial_(z) f)$. On en déduit
  que la conjuguée d'une fonction harmonique est harmonique, puis par linéarité que
  la partie réelle et la partie imaginaire d'une fonction harmonique sont des fonctions harmoniques.
]

=== Fonctions harmoniques et fonctions holomorphes
#proposition[
  Toute fonction holomorphe est harmonique.
]

#proof[
  Soit $f : D --> CC$ une fonction holomorphe. En particulier, $f$ est $scr(C)^(2)$.
  La condition @eqCauchy donne $partial_(overline(z)) f = 0,$ et en
  dérivant par rapport à $z$, on obtient @eqHarmoniqueZ.
]

La stabilité des fonctions harmoniques par passage à la partie réelle et imaginaire
entraine :

#corollary[
  La partie réelle et la partie imaginaire d'une fonction holomorphe sont des
  fonctions harmoniques.
]

La réciproque est vraie localement.

#proposition[
  Supposons que l'ouvert $D$ soit simplement connexe. Soit $f : D --> RR$
  une fonction harmonique réelle.
  Alors $f$ est la partie réelle d'une fonction holomorphe $F : D --> CC$. De plus,
  $F$ est unique à l'addition d'une constante imaginaire pure près.
]<propHarmoReelHolo>

#proof[
  Comme $f$ est harmonique, on a $partial^(2)_(z overline(z)) f = 0$. En particulier,
  la fonction $partial_(z) f$ est holomorphe sur $D$. Comme $D$ est simplement connexe,
  on sait que la forme différentielle $partial_(z) f dif z$ admet une primitive sur $D$.
  Autrement dit, il existe $F : D --> CC$ telle que
  #equation(id: "eqPrimitiveHolo")[
    $ dif F = 2 partial_(z) f dif z. $
  ]
  Cela montre que $dif F$ est $CC$-linéaire en tout point de $D$,
  donc que $F$ est holomorphe. En passant au conjugué dans @eqPrimitiveHolo, il vient
  $
    dif overline(F) = overline(dif F) = 2 overline(partial_(z) f) dif overline(z)
    = 2 partial_(overline(z)) overline(f) dif overline(z) = 2 partial_(overline(z)) f dif overline(z),
  $
  car $f$ est réelle. On a donc
  $
    dif (Re(F)) = 1/2 (dif F + dif overline(F)) = partial_(z) f dif z + partial_(overline(z)) f dif overline(z) = dif f,
  $
  donc $f = Re(F - c)$ pour une certaine constante réelle $c$. Supposons que $F_1, F_2 : D --> CC$
  sont deux fonctions holomorphes de même partie réelle. Notons $F = F_1 - F_2$. Alors
  $
    0 = dif (F + overline(F)) = partial_(z) F dif z + partial_(overline(z)) F dif overline(z),
  $
  ce qui exige $partial_(z) F = partial_(overline(z)) overline(F) = 0$. Ainsi, $F$ est constante
  de partie réelle nulle.
]

En particulier, comme $CC$ est localement simplement connexe, toute fonction harmonique
réelle est localement la partie réelle d'une fonction holomorphe déterminée à l'addition
près d'une constante imaginaire pure.

=== Propriété de la moyenne et principe du maximum
#lemma[
  Soit $overline(DD)(z, r)$ un disque fermé inclus dans $D$. Alors il
  existe $r prime > r > 0$ tel que $DD(z, r prime) subset D$.
  En particulier, tout disque fermé inclus dans $D$ admet un voisinage ouvert simplement connexe
  inclus dans $D$.
]

#proof[
  Si un tel $r prime$ n'existait pas, on trouverait une suite $(z_n)_(n gt.eq.slant 1)$ de points
  de $CC without D$ dont la distance à $z$ est au plus $r + 1/n$. Une telle suite est
  en particulier bornée, donc admet une sous-suite convergente vers
  un point de $overline(DD)(z, r)$. Comme $D$ est un voisinage ouvert de ce disque fermé,
  $z_n in D$ pour $n$ assez grand, ce qui est absurde.
]
#proposition(title: "Propriété de la moyenne")[
  Soit $f : D --> CC$ une fonction harmonique.
  Alors pour tout disque fermé $overline(DD)(z, r) subset D$, on a
  #equation(id: "eqPropMoyenne")[
    $
      f(z) = 1/(2 pi) integral_(0)^(2 pi) (f(z) + r e^(i theta)) dif theta.
    $
  ]
]<propPropMoyenneHarmo>

On dit qu'une fonction continue $D --> CC$ qui vérifie @eqPropMoyenne
pour tout $overline(DD)(z, r) subset D$ vérifie la propriété de la
moyenne. Il est clair que cette propriété est stable par combinaison
linéaire, partie réelle et imaginaire. De plus, toute fonction holomorphe
$g : D --> C$ vérifie la propriété de la moyenne.
En effet, la formule intégrale de Cauchy donne
$
  g(z) = 1/(2 i pi) integral_(partial DD(r)) g(z + zeta) (dif zeta)/zeta
  = 1/(2 pi) integral_(0)^(2 pi) g(z + r e^(i theta)) (r e^(i theta)dif theta) / (r e^(i theta))
  = 1/(2 pi) integral_(0)^(2 pi) g(z + r e^(i theta)) dif theta.
$

#proof(title: [Démonstration de la @propPropMoyenneHarmo])[
  Écrivons $f = P + i Q$ avec $P, Q : D --> RR$.
  On sait que $P$ et $Q$ sont harmoniques. Prenons un voisinage
  ouvert simplement connexe $U subset D$ de $overline(DD)(z, r)$.
  D'après la @propHarmoReelHolo, les restrictions de $P$ et $Q$
  à $U$ sont des parties réelles de fonctions holomorphes, donc
  vérifient la propriété de la moyenne, donc $f|_(U)$ aussi. Comme
  c'est vrai pour tout $overline(DD)(z, r) subset D$, cela conclut.
]

#proposition(title: "Principe du maximum")[
  Soit $f : D --> RR$ une fonction continue à valeurs réelles qui satisfait la propriété de la moyenne.
  Si $f$ atteint un maximum local en un point $z in D$, alors $f$ est
  constante dans un voisinage de $z$.
]<propPpeMaxReel>

#proof[
  Soit $DD(z, r)$ un disque contenu dans $D$ tel que
  pour tout $zeta in DD(z, r)$, on ait $f(zeta) lt.eq.slant f(z)$.
  L'égalité de la moyenne donne, pour tout $0 < r prime < r$
  $
    0 = 1/(2 pi) integral_(0)^(2 pi) (f(z) - f(z + r prime e^(i theta))) dif theta.
  $
  L'intégrande étant continue et positive ou nulle, elle est identiquement nulle.
  Cela montre que $f equiv f(z)$ sur $DD(z, r)$.
]

#corollary[
  Soit $f : D --> CC$ fonction continue définie sur un ouvert de $CC$
  qui satisfait la propriété de la moyenne. Si $abs(f)$ atteint un maximum
  local en un point $z in D$, alors $f$ est constante dans un
  voisinage de $z$.
]

#proof[
  Soit $DD(z, r)$ un disque contenu dans $D$ tel que
  pour tout $zeta in DD(z, r)$, on ait $abs(f(zeta)) lt.eq.slant abs(f(z))$.
  Soit $t in RR$ tel que $exp(- i t)f(z) in RR_(+)$. Alors
  $Re(exp(-i t) f)$ est une fonction continue à valeurs réelles
  satisfaisant la propriété de la moyenne, et pour tout $zeta in DD(z, r)$,
  on a
  $
    Re(exp(-i t) f(zeta)) lt.eq.slant abs(Re(exp(-i t) f(zeta))) lt.eq.slant abs(f(zeta)) lt.eq.slant abs(f(z)) = Re(exp(-i t)f(z))
  $
  D'après la @propPpeMaxReel, $Re(exp(-i t) f)$ est constante sur un voisinage de $z$,
  donc $Re(f)$ également. Par le même raisonnement, $Im(f) = Re(i f)$ est constante au voisinage de $z$, d'où
  le résultat.
]

Ces résultats étant établis, on en déduit le corollaire suivant.

#corollary[
  Une fonction harmonique dont le module admet un maximum local
  en un point $z$ est constante au voisinage de $z$.
]




=== Analyticité des fonctions harmoniques
#lemma[
  Toute fonction $CC$-analytique est $RR$-analytique.
]

#proof[
  Soit $f : D --> CC$ une fonction qui admet un développement en série entière
  en un point $a in D$. Il existe $r > 0$ et une suite de nombres complexes
  $(a_n)_(n in NN)$ tels que
  $
    forall z in DD(r), quad f(a + z) = sum_(n=0)^(infinity) a_n z^(n).
  $
  Écrivons $a = alpha + i beta$ et $z = x + i y$ avec $alpha, beta, x, y in RR$. On a, pour tout $n in NN$,
  $
    z^(n) = (x + i y)^(n) = sum_(k=0)^(n) binom(n, k) x^(k) (i y)^(n-k)
  $
  Soient $s, t in ]0, r/2[$. On a
  $
    sum_(n = 0)^(infinity) sum_(k = 0)^(n)
    abs(a_n binom(n, k) s^(k) (i t)^(n - k))
    = sum_(n = 0)^(infinity) abs(a_n) (s + t)^(n)
    lt.eq.slant sum_(n = 0)^(infinity) abs(a_n) r^(n) < infinity.
  $
  De là, pour tous $x, y in ]-r/2, r/2[$, on a
  $
    f(alpha + x, beta + y) = sum_(m, n gt.eq.slant 0) a_(m+n) binom(m+n, m)i^(n) x^(m) y^(n)
  $
  ce qui montre que $f$ est $RR$-analytique en $a$.
]

#proposition[
  Toute fonction harmonique est $RR$-analytique.
]

#proof[
  D'après la @propHarmoReelHolo, cela résulte du fait que la $RR$-analyticité
  est une propriété locale stable par combinaison linéaire
  et par passage à la partie réelle et imaginaire.
]

=== Formule de Poisson
Soit $f : D --> CC$ une fonction $CC$-analytique. Établissons
l'analogue de la formule intégrale de Cauchy pour la partie réelle
$g$ de $f$. Soit $z_0 in D$ et $rho > 0$ tels que pour tout
$z in DD(rho)$,
$
  f(z_0 + z) = sum_(n=0)^(infinity) a_n z^(n).
$
On a donc, pour $0 < r < rho$ fixé et pour tout $0 lt.eq.slant theta lt.eq.slant 2pi$,
$
  2g(z_0 + r e^(i theta)) = f(z_0 + r e^(i theta)) + overline(f(z_0 + r e^(i theta)))
  = sum_(n=0)^(infinity) r^(n)
  (a_n e^(i n theta) + overline(a_n) e^(-i n theta)).
$
Pour tout $m gt.eq.slant 1$, on a par convergence normale du membre de droite
$
  2 integral_(0)^(2pi) g(z_0 + r e^(i theta)) e^(-i m theta)dif theta =
  sum_(n = 0)^(infinity) r^(n) integral_(0)^(2pi)
  (a_n e^(i (n-m) theta) + overline(a_n)e^(-i(n+m)theta))dif theta =
  2pi r^(m) a_m
$
On en déduit, pour $abs(z) < r$
$
  f(z_0 + z) & = sum_(n = 0)^(infinity) a_n z^(n)\
  & = a_0 + 1/pi sum_(n = 1)^(infinity) integral_(0)^(2pi) g(z_0 + r e^(i theta)) (z/(r e^(i theta)))^(n) dif theta.
$
Par convergence normale en $theta$, on peut inverser les symboles somme
et intégrale, d'où
$
  f(z_0 + z) = f(z_0) + 1/pi integral_(0)^(2pi) g(z_0 + r e^(i theta))(z)/(r e^(i theta) - z)dif theta.
$
En passant à la partie réelle et en utilisant la propriété de la moyenne,
on obtient la formule de Poisson
#equation(id: "eqPoisson")[
  $
    g(z_0 + z) & = g(z_0) + 1/pi integral_(0)^(2pi) g(z_0 + r e^(i theta))
                 Re(z/(r e^(i theta) - z))dif theta \
               & = 1/(2pi) integral_(0)^(2pi) g(z_0 + r e^(i theta))
                 (1 + 2Re(z/(r e^(i theta) - z)))dif theta \
               & = 1/(2pi) integral_(0)^(2pi) g(z_0 + r e^(i theta))
                 Re((r e^(i theta) + z)/(r e^(i theta) - z))dif theta \
               & = 1/(2pi) integral_(0)^(2pi) g(z_0 + r e^(i theta))
                 Re((r e^(i theta) + z)(r e^(-i theta) - overline(z)))/abs(r e^(i theta) - z)^(2) dif theta \
               & = 1/(2pi) integral_(0)^(2pi) g(z_0 + r e^(i theta))
                 (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2)dif theta.
  $
]
En particulier, si $g : D --> RR$ est une fonction harmonique réelle
et $overline(DD)(z_0, r) subset D$, $g$ est la partie réelle d'une
fonction holomorphe sur un voisinage $DD(z_0, rho) subset D$ avec $rho > r$,
qui est donc analytique en $z_0$ avec rayon $gt.eq.slant rho$. La fonction
$g$ vérifie donc la formule de Poisson @eqPoisson pour tout $z in DD(r)$.
En fait, la formule de Poisson reste vraie pour une fonction harmonique
à valeurs dans $CC$, comme on le voit en séparant partie réelle et
imaginaire. À $r > 0$ et $theta$ fixés, la fonction
$
  z arrow.r.long.bar (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2)
  = Re((r e^(i theta) + z)/(r e^(i theta) - z))
$
qui figure sous le signe d'intégration dans @eqPoisson
est appelée noyau de Poisson. C'est une fonction harmonique de $z$
sur $CC without {r e^(i theta)}$ comme partie réelle d'une fonction
holomorphe. Elle s'annule sur le cercle $abs(z) = r$ privé de $r e^(i theta)$.
Elle est strictement positive dans le disque $abs(z) < r$. À $abs(z) < r$ fixés,
c'est une fonction continue périodique de $theta$, et en appliquant la
formule de Poisson à la fonction harmonique constante égale à $1$, on trouve
#equation(id: "eqIntegraleNoyauPoisson")[
  $
    1/(2pi) integral_(0)^(2pi) (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta = 1.
  $
]


=== Problème de Dirichlet sur le disque
Le problème de Dirichlet consiste à trouver une fonction harmonique
sur un domaine $D$ dont la restriction à la frontière $partial D$
coïncide avec une fonction continue donnée $f : partial D --> CC$.

#theorem[
  Le problème de Dirichlet sur un disque admet une unique solution.
  De plus, la valeur de cette solution au centre du disque est
  la moyenne des valeurs de la fonction $f$ sur le bord du disque.
]<thDirichletDisque>

L'idée de la démonstration est de construire une solution sous forme
intégrale à l'aide de la formule de Poisson. L'unicité est une
conséquence du principe du maximum. Soient $DD := DD(z_0, r)$ un
disque de $CC$, et $f : partial DD --> CC$ une fonction continue.
On considère la paramétrisation de $partial DD$ usuelle
$
  gamma : RR --> partial DD, quad theta arrow.r.long.bar z_0 + r e^(i theta).
$
Étant donnés $eta > 0$ et $alpha in RR$, on note
$ A_(alpha, eta) := gamma^(-1)(gamma(]alpha - eta, alpha + eta[)) $
l'ensemble des points dont l'image sur le cercle est à distance angulaire
inférieure à $eta$ de $gamma(alpha)$.

#lemma[
  Soit $G : overline(DD) --> CC$ une fonction continue,
  dont la restriction à $DD$ satisfait au principe du maximum,
  et nulle sur $partial DD$. Alors $G$ est identiquement nulle.
  C'est en particulier le cas si $G$ est harmonique dans $DD$
]<lemHarmoNulleBord>

#proof[
  Comme $G$ est nulle sur $partial DD$, il existe un point $z in
  DD$ où $abs(G)$ atteint son maximum. D'après le principe du
  maximum, $G^(-1)(G(z))$ est un ouvert de $DD$. Il est aussi
  fermé par continuité. Comme $DD$ est connexe, on en déduit que
  $G$ est constante sur $DD$, donc nulle par continuité.
]


#lemma[
  Soient $eta, alpha$ deux réels avec $0 < eta < pi$, de sorte que
  $[0, 2pi] without A_(alpha, eta)$ soit d'intérieur non vide. Alors,
  $
    integral_([0, 2pi] without A_(alpha, eta)) (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta
    stretch(arrow)_(z -> r e^(i alpha)\ abs(z) < r) 0.
  $
]<lemNoyauPoissonHorsVoisinage>

#proof[
  Notons $A := A_(alpha, eta)$ pour alléger les notations.
  Soit $0 < rho < 1/2 abs(1 - r e^(i eta)) =: mu$.
  Pour tous $theta in [0, 2pi] without A$ et $z in DD(r) inter DD(r e^(i alpha), rho)$,
  on a
  $
    abs(r e^(i theta) - z) & > mu > 0.
  $
  Il suit
  $
    0 lt.eq.slant integral_([0, 2pi] without A) (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta
    lt.eq.slant (4 pi r rho)/(mu^(2)).
  $
  En prenant $rho$ arbitrairement petit, on obtient le résultat.
]

#proof(title: [Démonstration du @thDirichletDisque])[

  _Montrons l'unicité_.
  Soient $F_1, F_2 : overline(DD) --> CC$ deux solutions au
  problème de Dirichlet sur $DD$ associé à $f$. Alors la différence
  $G = F_1 - F_2$ est continue sur $overline(DD)$, harmonique
  dans $DD$ et nulle sur $partial DD$. D'après le
  @lemHarmoNulleBord, $G$ est identiquement nulle, donc
  $F_1 = F_2$.

  _Montrons l'existence_. Le problème de Dirichlet étant linéaire,
  il suffit de le résoudre pour $f$ à valeurs réelles, ce que l'on suppose
  désormais. Notons respectivement
  $z_0$ et $r$ le centre et le rayon de $DD$. On pose, pour
  $abs(z) < r$
  $
    F(z_0 + z) = 1/(2 pi) integral_(0)^(2 pi) f(z_0 + r e^(i theta))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta
    = Re(
      1/(2 pi) integral_(0)^(2 pi) f(z_0 + r e^(i theta))
      (r e^(i theta) + z)/(r e^(i theta) - z) dif theta
    ).
  $
  Dans le membre de droite, l'intégrande est une fonction continue
  de $(theta, z)$ et holomorphe en $z$. Par différentiation sous le signe
  d'intégration, on en déduit que $F$ est la partie réelle d'une fonction
  holomorphe sur $DD$, donc harmonique. Soit $alpha in RR$. Montrons que
  $
    F(z_0 + z) stretch(arrow)_(z -> r e^(i alpha)) f(z_0 + r e^(i alpha)).
  $
  D'après @eqIntegraleNoyauPoisson, on a
  $
    F(z_0 + z) - f(z_0 + r e^(i alpha)) =
    1/(2 pi) integral_(0)^(2 pi) (f(z_0 + r e^(i theta)) - f(z_0 + r e^(i alpha)))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta.
  $
  Soit $epsilon > 0$. Par continuité de $f$ en $z_0 + r e^(i alpha)$,
  il existe $0 < eta < pi$ tel que pour tout $theta in A_(alpha, eta)$, on ait
  $
    abs(f(z_0 + r e^(i theta)) - f(z_0 + r e^(i alpha))) lt.eq.slant epsilon/2.
  $
  Encore par continuité de $f$ et compacité de $partial DD$, il existe
  $M > 0$ tel que $abs(f(zeta)) lt.eq.slant M$ pour tout $zeta in partial DD$.
  On en déduit
  $
    abs(F(z_0 + z) - f(z_0 + r e^(i alpha))) lt.eq.slant
    epsilon/2 1/(2 pi) integral_(A_(alpha, eta))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta +
    (2M)/(2 pi) integral_([0, 2pi] without A_(alpha, eta))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta.
  $
  Or, d'après le @lemNoyauPoissonHorsVoisinage et @eqIntegraleNoyauPoisson, on a
  $
    integral_([0, 2pi] without A_(alpha, eta))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta
    stretch(arrow)_(z -> r e^(i alpha)) 0 quad "et" quad
    1/(2pi) integral_(A_(alpha, eta))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta
    stretch(arrow)_(z -> r e^(i alpha)) 1.
  $
  Ainsi, pour $z in DD(r)$ suffisamment proche de $r e^(i alpha)$, on obtient
  $
    abs(F(z_0 + z) - f(z_0 + r e^(i alpha))) < epsilon.
  $
  Cela montre que $F$ se prolonge en une fonction continue sur $overline(DD)$
  dont la restriction à $partial DD$ coïncide avec $f$.
  Enfin, on a
  $
    F(z_0) = 1/(2 pi) integral_(0)^(2 pi) f(z_0 + r e^(i theta)) (r^(2) - abs(0)^(2))/abs(r e^(i theta) - 0)^(2) dif theta
    = 1/(2 pi) integral_(0)^(2 pi) f(z_0 + r e^(i theta)) dif theta.
  $
  Cela conclut la preuve.
]

=== Caractérisation des fonctions harmoniques par la propriété de la moyenne
#theorem[
  Soit $f : D --> CC$ une fonction continue. Alors $f$ est harmonique si et seulement si
  elle satisfait la propriété de la moyenne.
]<thCaracHarmoMoyenne>

#proof[
  On a déjà vu que toute fonction harmonique satisfait la propriété de la moyenne à
  la @propPropMoyenneHarmo. Réciproquement, supposons que $f$ satisfasse la propriété
  de la moyenne. L'harmonicité étant une propriété locale, prenons un disque fermé
  $K subset D$ et montrons que $f$ est harmonique à l'intérieur de $K$. Cela suffit
  car on peut recouvrir $D$ par une famille de tels disques. D'après le
  @thDirichletDisque, il existe une fonction continue $g : K --> CC$ harmonique
  à l'intérieur de $K$ et coïncidant avec $f$ sur la frontière de $K$. Alors $g - f$
  satisfait la propriété de la moyenne, donc le principe du maximum à l'intérieur de $K$
  et est nulle sur la frontière de $K$. D'après le @lemHarmoNulleBord, on en déduit
  que $g - f$ est identiquement nulle sur $K$. En particulier, $f$ est harmonique
  à l'intérieur de $K$.
]

=== Singularité effaçable pour les fonctions harmoniques
Le théorème de la singularité effaçable, connu pour les fonctions holomorphes,
admet un énoncé analogue valable plus généralement pour les fonctions harmoniques.
On note $ psi : DD^(*) --> RR, quad z arrow.r.long.bar - ln abs(z) $

#theorem(title: [Singularité effaçable])[
  Soit $f : DD^(*) --> CC$ une fonction harmonique telle que $f = o(psi)$ en $0$.
  Alors $f$ se prolonge en une fonction harmonique sur $DD$.
]<thSingulariteEffacableHarmo>

#proof[
  En séparant partie réelle et imaginaire, on voit qu'il suffit de
  prouver le théorème dans le cas où $f$ est à valeurs réelles. Notons $B = DD(1/2)$,
  et $g : B --> RR$ la fonction harmonique qui coïncide avec $f$ sur $partial B$.
  Comme $g$ est bornée, on a $f - g = o(psi)$ en $0$. Soient $z in B without { 0 }$ et
  $epsilon > 0$. Il existe $0 < delta < abs(z)$ tel que
  $abs(f - g) lt.eq.slant epsilon psi$ sur $DD(delta)$. Comme $f - g - epsilon psi$
  est harmonique sur $B without { 0 }$ et négative sur $partial DD(delta) union partial B$,
  le principe du maximum donne
  $
    forall delta lt.eq.slant abs(w) lt.eq.slant 1/2, quad f(w) - g(w) - epsilon psi(w)
    lt.eq.slant 0.
  $
  En particulier, on a $f(z) - g(z) lt.eq.slant epsilon psi(z)$. Le même raisonnement
  appliqué à $g - f - epsilon psi$ montre que $g(z) - f(z) lt.eq.slant epsilon psi(z)$.
  On a obtenu
  $
    forall epsilon > 0, quad abs(f(z) - g(z)) lt.eq.slant epsilon psi(z),
  $
  donc $f = g$ sur $B without { 0 }$. Ainsi, $g$ fournit le prolongement recherché.
]

=== Suites de fonctions harmoniques et principe de Harnack

#proposition[
  Soit $(f_n)_(n in NN)$ une suite de fonctions harmoniques sur $D$
  qui converge uniformément sur les compacts. Alors la limite est harmonique
  sur $D$.
]<propLimiteHarmo>

#proof[
  Le domaine $D$ est localement compact, donc la suite $(f_n)$ converge simplement
  vers $f : D --> CC$ continue et vérifiant la propriété de la moyenne, donc harmonique
  par le @thCaracHarmoMoyenne.
]

#theorem(title: [Harnack])[
  Soit $(f_n)_(n in NN)$ une suite croissante
  de fonctions harmoniques sur $DD(R)$. On note $f = sup_(n in NN) f_n$.
  Alors, ou bien $f equiv +infinity$, ou bien $f$ est harmonique et la suite $(f_n)_(n in NN)$
  converge uniformément sur tout compact de $DD(R)$ vers $f$.
]<thHarnack>

#proof[
  Soit $K$ un compact de $DD(R)$. Posons $rho := max_(z in K) abs(z) < R$,
  de sorte que $K subset overline(DD)(rho) subset DD(R)$. On se donne
  également $r$ tel que $rho < r < R$. Appliquons la formule de Poisson
  à $f_n - f_m$ pour $m lt.eq.slant n in NN$ sur le disque $overline(DD)(r)$.
  Pour tout $z in overline(DD)(rho)$, on a
  $
    0 lt.eq.slant (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2)
    = Re((r e^(i theta) + z)/(r e^(i theta) - z))
    lt.eq.slant abs(r e^(i theta) + z)/abs(r e^(i theta) - z)
    lt.eq.slant (r + abs(z))/(r - abs(z))
    lt.eq.slant (r + rho)/(r - rho),
  $
  d'où pour $z in K,$
  $
    0 lt.eq.slant (f_n - f_m)(z) & = 1/(2 pi) integral_(0)^(2 pi) (f_n - f_m)(r e^(i theta))
    (r^(2) - abs(z)^(2))/abs(r e^(i theta) - z)^(2) dif theta\
    & lt.eq.slant (r + rho)/(r - rho) 1/(2 pi) integral_(0)^(2 pi) (f_n - f_m)(r e^(i theta)) dif theta\
    & lt.eq.slant (r + rho)/(r - rho) (f_n - f_m)(0).
  $
  Si $f(0) < +infinity$, le critère de Cauchy uniforme montre que la suite $(f_n)_(n in NN)$ converge uniformément
  sur $K$. La limite est harmonique sur $DD(R)$ par la @propLimiteHarmo.
  Plus généralement, si $f$ n'est pas identiquement égale à $+infinity$,
  il existe $a in DD$ tel que $f(a) < +infinity$. On applique le raisonnement précédent
  à la suite $(g_n = f_n compose psi)_(n in NN)$ où
  $
    psi : DD(R) arrowTildeLong DD(R), quad z arrow.r.long.bar (R^(2)(z + a))/(R^(2) + overline(a)z) = R psi_(-a)(z / R).
  $
  La fonction $psi_(-a)$ est définie à la @secSchwarzPick, et on y montre que c'est un automorphisme de $DD$ qui envoie $0$ sur $a$.
  Cela conclut la preuve.
]

== Fonctions (sous)harmoniques sur une surface de Riemann
Dans cette section, on fixe $X$ une surface de Riemann.

=== Définitions et propriétés élémentaires

#definition(title: "Fonction harmonique")[
  Une fonction continue $f : X --> CC$ est dite harmonique si, pour toute carte
  $phi : U --> X$ avec $U$ un ouvert de $CC$, la fonction $f compose phi : U --> CC$
  est harmonique.
]

On observe que l'harmonicité dans $CC$ est conservée par changement de variable holomorphe.
Il suffit pour le voir d'appliquer la règle de la chaîne. Ainsi, pour montrer
qu'une fonction $f : X --> CC$ est harmonique, il suffit de vérifier
l'harmonicité de $f compose phi$ pour une famille de cartes
recouvrant $X$.

#definition(title: "Fonction sous-harmonique, surharmonique")[
  Soit $f : X --> RR$ une fonction continue à valeurs réelles. On dit que
  $f$ est _sous-harmonique_ si, pour toute carte
  $phi : U --> X$ avec $U$ un ouvert de $CC$, et tout disque fermé
  $overline(DD)(z, r) subset U$, on a
  #equation(id: "eqDiffMoyenne")[
    $
      f compose phi(z) lt.eq.slant 1/(2 pi)
      integral_(0)^(2 pi) f compose phi(z + r e^(i theta)) dif theta.
    $
  ]
  On dit que $f$ est _surharmonique_ si $-f$ est sous-harmonique.
]

#remark[
  D'après le @thCaracHarmoMoyenne, une fonction sous-harmonique $f : X --> RR$
  est harmonique si et seulement si @eqDiffMoyenne est une égalité pour toute carte
  $phi : U --> X$ et tout disque fermé $overline(DD)(z, r) subset U$.
]

On vérifie immédiatement la stabilité des fonctions sous-harmoniques par
combinaisons linéaires à coefficients positifs. En outre, elles sont
stables par passage au supremum de deux fonctions.

#proposition[
  Un supremum de deux fonctions sous-harmoniques est une fonction sous-harmonique.
]

#proof[
  Soient $f, g : X --> RR$ deux fonctions sous-harmoniques. Alors $sup(f, g) = 1/2 (f + g + abs(f - g))$
  est continue. De plus, pour toute carte $phi : U --> X$ et tout disque $overline(DD)(z, r) subset U$, on a
  $
    f compose phi(z) lt.eq.slant 1/(2 pi) integral_(0)^(2 pi) f compose phi(z + r e^(i theta)) dif theta lt.eq.slant
    integral_(0)^(2 pi) sup(f, g) compose phi(z + r e^(i theta)) dif theta.
  $
  L'inégalité analogue est vraie pour $g$, donc elle l'est aussi pour $sup(f, g)$.
]

=== Principe du maximum et caractérisation locale des fonctions sous-harmoniques

#proposition(title: [Principe du maximum])[
  Soit $f : X --> RR$ une fonction continue localement sous-harmonique.
  Si $f$ atteint un maximum local en un point $x in X$, alors $f$ est
  constante dans un voisinage de $x$.
]<propPpeMaxLocSsHarmo>

#proof[
  Il existe une carte locale $phi : U --> CC$ centrée en $x$ telle
  que $f$ soit sous-harmonique sur $U$ et $f(x) gt.eq.slant f(y)$
  pour tout $y in U$. On se donne $DD(R)$ un
  disque contenu dans $phi(U)$. Alors, pour tout $0 < r < R$, on a
  par définition de la sous-harmonicité
  $
    0 gt.eq.slant f(x) - 1/(2 pi) integral_(0)^(2 pi)
    f compose phi^(-1)(r e^(i theta)) dif theta
    = 1/(2 pi) integral_(0)^(2 pi) (f compose phi^(-1)(0) - f compose phi^(-1)(r e^(i theta))) dif theta
    gt.eq.slant 0.
  $
  On en déduit par continuité que $f compose phi^(-1)$ est constante
  égale à $f(x)$ sur $partial DD(r)$. C'est valable pour tout $0 < r < R$,
  et $phi$ est un homéomorphisme, donc $f$ est constante égale à $f(x)$ sur
  le voisinage $phi^(-1)(DD(R))$ de $x$.
]

#definition[
  On dit qu'un ouvert connexe $D subset X$ est _un domaine régulier_ si
  $overline(D)$ est compact et si le problème de Dirichlet sur $D$ admet une unique solution pour
  toute fonction continue $f : partial D --> RR$.
]

Étant donnés une fonction continue $f : X --> RR$ et un ouvert
régulier $D subset X$, on note $f_D : X --> RR$ l'unique fonction continue,
harmonique sur $D$ et qui coïncide avec $f$ sur $X without D$.

#proposition(title: [Caractérisation des fonctions sous-harmoniques])[
  Soit $f : X --> RR$ une fonction continue. Alors les propriétés suivantes
  sont équivalentes
  #ilist[
    + La fonction $f$ est localement sous-harmonique ;
    + Pour tout ouvert régulier $D subset X$, on a
      #equation(id: "eqInegaliteSsHarmoRegulier")[
        $
          f lt.eq.slant f_D thick ;
        $
      ]
    + La fonction $f$ est sous-harmonique.
  ]
  En particulier, la sous-harmonicité est une propriété locale.
]<propCaracSsHarmo>

#proof[L'implication _(iii)_ $==>$ _(i)_ est évidente.

  _(i)_ $==>$ _(ii)_. Supposons que $f$ soit localement sous-harmonique.
  Soit $D subset X$ un domaine régulier.
  Puisque $f$ et $f_D$ coïncident en dehors de $D$,
  il suffit de montrer @eqInegaliteSsHarmoRegulier sur $D$. On
  observe que $f_D - f$ est localement sous-harmonique sur $D$ par
  combinaison linéaire. Supposons par l'absurde qu'il existe
  $x in D$ tel que $f(x) - f_(D) (x) > 0$. Le domaine $D$ étant
  relativement compact, la fonction $f - f_D$ atteint son maximum
  en un point $y in overline(D)$ ; en outre, $y in D$ car
  $f - f_D$ est nulle sur $partial D$. D'après la @propPpeMaxLocSsHarmo,
  appliquée à $g := (f - f_D)|_(D)$, l'ensemble $g^(-1)(g(y))$ est un
  ouvert de $D$. C'est également un fermé par continuité, et $D$ est
  connexe, donc $g$ est constante sur $D$. La continuité de $f - f_D$
  sur $overline(D)$ entraine $g(y) = 0$, ce qui fournit une contradiction et
  achève de montrer _(ii)_.

  _(ii)_ $==>$ _(iii)_. Supposons que @eqInegaliteSsHarmoRegulier soit satisfaite pour
  tout domaine régulier. Soit $phi : U --> X$ une carte, et
  $overline(DD)(z, r) subset U$ un disque fermé. Le @thDirichletDisque
  assure que le disque $D := phi(DD(z, r))$ est un domaine régulier et
  permet de calculer la valeur de $f_D$ en $phi(z)$.
  $
    f compose phi(z) lt.eq.slant f_D compose phi(z) = 1/(2 pi)
    integral_(0)^(2 pi) f_D compose phi(z + r e^(i theta)) dif theta
    = 1/(2 pi) integral_(0)^(2 pi) f compose phi(z + r e^(i theta)) dif theta.
  $
  Cela montre que $f$ est sous-harmonique et conclut la preuve.
]

Soient $f : X --> RR$ une fonction continue et $D$ un domaine régulier.
Alors, par le principe du maximum, on a sur $D$
$
  inf_(partial D) f lt.eq.slant f_D lt.eq.slant sup_(partial D) f.
$
En particulier, si $f$ est positive, alors $f_D$ l'est aussi.
Par linéarité du problème de Dirichlet, il suit que si
$g : X --> RR$ est une autre fonction continue telle que
$f lt.eq.slant g$, alors $f_D lt.eq.slant g_D$.

#corollary[
  Soit $f : X --> RR$ une fonction sous-harmonique et $D$ un domaine régulier. Alors
  $f_D$ est sous-harmonique.
]<corSsHarmoStableParDirichlet>

#proof[
  Soit $D prime$ un domaine régulier de $X$. Notons $g := f_D$ ; d'après la @propCaracSsHarmo
  il suffit de montrer que
  $
    g lt.eq.slant g_(D prime).
  $
  Soit $x in X$. Si $x in X without D prime$, alors $g_(D prime)(x) = g(x)$.
  La sous-harmonicité de $f$ entraine
  $f lt.eq.slant g$, puis $f lt.eq.slant f_(D prime) lt.eq.slant g_(D prime)$.
  Ainsi, si $x in X without D$, il vient
  $
    g(x) = f_(D)(x) = f(x) lt.eq.slant g_(D prime)(x).
  $
  On en déduit que $g - g_(D prime) lt.eq.slant 0$ sur $X without (D inter D prime)$.
  Comme cette fonction est de plus harmonique sur $D inter D prime$, le principe du maximum
  entraine que $g - g_(D prime) lt.eq.slant 0$ sur $D inter D prime$.
]

=== Familles de Perron
#definition(title: "Famille de Perron")[
  On dit qu'un ensemble $cal(F)$ de fonctions $X --> RR$ sous-harmoniques est une
  famille de Perron sur $X$ si
  #ilist[
    + Pour tout $f, g in cal(F)$, on a $sup(f, g) in cal(F)$ ;
    + Pour toute fonction $f in cal(F)$, tout ouvert $D$ de $X$ tel que $overline(D)$
      soit l'image d'un disque fermé de $CC$ par
      une carte, et toute fonction continue $g : X --> R$ telle que
      $
        g|_(X without D) eq f|_(X without D)
      $
      et $g$ est harmonique sur $D$, on a $g in cal(F)$.
  ]
  On dit qu'une famille de Perron $cal(F)$ est majorée (resp. bornée) s'il existe $M > 0$ tel que
  $
    forall f in cal(F), forall x in X, quad f(x) lt.eq.slant M quad ("resp." abs(f(x)) lt.eq.slant M).
  $
]<defPerron>

#theorem(title: "Perron")[
  Si $cal(F)$ est une famille de Perron non vide sur $X$,
  et $F := sup cal(F)$. Si $F$ ne vaut pas identiquement $+infinity$, alors
  elle est harmonique sur $X$.
]<thPerron>

#proof[
  Supposons pour commencer que $X = DD$. On suppose que $F eq.not +infinity$
  Soit $z_0 in DD$ tel que $F(z_0) < infinity$. On complète $z_0$ par une
  énumération $(z_(j))_(j gt.eq.slant 1)$ de $QQ times QQ inter DD$
  (qui est dense dans $DD$). Pour tout $j in NN$, on se donne une suite
  $(v_(j, k))_(k in NN)$ d'éléments de $cal(F)$ telle que
  $
    v_(j, k)(z_(j)) stretch(arrow)_(k -> +infinity) F(z_(j)).
  $
  Soit $r$ un réel tel que $abs(z_0) lt r lt 1$. On définit une suite $(w_n)_(n in NN)$
  d'éléments de $cal(F)$ par récurrence de la manière suivante
  $
    w_0 = (v_(0, 0))_(DD(r)) gt.eq.slant v_(0, 0) quad "et" quad
    w_(n+1) = [sup { w_n } union { v_(j, k) mid(|) 0 lt.eq.slant j, k lt.eq.slant n + 1 }]_(DD(r)).
  $
  Ainsi, la suite $(w_n)$ est croissante, et pour tout $n in NN$ et tous $j, k lt.eq.slant n$,
  la fonction $w_n in cal(F)$ est harmonique sur $DD(r)$ et vérifie
  $
    w_n(z_(j)) gt.eq.slant v_(j, k)(z_(j)).
  $
  On en déduit que pour tout $j in NN$,
  $
    w_n(z_(j)) stretch(arrow)_(n -> infinity) F(z_(j)).
  $
  Notons $W$ la limite simple de la suite $(w_n)_(n in NN)$. On a
  $W(z_0) = F(z_0) < + infinity$, donc $W$ est harmonique sur $DD(r)$
  par le @thHarnack. On a $W lt.eq.slant F$ sur $DD$ car les $w_n$ sont
  dans $cal(F)$. Soit $v in cal(F)$. On a, pour tout $j in NN$,
  $
    W(z_j) = F(z_j) gt.eq.slant v(z_j).
  $
  Comme $W - v$ est continue sur $DD(r)$, la densité des $z_j$ entraine
  $W gt.eq.slant v$ sur $DD(r)$. Par passage au supremum sur $cal(F)$, on
  en déduit $W gt.eq.slant F$ sur $DD(r)$. Ainsi, $W = F$ sur $DD(r)$. Comme
  on peut prendre $r$ arbitrairement proche de $1$, on en déduit que $F$ est
  harmonique sur $DD$.

  On traite maintenant le cas général. D'après ce qui précède, on sait que
  pour tout disque $Delta subset X$, $F$ est soit harmonique, soit identiquement
  égale à $+infinity$ sur $Delta$. Comme tout point de $X$ possède un voisinage
  biholomorphe à un disque, on en déduit que $F^(-1)(+infinity)$ et $F^(-1)(RR)$
  sont ouverts dans $X$. Le résultat découle alors de la connexité de $X$.
]

=== Problème de Dirichlet dans une surface de Riemann
On donne une condition suffisante pour l'existence de solutions au problème de Dirichlet
dans une surface de Riemann.

#theorem(title: "Existence de fonctions harmoniques")[
  Soit $Y$ un ouvert de $X$ tel que $overline(Y)$
  soit une sous-variété à bord lisse non vide de $X$.
  Alors, pour toute fonction continue bornée $f : partial Y --> RR$,
  il existe une fonction continue $u : overline(Y) --> RR$ harmonique sur
  $Y$ et dont la restriction à $partial Y$ est $f$.
]<thDirichletSurfaceRiemann>

#proof[
  Soient $m, M$ des réels tels que $m < inf f$ et $sup f < M$.
  Considérons l'ensemble $cal(F)$ des restrictions à $Y$ de fonctions continues
  $v : overline(Y) --> RR$, sous-harmoniques sur $Y$ et telles que
  $v|_(partial Y) lt.eq.slant f$. La fonction
  constante égale à $m$ appartient à $cal(F)$, qui est donc non vide. Comme un supremum
  de deux fonctions sous-harmoniques est sous-harmonique, $cal(F)$ vérifie le _(i)_ de la
  @defPerron. Le _(ii)_ découle quant à lui du @corSsHarmoStableParDirichlet. Ainsi,
  $cal(F)$ est une famille de Perron sur $Y$, majorée par $M$. D'après le @thPerron,
  $u := sup cal(F)$ est harmonique sur $Y$ ; bien-sûr, $u$ est à valeurs dans $[m, M]$.
  Il reste à montrer que $u$ se prolonge en une fonction continue sur
  $overline(Y)$ coïncidant avec $f$ sur $partial Y$.

  Soient $x in partial Y$ et $phi : U --> CC$ une carte holomorphe
  de $X$ centrée en $x$, de sorte que $phi(U inter partial Y)$ soit
  une sous-variété lisse de $RR^(2)$ de dimension $1$. On peut donc, quitte à réduire
  $U$, se donner une suite $(x_n)_(n in NN)$ de points de $U without overline(Y)$
  convergeant vers $x$ et telle que pour tout $n in NN$,
  #equation(id: "eqConditionRegulariteBord")[
    $
      abs(phi(x_n)) = inf_(z in phi(U inter Y))abs(phi(x_n) - z).
    $
  ]

  Pour tous $epsilon > 0$ et $n in NN$, on considère les fonctions
  $
    h_(n, epsilon) : overline(Y) & --> RR, quad
                                   y & arrow.r.long.bar cases(
                                         max(m, ln abs(phi(x_n)/(phi(y) - phi(x_n))) + f(x) - epsilon) & quad "si" y in U,
                                         m & quad "sinon"
                                       )
  $
  et
  $
    k_(n, epsilon) : overline(Y) & --> RR, quad
                                   y & arrow.r.long.bar cases(
                                         min(M, ln abs((phi(y) - phi(x_n))/phi(x_n)) + f(x) + epsilon) & quad "si" y in U,
                                         M & quad "sinon".
                                       )
  $

  #lemma[
    Pour tout réel $epsilon > 0$,
    il existe $N in NN$ tel que pour tout $n gt.eq.slant N$,
    #ilist[
      + $h_(n, epsilon)$ est continue, sous-harmonique sur $Y$ et $h_(n, epsilon) < f$
        sur $partial Y$.
      + $k_(n, epsilon)$ est continue, surharmonique sur $Y$ et $k_(n, epsilon) > f$
        sur $partial Y$.
    ]
  ]<lemBarriersDirichlet>

  #proof[
    Soit $epsilon > 0$. On se donne $Delta subset U$ tel que $phi(Delta)$ soit un disque fermé.
    Alors, pour $n$ assez grand, et $y in U without Delta$, on a $h_(n, epsilon)(y) = m$. Donc
    $h_(n, epsilon)$ est continue et harmonique sur $overline(Y) without Delta$. La fonction
    $ overline(Y) inter U --> RR, quad y arrow.r.long.bar ln abs(phi(x_n)/(phi(y) - phi(x_n))) $
    est continue et harmonique sur $Y inter U$ comme composée d'une fonction holomorphe par une
    fonction harmonique. Par passage au sup, $h_(n, epsilon)$ est sous-harmonique sur $Y inter U$.
    Cela montre que $h_(n, epsilon)$ est continue et sous-harmonique sur $Y$.
    La condition @eqConditionRegulariteBord assure que $h_(n, epsilon) < f$ sur $partial Y$. Cela montre
    _(i)_. La preuve de _(ii)_ est similaire.
  ]

  Soit $epsilon > 0$. On se donne $N in NN$ vérifiant les propriétés du @lemBarriersDirichlet.
  Alors $h_(n, epsilon)|_(Y) in cal(F)$. Or, $h_(n, epsilon)(x) gt.eq.slant f(x) - epsilon$,
  donc il existe un voisinage $V$ de $x$ dans $overline(Y)$
  tel que pour tout $y in V$,
  $
    u(y) gt.eq.slant h_(n, epsilon)(y) gt.eq.slant f(x) - 2 epsilon.
  $
  De même, $k_(n, epsilon)(x) lt.eq.slant f(x) + epsilon$, donc il existe un voisinage
  $W$ de $x$ dans $overline(Y)$ tel que pour tout $y in W$,
  $k_(n, epsilon)(y) lt.eq.slant f(x) + 2 epsilon.$ Or, pour tout $v in cal(F)$,
  la fonction $v - k_(n, epsilon)$ est sous-harmonique sur $Y$ et se prolonge en une fonction
  continue sur $overline(Y)$, négative sur $partial Y$. Par le principe du maximum,
  on en déduit que $v lt.eq.slant k_(n, epsilon)$ sur $overline(Y)$. En particulier,
  $
    u(y) lt.eq.slant k_(n, epsilon)(y) lt.eq.slant f(x) + 2 epsilon
  $
  sur $W$. Ainsi pour tout $y in V inter W$,
  $
    abs(u(y) - f(x)) lt.eq.slant 2 epsilon.
  $
  Cela montre que $u(y) stretch(arrow)_(y -> x) f(x)$, et conclut la preuve.
]

=== Fonctions de Green
On garde la notation $X$ pour une surface de Riemann connexe non compacte. On
appelle _pièce_ de $X$ une sous-variété à bord lisse compacte connexe de $X$
de dimension $2$ sur $RR$. Cette notion sera étudiée plus en détail
dans la @secRemplissagePieces.

#definition(title: "Fonction de Green")[
  Soit $P$ une pièce de $X$ et $a in circle(P)$. Une _fonction de Green relative au
  couple $(P, a)$_ est une fonction continue $G : P without { a } --> RR$, nulle sur $partial P$,
  harmonique sur $circle(P) without { a }$ pour laquelle il existe une carte locale $phi : U --> CC$
  centrée en $a$ avec $U subset circle(P)$ et une fonction harmonique $h : U --> RR$
  telles que $G + ln abs(phi) = h$ sur $U without { a }$.
]<defFonctionGreen>

#remark[
  Avec les notations de la @defFonctionGreen, si $psi : V --> RR$ est une autre carte locale
  centrée en $a$ avec $V subset circle(P)$, on a sur $U inter V without { a }$,
  $
    G + ln abs(psi) & = h + ln abs(psi/phi).
  $
  Or
  $psi compose phi^(-1) : phi(U inter V) --> psi(U inter V)$
  est un biholomorphisme nul en $0$, donc il s'écrit sous la forme $z arrow.r.long.bar z g(z)$
  avec $g$ holomorphe non nulle en $0$. De là, il vient
  $
    ln abs(psi/phi) = ln abs(g compose phi),
  $
  qui se prolonge donc en une fonction harmonique sur $U inter V$. Ainsi, pour toute
  carte $psi$, $G + ln abs(psi)$ se prolonge en une fonction harmonique sur un voisinage
  non épointé de $a$, ce qui montre que  la @defFonctionGreen est indépendante du choix de la carte.

]

#lemma[
  Soit $P$ une pièce de $X$, $a in circle(P)$ et $phi : U arrowTildeLong DD(R)$ une carte centrée en $a$
  avec $U subset circle(P)$.
  Alors, il existe une fonction continue $k : P without { a } --> RR$, nulle sur $partial P$,
  surharmonique sur $circle(P) without { a }$ et telle que $k + ln abs(phi)$ soit constante au voisinage de $a$.
]<lemFonctionSurharmoniqueLog>

#proof[
  Soit $r$ un réel tel que $0 < r < R$.
  Notons $W := phi^(-1)(DD(r)) subset U$. On considère la fonction continue $h : P without W --> RR$
  valant $0$ sur $partial P$, $1$ sur $partial W$ et harmonique dans $circle(P) without overline(W)$.
  On définit également, pour tout $alpha > 0$, les fonctions
  $ u_alpha = - ln abs(phi) + ln r + alpha : U without { a } --> RR $
  et
  $
    v_(alpha) : P without { a } & --> RR, quad cases(
                                    v_(alpha) = u_alpha & quad "sur" W without { a },
                                    v_(alpha) = alpha h & quad "sur" P without W.
                                  )
  $
  Alors $v_(alpha)$ est continue,  harmonique sur $circle(P) without overline(W)$
  et sur $W without { a }$ et vérifie
  $ v_(alpha)|_(partial P) = 0 quad "et" quad v_(alpha)|_(partial W) = alpha. $
  Par construction, $v_(alpha) + ln abs(phi)$ est constante sur $W without { a }$.
  Il ne reste qu'à montrer que pour $alpha$ bien choisi, $v_(alpha)$ est
  surharmonique sur $circle(P) without { a }$. On a vu que la surharmonicité est
  une propriété locale, donc il suffit de vérifier l'inégalité de la moyenne
  @eqDiffMoyenne sur $partial W$.
  Soit $rho$ un réel tel que $r < rho < R$. Comme $h$ est harmonique non constante
  sur $circle(P) without overline(W)$, le principe du maximum assure que
  $
    0 < m := sup_(partial DD(rho)) h compose phi^(-1) < 1.
  $
  La solution au problème de Dirichlet sur la couronne
  $A_(rho) := { z in CC mid(|) r lt.eq.slant abs(z) lt.eq.slant rho }$
  avec valeur $m$ sur $partial DD(rho)$ et $alpha$ sur $partial DD(r)$ est donnée par
  $
    w_(alpha)(z) = (alpha - m) / (ln r/rho) ln abs(z)/rho + m.
  $
  Le principe du maximum assure que pour tout $alpha > 0$,
  $alpha h lt.eq.slant w_(alpha)$ sur $A_(rho)$. Par concavité de la fonction
  $ln$, on a également
  #equation(id: "ineqwConcavite")[
    $
      w_(alpha)(z) lt.eq.slant (alpha -m) / (r - rho) (abs(z) - rho) + m.
    $
  ]

  De plus, pour $alpha$ assez grand, puisque $r < rho$,
  $
    (alpha - m) / (r - rho) < - 1 / r,
  $
  qui n'est autre que la dérivée radiale de $u_alpha$ sur $partial DD(r)$.
  Fixons un tel $alpha$. Encore par concavité de la fonction $ln$ et par @ineqwConcavite,
  on a, pour $z in A_(rho)$,
  $
    u_alpha(z) gt.eq.slant - 1 / r (abs(z) - r) + alpha gt.eq.slant w_(alpha)(z)
    gt.eq.slant alpha h(z).
  $
  Ceci étant valable pour un choix arbitraire de $rho$, on en déduit
  $u_alpha gt.eq.slant alpha h$ sur $U without W$, d'où $v_(alpha) lt.eq.slant u_(alpha)$
  sur $U without { a }$. Ainsi, si $z in partial DD(r)$ et
  $overline(DD)(z, delta) subset U without { a }$, on obtient par harmonicité de $u_alpha$
  $
    v_(alpha)compose phi^(-1)(z) & = alpha = u_alpha compose phi^(-1)(z) \
    & = 1/(2pi) integral_(0)^(2pi) u_alpha compose phi^(-1)(z + delta e^(i theta)) dif theta\
    & gt.eq.slant 1/(2pi) integral_(0)^(2pi) v_(alpha) compose phi^(-1)(z + delta e^(i theta)) dif theta.
  $
  Cela montre que $v_(alpha)$ est surharmonique sur $circle(P) without { a }$, et achève la preuve.
]

#theorem[
  Soit $P$ une pièce de $X$ et $a in circle(P)$. Alors, il existe une unique
  fonction de Green relative au couple $(P, a)$.
]

#proof[
  _Montrons l'unicité_. Soient $G_1, G_2$ deux fonctions de Green relatives à $(P, a)$.
  Alors, $G := G_1 - G_2$ s'étend par définition en une fonction
  continue encore notée $G : P --> RR$ et harmonique sur $circle(P)$. Comme $G|_(partial P) eq 0$,
  le principe du maximum assure que $G eq 0$ sur $P$.

  _Montrons l'existence_. Soit $phi : U --> CC$ une carte locale centrée en $a$, avec
  $U subset circle(P)$, et dont l'image contient un disque $DD(r)$ avec $r > 1$.
  On considère l'ensemble $cal(F)$
  des restrictions à $circle(P) without { a }$ de fonctions continues
  $f : P without { a } --> RR$, nulles sur $partial P$, sous-harmoniques sur
  $circle(P) without { a }$ et telles que $f + ln abs(phi)$ soit majorée au
  voisinage de $a$. On vérifie aussitôt que $cal(F)$ est une famille de Perron sur
  $circle(P) without { a }$. Elle est non vide car la fonction
  $lambda = sup(0, - ln abs(phi)) : circle(P) without { a } --> RR$ est dans $cal(F)$.
  Soit $k : P without { a } --> RR$
  une fonction continue, nulle sur $partial P$, surharmonique sur $circle(P) without { a }$
  et telle que $k + ln abs(phi)$ soit constante au voisinage de $a$ donnée par le
  @lemFonctionSurharmoniqueLog. Alors, pour toute
  fonction $f : P without { a } --> RR$ dont la restriction à $circle(P) without { a }$ appartient
  à $cal(F)$, la fonction $f - k$ se prolonge en une fonction sous-harmonique sur $circle(P)$.
  Le principe du maximum assure qu'elle est négative. En particulier,
  $f lt.eq.slant k$ sur $P without { a }$. D'après le @thPerron, la fonction
  $G := sup cal(F) : circle(P) without { a } --> RR$ est harmonique. De plus,
  $lambda lt.eq.slant G lt.eq.slant k$ donc $u$ se prolonge en une fonction continue
  sur $P without { a }$, nulle sur $partial P$. Enfin, $G + ln abs(phi)$ est harmonique
  sur $U without { a }$ et bornée au voisinage de $a$. Elle se prolonge donc en une fonction
  harmonique sur $U$ par le #ref(<thSingulariteEffacableHarmo>, supplement: "Théorème de la singularité effaçable").
  Ainsi, $G$ est une fonction de Green relative au couple $(P, a)$.
]

== Inégalités d'Erdős et Koebe
=== Théorème de Schwarz-Pick <secSchwarzPick>

#theorem(title: [Lemme de Schwarz])[
  Soit $f : DD --> CC$ une application holomorphe telle que $f(0) = 0$ et
  $abs(f(z)) lt.eq.slant 1$ pour tout $z in DD$. Alors, pour tout $z in DD$,
  $ abs(f(z)) lt.eq.slant abs(z) quad "et" quad abs(f prime (0)) lt.eq.slant 1. $
  De plus, si $abs(f(z)) = abs(z)$
  pour un certain $z in DD^(*)$ ou si $abs(f prime (0)) = 1$, alors $f$ est une
  rotation de rapport $f^(prime)(0)$.
]<thSchwarz>

#proof[
  Comme $f$ est analytique en $0$, il existe une fonction holomorphe
  $g : DD --> CC$ telle que $f(z) = z g(z)$ pour tout $z in DD$ et $g(0) = f prime (0)$.
  Pour tous $r$ tel que $0 < r < 1$ et $z in partial DD(r)$, on a
  $
    abs(g(z)) = abs(f(z)) / abs(z) lt.eq.slant 1 / r.
  $
  D'après le principe du maximum appliqué à $g$, on en déduit que $abs(g) lt.eq.slant 1/r$
  sur $overline(DD)(r)$. Ceci étant valable pour $r$ arbitraire, il suit que $abs(g) lt.eq.slant 1$
  sur $DD$. Si $abs(g)$ atteint $1$ en un point de $DD$, alors $g$ est constante de module $1$,
  autrement dit $f(z) = f prime (0) z$ pour tout $z in DD$ avec $abs(f prime (0)) = 1$.
]

#corollary(title: [Théorème de Schwarz-Pick])[
  Soit $f : DD --> DD$ une application holomorphe. Alors, pour tous $z, w in DD$,
  $
    abs((f(z) - f(w)) / (1 - overline(f(w)) f(z))) lt.eq.slant abs((z - w) / (1 - overline(w) z)).
  $
]<corSchwarzPick>

Pour préparer la preuve, considérons, $w in DD$ étant donné, l'application méromorphe
$
  phi_(w) : CC --> CC, quad z arrow.r.long.bar (z - w) / (1 - overline(w) z).
$
Si $w = 0$, ce n'est autre que l'identité. Sinon, elle induit un
biholomorphisme de $CC without { overline(w)^(-1) }$ sur $CC without { - overline(w)^(-1) }$,
d'inverse
$
  phi_(w)^(-1) = phi_(-w) : CC without { - overline(w)^(-1) } --> CC without { overline(w)^(-1) }, quad z arrow.r.long.bar (z + w) / (1 + overline(w) z).
$
Elle est holomorphe au voisinage de $overline(DD)$ et pour tout $z in partial DD$,
$ abs(phi_(w)(z)) = abs(z - w) / abs(1 - overline(w)z) = abs(z - w) / abs(overline(z - w)) = 1. $
Par le principe du maximum, $psi_(w) := phi_(w)|_(DD)$ étant non constante, elle est à valeurs dans $DD$, et
est donc un automorphisme de $DD$.

#proof(title: [Démonstration du @corSchwarzPick])[
  Fixons $w in DD$ et considérons l'application holomorphe de $DD$ dans lui-même
  $g := psi_(f(w)) compose f compose psi_(-w)$. Par construction, on a $g(0) = 0$.
  Le @thSchwarz assure que pour tout $z in DD$,
  $abs(psi_(f(w)) compose f) = abs(g compose psi_(w)) lt.eq.slant abs(psi_(w))$,
  ce qui s'écrit explicitement, pour $z in DD$
  $
    abs((f(z) - f(w)) / (1 - overline(f(w)) f(z)))
    lt.eq.slant abs((z - w) / (1 - overline(w) z)).
  $
]

#corollary[
  Soient $R, R prime$ des réels tels que $0 < R < R prime$, et $f : DD(R) --> DD(R prime)$
  une application holomorphe telle que $f(0) = 0$ et $f prime (0) = 1$.
  Alors, pour tout $z in DD(R)$,
  $
    abs(f(z) - z) lt.eq.slant abs(z)^(2)/R^(2) (R prime^(2) - R^(2)) / (R prime - abs(z)).
  $
]<corBorneSchwarzPick>

#proof[
  Soit $g : DD --> DD$ la fonction holomorphe définie par
  $
    g(z) = f(R z) / (R prime) .
  $
  On a $g(0) = 0$ et $g prime (0) = R / (R^(prime)) < 1$. Le @thSchwarz assure que
  la fonction $h$ définie sur $DD$ par
  $ h(z) = g(z) / z "si" z eq.not 0 quad "et" quad h(0) = g prime (0) $
  est holomorphe à valeurs dans $DD$.
  Appliquons alors le @corSchwarzPick à $h$, $z / R$ et $w = 0$ avec $z in DD(R)$ fixé ; on obtient

  #equation(id: "eqBorneSP")[
    $
      abs(u) lt.eq.slant abs(psi_(0)(z / R)) = abs(z) / R.
    $
  ]
  Où $u := psi_(h(0)) compose h(z / R)$. De plus, on a
  $
    (f(z) R) / (z R prime) = h(z / R) = psi_(-h(0))(u) = (u + h(0)) / (1 + overline(h(0)) u)
    = (u + R/R^(prime)) / (1 + R/R^(prime) u).
  $
  En réarrangeant, il vient
  $
    f(z) - z = z ((R prime) / R (u + R/R^(prime)) / (1 + R/R^(prime) u) - 1)
    = z u (R^(prime)/R - R/R^(prime)) / (1 + R/R^(prime) u) = z/R u (R^(prime 2) - R^(2)) / ( R^(prime) + R u).
  $
  En passant au module et en majorant en utilisant @eqBorneSP, on obtient finalement
  $
    abs(f(z) - z) lt.eq.slant abs(z) / R abs(u) (R prime^(2) - R^(2)) / (R prime - R abs(u))
    lt.eq.slant abs(z)^(2)/R^(2) (R prime^(2) - R^(2)) / (R prime - abs(z)),
  $
  d'où le résultat.
]

=== Théorème de l'aire de Gronwall, conjecture de Bieberbach pour $n = 2$
#definition(title: [Fonctions schlight])[
  Soit $U$ un ouvert de $CC$ contenant $0$. Une application holomorphe
  $f : U --> CC$ est dite _schlight_ si elle est injective et vérifie
  $
    f(0) = 0 quad "et" quad f prime (0) = 1.
  $
]

On note $cal(S)(U)$ l'ensemble des fonctions schlight définies sur $U$. Si $U = DD(r)$
on écrit simplement $cal(S)(r)$. On écrit également $cal(S)$ au lieu de $cal(S)(1)$.

#lemma(title: [Théorème de l'aire de Gronwall])[
  Soit $f in cal(S)$. Alors, la fonction
  $
    g : CC without overline(DD) --> CC, quad z arrow.r.long.bar 1 / f(1 / z)
  $
  admet un développement en série de Laurent convergeant sur $CC without overline(DD)$ de la forme
  #equation(id: "eqThAire")[
    $
      g(z) = z + sum_(n = 0)^(infinity) b_n z^(-n), quad "avec" quad
      sum_(n = 1)^(infinity) n abs(b_n)^(2) lt.eq.slant 1.
    $
  ]
]<lemThAireGronwall>

L'idée de la preuve est assez simple. On calcule l'aire du complémentaire de l'image de $g$
dans $CC$ en fonction des coefficients $b_n$ grâce à la formule de Stokes. La positivité
de cette aire fournit l'inégalité @eqThAire. Cependant, on prend ici garde à
justifier soigneusement chaque étape sans utiliser le théorème de la
courbe fermée de Jordan, ce qui rend la démonstration un peu fastidieuse.

#proof[
  La fonction $z arrow.r.long.bar f(z) / z$ se prolonge en une fonction holomorphe sur $DD$ qui
  ne s'annule pas et vaut $1$ en $0$.
  Son inverse $h : DD --> CC^(*)$ est donc également holomorphe. La fonction $h$ admet donc
  un développement en série entière en $0$ convergeant sur $DD$, de la forme
  $
    h(z) = 1 + sum_(n = 0)^(infinity) b_(n) z^(n+1).
  $
  Pour tout $z in DD^(*)$, $1/f(z) = 1/z h(z)$. De là, on obtient pour $z in CC without overline(DD)$,
  $
    g(z) = z h(1/z) = z (1 + sum_(n = 0)^(infinity) b_(n) z^(-n - 1))
    = z + sum_(n = 0)^(infinity) b_(n) z^(-n)
  $
  Montrons maintenant l'inégalité @eqThAire. Pour cela, l'idée est de calculer
  l'aire du complémentaire dans $CC$ de l'image de $g$. Voici ce que l'on fait précisément.
  Soit $r > 1$ un réel. On considère l'ensemble
  $
    K_(r) := CC without g(CC without overline(DD)(r)).
  $
  C'est un sous ensemble fermé car $g$ est une application ouverte.
  Il est également borné. En effet, $f$ induit un biholomorphisme entre deux voisinages
  de $0$, ce qui implique que l'image de $CC without overline(DD)(r)$ contient un
  voisinage de l'infini. Ainsi, $K_r$ est compact. Calculons son aire
  $
    A_r := integral_(K_(r)) dif x and dif y.
  $
  Montrons que $K_r$ est une sous-variété à bord lisse de $CC$ de dimension $2$ sur $RR$.
  Premièrement, l'ouvert $g(DD(r) without overline(DD))$ est contenu dans $K_r$ par injectivité
  de $g$, donc $K_r$ a un intérieur non vide. Deuxièmement, mettons en évidence un redressement
  au voisinage de chaque point de la frontière de $K_r$, que l'on commence par déterminer.
  On a
  $
    partial K_(r) = partial g(CC without overline(DD)(r)).
  $
  La continuité de $g$ implique
  $
    g(CC without DD(r)) subset overline(g(CC without overline(DD)(r))).
  $
  L'inclusion réciproque vient du fait que $g$ est propre (car $g tilde id$ au voisinage de $infinity$).
  En effet, si $g(p_n) stretch(arrow)_(n -> infinity) q$, avec $abs(p_n) > r$ pour tout $n in NN$,
  alors la suite $(p_n)_(n in NN)$ est bornée, donc admet une valeur d'adhérence $p in CC$ telle que
  $abs(p) gt.eq.slant r$. Par continuité de $g$, on a $g(p) = q$, donc
  $q in g(CC without overline(DD)(r))$.
  On en déduit l'égalité
  $
    partial K_r = g(CC without DD(r)) without g(CC without overline(DD)(r)) = g(partial DD(r)).
  $
  Comme $g$ est holomorphe, elle s'écrit localement comme un monôme, à composition à droite
  près par un biholomorphisme. Par injectivité de $g$, un tel monôme est nécessairement
  de degré $1$, ce qui montre que $g^(prime)$ ne s'annule pas. Pour tout $z = g(xi) in partial K_r$,
  avec $xi in partial DD(r)$, il existe donc, par inversion locale,
  des ouverts $U, V subset CC$ contenant respectivement $xi$ et $z$
  tels que $g|_U : U --> V$ soit un biholomorphisme. De plus,
  $ V inter partial K_r = g(U inter partial DD(r)) quad "et" quad V inter circle(K_r) = g(U inter DD(r)). $
  Cela fournit un redressement convenable de $K_r$ au voisinage de $z$. De plus, on remarque
  que le lacet
  $
    gamma_(r) : [0, 2pi] --> CC, quad theta arrow.r.long.bar g(r e^(i theta))
  $
  est une paramétrisation régulière de $partial K_r$, compatible avec l'orientation de $K_r$.
  On peut donc appliquer la formule de Stokes pour calculer $A_r$. Rappelons que
  $
    dif x and dif y = 1/(4i)(dif overline(z) and dif z - dif z and dif overline(z))
    = i/2 dif z and dif overline(z)
    = 1/(2 i) dif (overline(z) dif z).
  $
  Il suit
  $
    A_(r) & = 1/(2 i) integral_(K_r) dif (overline(z) dif z)
            = 1/(2 i) integral_(gamma_(r)) overline(z) dif z
            = 1/(2i) integral_(partial DD(r)) overline(g(z)) g prime (z) dif z.
  $

  On utilise maintenant le développement en série de Laurent de $g$ pour calculer
  explicitement le membre de droite. Sur le cercle $partial DD(r)$,
  on a $overline(z) = r^(2)/z$, donc
  $
    overline(g(z)) = r^(2)/z + overline(b_(0)) + sum_(n = 1)^(infinity) overline(b_n) z^(n)/r^(2n).
    quad "et" quad
    g^(prime) (z) = 1 - sum_(n = 1)^(infinity) n b_n z^(-n - 1).
  $
  Les deux séries convergent normalement sur le cercle $partial DD(r)$, donc on peut
  réarranger le produit selon les degrés des monômes en $z$, et inverser les symboles
  somme et intégrale. Le seul terme qui contribue à l'intégrale est celui en $z^(-1)$.
  Or, pour $z in partial DD(r)$, le terme $overline(g(z)) g prime (z)$ s'écrit sous la forme
  $
    overline(g(z)) g prime (z) = (r^(2) - sum_(n = 1)^(infinity) n/r^(2n) b_n overline(b_n))z^(-1)
    + sum_(n in ZZ without { -1 }) c_n z^(n),
  $
  d'où
  $
    A_(r) = pi (r^(2) - sum_(n = 1)^(infinity) n/r^(2n) abs(b_n)^(2)).
  $
  Comme $A_r$ est positive, on a pour tout $r > 1$
  $
    sum_(n = 1)^(infinity) n/r^(2n) abs(b_n)^(2) lt.eq.slant r^(2).
  $
  On en déduit que la série de terme général $n abs(b_n)^(2)$ (qui domine le terme
  général du membre de gauche) converge.
  On applique alors la convergence dominée en faisant tendre $r$ vers $1$, ce qui donne
  $
    sum_(n = 1)^(infinity) n abs(b_n)^(2) lt.eq.slant 1,
  $
  et achève la preuve.
]

#theorem(title: [Bieberbach])[
  Soit $f in cal(S)$. Notons
  $
    f(z) = z + sum_(n = 2)^(infinity) a_n z^(n)
  $
  le développement en série entière de $f$ au voisinage de $0$.
  Alors $abs(a_2) lt.eq.slant 2$.
]<thmBieberbach>

#proof[
  On considère la fonction $g$ définie sur $DD$ par $g(z) = f(z^(2))$.
  Il existe une fonction holomorphe
  $h : DD --> CC$ telle que $g(z) = z^(2) h(z)$ pour tout $z in DD$ et $h(0) = 1$.
  Comme $g$ ne s'annule pas sur $DD^(*)$, $h$ ne s'annule pas sur $DD$.
  Considérons le revêtement
  $
    pi : CC^(*) --> CC^(*), quad z arrow.r.long.bar z^(2).
  $
  Le domaine $DD$ est simplement connexe, donc il existe un unique relèvement
  $tilde(h) : DD --> CC^(*)$ de $h$ le long de $pi$ tel que $tilde(h)(0) = 1$.
  Soit $tilde(g) : DD --> CC$ la fonction holomorphe donnée par $tilde(g)(z) = z tilde(h)(z).$
  On a par construction $tilde(g)^(2) = g$ sur $DD$. De plus, $tilde(g)(0) = 0$ et le choix
  $tilde(h)(0) = 1$ assure que $tilde(g) prime (0) = 1$. On remarque également que $g$ est injective
  sur $DD^(*)$, et n'atteint $0$ qu'en $0$, donc elle est injective sur $DD$. Par conséquent,
  $tilde(g)$ est également injective sur $DD$. Le @lemThAireGronwall s'applique donc à $tilde(g)$
  et donne
  #equation(id: "eqIneqAiregtilde")[
    $
      sum_(n = 1)^(infinity) n abs(b_n)^(2) lt.eq.slant 1,
    $
  ]
  où les $b_n$ sont tels que
  $
    1/(tilde(g)(1/z)) = z + sum_(n = 0)^(infinity) b_n z^(-n).
  $
  On termine en exprimant $a_2$ en fonction des $b_n$. D'une part, on a, au voisinage de $0$,
  $
    g(z) = z^(2) + a_2 z^(4) + o(z^(4)).
  $
  D'autre part, toujours au voisinage de $0$,
  $
    g(z) & = 1 / (1/z + b_0 + b_1 z + o(z))^(2) \
         & = z^(2) / (1 + b_0 z + b_1 z^(2) + o(z^(2)))^(2) \
         & = z^(2) (1 - 2 b_0 z + (b_0^(2) - 2 b_1) z^(2) + o(z^(2))) \
         & = z^(2) - 2 b_0 z^(3) + (b_0^(2) - 2 b_1) z^(4) + o(z^(4)).
  $
  On en déduit que $b_0 = 0$ et $a_2 = 2 b_1$. Or, d'après @eqIneqAiregtilde, on a
  $ abs(b_2)^(2) lt.eq.slant sum_(n = 1)^(infinity) n abs(b_n)^(2) lt.eq.slant 1, $
  donc on obtient comme attendu $abs(a_2) = 2 abs(b_1) lt.eq.slant 2.$
]

=== Théorème du quart et inégalités de distorsion de Koebe
#theorem(title: [Théorème du quart de Koebe])[
  Soit $f in cal(S)(R)$. Alors,
  $
    DD(R slash 4) subset f(DD(R)).
  $
]<thKoebeQuart>

#proof[
  Supposons pour commencer que $R = 1$. Soit $w in CC without f(DD(r))$ ;
  montrons que $abs(w) gt.eq.slant R / 4$.
  Écrivons
  $
    f(z) = sum_(n = 0)^(infinity) a_n z^(n).
  $
  au voisinage de $0$. On considère également
  $
    phi : CC without { w } --> CC, quad z arrow.r.long.bar (w z) / (w - z).
  $
  C'est une homographie, donc une application holomorphe injective. De plus, $phi(0) = 0$
  et $phi prime (0) = 1$. De là, $g := phi compose f : DD --> CC$ est holomorphe, injective,
  $g(0) = 0$ et $g^(prime)(0) = 1$. De plus, on a pour $z$ voisin de $0$,
  $
    g(z) & = (w (z + a_2 z^(2) + o(z^(2)))) / (w - (z + o(z))) \
         & = (z + a_2 z^(2) + o(z^(2))) (1 + z/w + o(z)) \
         & = z + (a_2 + 1/w) z^(2) + o(z^(2)).
  $
  On applique alors le @thmBieberbach à $f$ et à $g$, pour obtenir
  $abs(a_2) lt.eq.slant 2$ et $abs(a_2 + 1/w) lt.eq.slant 2$. Finalement, il vient
  $
    abs(1/w) lt.eq.slant abs(a_2 - a_2 + 1/w) lt.eq.slant abs(a_2) + abs(a_2 + 1/w) lt.eq.slant 4.
  $
  Cela achève la preuve dans le cas $R = 1$. Dans le cas général, on pose
  $
    h : DD --> CC, quad z arrow.r.long.bar f(R z)/R.
  $
  Daprès le premier cas, on a $DD(1 slash 4) subset h(DD) = 1/R f(DD(R))$, ce qui conclut.
]

#theorem(title: [Inégalités de distorsion de Koebe])[
  Soit $f in cal(S)$. Alors les inégalités suivantes sont vérifiées pour tout
  $z in DD$
  #equation(id: "eqDistorsionDerivee")[
    $
      (1 - abs(z)) / (1 + abs(z))^(3) lt.eq.slant abs(f prime (z)) lt.eq.slant (1 + abs(z)) / (1 - abs(z))^(3) ;
    $
  ]
  #equation(id: "eqDistorsionf")[
    $
      abs(z) / (1 + abs(z))^(2) lt.eq.slant abs(f(z)) lt.eq.slant abs(z) / (1 - abs(z))^(2).
    $
  ]
]<thDistorsionKoebe>

#proof[
  Soit $a in DD$. On note $psi$ la fonction holomorphe sur $DD$ définie par
  $
    psi(z) = (z + a) / (1 + overline(a) z).
  $
  On a vu que c'est un biholomorphisme de $DD$ qui vérifie $psi(0) = a$ et $psi^(prime)(0) = 1 - abs(a)^(2)$.
  On considère alors
  $ F : DD --> CC, quad z arrow.r.long.bar (f compose psi(z) - f(a)) / ((1 - abs(a)^(2))f^(prime)(a)), $
  de sorte que $F in cal(S)$. D'après le @thmBieberbach, on a
  $
    abs(F^(prime.double)(0)) = abs((1 - abs(a)^(2))(f^(prime.double)(a))/ (f^(prime)(a)) - 2 overline(a)) lt.eq.slant 4.
  $
  Ceci étant valable pour tous $a, z in DD$, il vient en multipliant par
  $abs(a) / (1 - abs(a)^(2))$, puis en choisissant $a = z$,
  #equation(id: "ineqDeriveeSecAux")[
    $
      abs(z (f^(prime.double)(z)) / (f^(prime)(z)) - (2 abs(z)^(2))/(1 - abs(z)^(2))) lt.eq.slant (4 abs(z)) / (1 - abs(z)^(2)).
    $
  ]
  Comme on l'a déjà vu, la dérivée d'une fonction holomorphe injective ne s'annule pas.
  On peut donc se donner un relèvement holomorphe $ln f^(prime) : DD --> CC$ de
  $f^(prime) : DD --> CC^(*)$ le long de $exp : CC --> CC^(*)$ tel que
  $ln f^(prime)(0) = 0$. Maintenant, remarquons que pour tout $z = r e^(i theta) in DD$,
  $
    r partial_(r) ln abs(f^(prime)(r e^(i theta)))
    & = r Re(partial_(r) ln f^(prime)(r e^(i theta))) \
    & = Re[r e^(i theta) (f^(prime.double)(r e^(i theta))) / (f^(prime)(r e^(i theta)))] \
  $
  L'équation @ineqDeriveeSecAux se réécrit donc
  $
    abs(r partial_(r) ln abs(f^(prime)(r e^(i theta))) - (2 r^(2))/(1 - r^(2)))
    lt.eq.slant (4 r) / (1 - r^(2)),
  $
  et fournit l'encadrement
  $
    (2r - 4) / (1 - r^(2)) lt.eq.slant partial_(r)
    ln abs(f^(prime)(r e^(i theta))) lt.eq.slant (2r + 4) / (1 - r^(2)).
  $
  En intégrant entre $0$ et $rho > 0$, il vient
  $
    ln((1 - rho) / (1 + rho)^(3)) lt.eq.slant
    ln abs(f^(prime)(rho e^(i theta))) lt.eq.slant ln((1 + rho) / (1 - rho)^(3)).
  $
  On passe alors à l'exponentielle et on obtient @eqDistorsionDerivee pour $z = rho e^(i theta)$.
  Montrons maintenant @eqDistorsionf. La majoration de $abs(f(z))$ découle immédiatement
  de @eqDistorsionDerivee par intégration le long du segment $[0, z]$. Montrons la minoration.
  Comme le membre de gauche de @eqDistorsionf est majoré par $1/4$, il suffit de montrer
  l'inégalité pour $z in U := f^(-1)(DD(1 slash 4))$. Or, d'après le @thKoebeQuart, $f$ induit
  un biholomorphisme
  $ f|_(U) : U --> DD(1 slash 4). $
  On définit alors
  $
    gamma : [0, 1] --> U, quad t arrow.r.long.bar f|_(U)^(-1)(t f(z)).
  $
  Le théorème fondamental de l'analyse donne
  $
    abs(f(z)) = abs(integral_(gamma) f^(prime)(w) dif w) = abs(integral_(0)^(1) f^(prime)(gamma(t)) gamma prime (t) dif t).
  $
  Or, par construction, on a pour tout $t in [0, 1]$,
  $
    f^(prime)(gamma(t)) gamma^(prime)(t) = partial_(t) (t f(z)) = f(z).
  $
  On a donc
  $
    abs(f(z)) = integral_(0)^(1) abs(f^(prime)(gamma(t)) gamma prime (t)) dif t.
  $
  En utilisant la minoration de @eqDistorsionDerivee, et le fait que $abs(gamma)$ est
  dérivable sur $]0, 1]$ et vérifie $abs(gamma^(prime)) gt.eq.slant abs(gamma)^(prime)$
  en vertu de l'inégalité triangulaire
  $abs(gamma(t + h) - gamma(t)) gt.eq.slant abs(abs(gamma(t + h)) - abs(gamma(t)))$,
  on trouve
  $
    abs(f(z)) gt.eq.slant integral_(0)^(1) (1 - abs(gamma)(t)) / (1 + abs(gamma)(t))^(3) abs(gamma)^(prime)(t)) dif t
    = integral_(0)^(abs(z)) (1 - r) / (1 + r)^(3) dif r = abs(z) / (1 + abs(z))^(2),
  $
  d'où le résultat.
]

=== Inégalité d'uniformisation d'Erdős
#lemma[
  Soit $f in cal(S)$. Alors $f(DD(1 slash 16)) subset DD(1 slash 4).$
]

#proof[
  Appliquons la majoration de @eqDistorsionf, avec $z in DD(1 slash 16)$. Il vient
  $
    abs(f(z)) lt.eq.slant abs(z) / (1 - abs(z))^(2) lt.eq.slant (1/16) / (1 - 1/16)^(2) = 16/15^(2).
  $
  L'inégalité souhaitée est largement vérifiée.
]

#theorem[
  Soit $f in cal(S)$. Alors, pour tout
  $z in DD(1 slash 16)$,
  $
    abs(f(z) - z) lt.eq.slant 80 abs(z)^(2).
  $
]<thInegaliteErdos>

#proof[
  On pose $R = 1/16$ et $R^(prime) = 1/4$.
  On applique le @corBorneSchwarzPick à la restriction de $f$ à $DD(R)$.
  Il vient, pour tout $z in DD(R)$,
  $
    abs(f(z) - z) lt.eq.slant abs(z)^(2)/R^(2) (R prime^(2) - R^(2)) / (R prime - abs(z))
    lt.eq.slant abs(z)^(2)/R^(2) (R prime^(2) - R^(2)) / (R prime - R)
    = (1/4 + 1/16)/(1/16^(2))abs(z)^(2)
    = (4^(3) + 4^(2)) abs(z)^(2)
    = 16 times 5 abs(z)^(2) = 80 abs(z)^(2),
  $
  d'où le résultat.
]

#corollary[
  Soit $f in cal(S)(R)$. Alors, pour tout
  $z in DD(R slash 16)$,
  $ abs(f(z) - z) lt.eq.slant 80 abs(z)^(2) / R. $
]<corInegaliteErdos>

#proof[
  On applique le @thInegaliteErdos à la fonction
  $
    g : DD --> CC, quad z arrow.r.long.bar f(R z)/R,
  $
  qui est dans $cal(S)$. On obtient, pour tout $z in DD(R slash 16)$,
  $
    abs(f(z) - z) = R abs(g(z / R) - z / R) lt.eq.slant R times 80 abs(z / R)^(2)
    = 80 abs(z)^(2) / R.
  $
]

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

#definition(title: [Collet])[
  Soit $M$ une variété topologique à bord. Un _collet_ de $M$ est un
  voisinage $V$ de $partial M$ muni d'un homéomorphisme
  $
    phi : V --> partial M times [0, 1[
  $
  dont la restriction à $partial M$ est l'application canonique
  $partial M --> partial M times { 0 }.$
]

Si $M$ est lisse et $partial M$ est compact, on voit en intégrant un champ
de vecteurs transversal au bord et pointant vers l'intérieur de $M$ que celle-ci
admet un collet lisse.

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
  Soit $omega$ une $1$-forme différentielle fermée sur $P without { a }$. Alors, pour tout
  lacet $gamma$ dans $P without { a }$, il existe un entier $d in ZZ$ tel que
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
  est également un générateur par la discussion précédente. Ainsi, pour tout lacet
  $gamma$ dans $P without { a }$, il existe un entier $d in ZZ$ tel que $[gamma] = d iota_(*)[delta]$.
  On en déduit que $gamma - d delta$ est le bord d'une $2$-chaîne singulière $sigma$ dans
  $P without { a }$. Par la formule de Stokes, on a donc
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
  Soient $y in Y$ et $y_1, y_2 in tilde(Y)|_(y)$. Soit $gamma : [0, 1] --> tilde(Y)$ un
  chemin de $a$ à $b$. On a
  $
    F(y_2) - F(y_1) = integral_(gamma) dif F = integral_(gamma) p^(*) omega = integral_(p compose gamma) omega.
  $
  Or, $p compose gamma$ est un lacet en $y$ dans $Y$. D'après le @lemIntegraleFormeFermee, il existe un entier $d in ZZ$
  tel que
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
  introduit à la @secSchwarzPick. Alors $phi_a$ est bien définie sur $D$
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

#pagebreak()
#bibliography("bib/biblio.bib")
