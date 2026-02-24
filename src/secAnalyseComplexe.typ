#import "../lib/lib.typ": *

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

=== Une famille d'automorphismes du disque <secAutomorphismesDisque>
Dans toute la suite, on notera $DD(z, r) := {w in CC | abs(w - z) lt r}$ 
le disque ouvert de centre $z$ et de rayon $r$, et $overline(DD)(z, r)$ son
adhérence dans $CC$. Si $z = 0$, on se contentera d'écrire $DD(r) := DD(0, r)$,
et on désigne également par $DD$ le disque unité ouvert.

Dans ce paragraphe, on introduit et on étudie brièvement des automorphismes du disque qui envoient
$0$ sur un point choisi arbitrairement. Nous les utiliserons à plusieurs
reprises dans la suite comme reparamétrisation du disque.

Considérons, $w in DD$ étant donné, l'application méromorphe
$
  phi_(w) : CC --> CC, quad z arrow.r.long.bar (z - w) / (1 - overline(w) z).
$
Si $w = 0$, ce n'est autre que l'identité. Sinon, elle induit un
biholomorphisme de $CC without { overline(w)^(-1) }$ sur $CC without { - overline(w)^(-1) }$,
d'inverse
$
  phi_(w)^(-1) = phi_(-w) : CC without { - overline(w)^(-1) } --> CC without { overline(w)^(-1) }, quad z arrow.r.long.bar (z + w) / (1 + overline(w) z).
$
L'application $phi_w$ est holomorphe au voisinage de $overline(DD)$ et pour tout $z in partial DD$,
$ abs(phi_(w)(z)) = abs(z - w) / abs(1 - overline(w)z) = abs(z - w) / abs(overline(z - w)) = 1. $
Par le principe du maximum, $psi_(w) := phi_(w)|_(DD)$ étant non constante, elle est à valeurs dans $DD$, et
est donc un automorphisme de $DD$, qui vérifie
$
  psi_w (0) = w, quad psi_w (-w) = 0, quad (psi_w)'(0) = 1 - abs(w)^(2).
$

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
    psi : DD(R) arrowTildeLong DD(R), quad z arrow.r.long.bar (R^(2)(z + a))/(R^(2) + overline(a)z) = R psi_(-a slash R)(z / R).
  $
  La fonction $psi_(-a slash R)$ est définie à la @secAutomorphismesDisque, et on y montre que c'est un automorphisme de $DD$ qui 
  envoie $0$ sur $a slash R$. Cela conclut la preuve.
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
  On a vu à la @secAutomorphismesDisque que c'est un biholomorphisme de $DD$ qui vérifie $psi(0) = a$ et $psi^(prime)(0) = 1 - abs(a)^(2)$.
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

