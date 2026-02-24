#import "../lib/lib.typ": *

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
/ Topologie Algébrique.: Homologie singulière, Excision, suites exactes de paires, 
  orientation. Le livre @bredon_topology_1993 est une excellente référence.
/ Calcul différentiel et Géométrie différentielle.:
  Théorème de Sard, variétés topologiques et différentielles,
  variétés à bord, champs de vecteurs, flots, intégration des
  formes différentielles, théorème de Stokes, lissage des chemins, 
  isomorphisme entre l'homologie singulière continue et lisse 
  pour les variétés. On renvoie pour cela
  à @lee_introduction_2013, très détaillé.

Ces prérequis étant satisfaits, le texte qui suit est entièrement autonome.
Chaque démonstration est détaillée.
