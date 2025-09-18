#import "@preview/touying:0.6.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/lovelace:0.3.0": *
#import "@preview/algo:0.3.6": *

#import themes.metropolis: *

#let diagram = touying-reducer.with(
  reduce: fletcher.diagram, cover: fletcher.hide)

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  footer: self => [],
  config-colors(
    primary: rgb("#eb811b"),
    primary-light: rgb("#d6c6b7"),
    secondary: rgb("#23373b"),
    neutral-lightest: rgb("#fafafa"),
    neutral-dark: rgb("#23373b"),
    neutral-darkest: rgb("#23373b"),
  ),
  config-info(
    title: [Iterative Monomorphisation],
    subtitle: [ARPE internship],
    author: [Jasmin Blanchette and Tanguy Bozec],
    institution: [LMU, München, Germany and ENS Paris-Saclay, Gif-sur-Yvette, France],
  ),
  config-common(new-section-slide-fn: none),
)

#show strong: alert

#set text(size: 24pt, font: "Fira Sans", fallback: false)

#let primary = rgb("#eb811b")

#let alert(body) = {text(fill: primary, weight: "semibold")[#body]}

#let good_col = green.lighten(20%)
#let bad_col = red.lighten(40%)

#let ty(body) = {
  set text(
    font: "Fira Mono",
    size: 20pt
  )
  body
}

#let mathCol(x, color) = text(fill: color)[$#x$]

#let hl(body, colour: yellow) = {box(fill: colour.lighten(20%),stroke: none, outset: 0.1em, body)}

#let altHighlight(self, body, visible: "2-", colour: yellow) = {
  if utils.check-visible(self.subslide, visible) {hl(body, colour: colour)}
  else {body}
}

#let hide(self, body, invisible: "1") = {
  if utils.check-visible(self.subslide, invisible) {}
  else {body}
}

// TODO this is a temporary fix, the correct thing to do
// would be to pass the previous character as an argument,
// measure the height of both and align accordingly
#let cross = text(font: "Noto Color Emoji", top-edge: "ascender")[#box[#move(dy: -2.5pt, emoji.crossmark)]]

#title-slide()

= Introduction

== Motivation
#slide(repeat: 7, self => {
   let (uncover, only, alternatives) = utils.methods(self)

  [

    #align(center)[
    #set text(font: "Fira Sans")
    #diagram(
     //debug: 3,
     spacing: (2.5em, 1em),
     node((0, 1.5), altHighlight(self, [Isabelle/HOL], visible: "2, 3-7")),

     node(name: <sl>, (0.88, 1.5), [Sledgehammer], defocus: 0.7),

     //node(name: <ghost-zip>,  (2, 0), [a]),
     //node(name: <ghost-vamp>, (2, 1), [a]),
     //node(name: <ghost-e>,    (2, 2), [a]),

     let hl_poly(body) = {altHighlight(self, body, visible: "3-7")},
     let hl_mono(body) = {altHighlight(self, body, colour: green, visible: "4-7")},

     node(name: <zip>,  (2,0), width: 7em, height: 2em, align(left)[#hl_poly[Zipperposition]]),
     node(name: <vamp>, (2,1), width: 7em, height: 2em, align(left)[#hl_poly[Vampire]]       ),
     node(name: <e>,    (2,2), width: 7em, height: 2em, align(left)[#hl_mono[E] #uncover("7")[#cross]]),
     node(name: <leo>,  (2,3), width: 7em, height: 2em, align(left)[#hl_poly[Leo-III]]       ),

     //node(name: <zip>,  <ghost-zip.west>,  [Zipperposition]),
     //node(name: <vamp>, <ghost-vamp.west>, [Vampire]),
     //node(name: <e>,    <ghost-e.west>,    [E]),

     edge((0,1.5),(1,1.5), "->"),

     edge((0.87, 1.5), <zip.west> , "->", layer: -1),
     edge((0.87, 1.5), <vamp.west>, "->", layer: -1),
     edge((0.87, 1.5), <e.west>   , "->", layer: -1),
     edge((0.87, 1.5), <leo.west> , "->", layer: -1),


     pause,
     /*only("1-6")*/[#node((0, 0), [#hl[Polymorphic]\ with type variables])],
     pause,
     pause,
     /*only("1-6")*/[#node((0.88, 0), [#hl(colour: green)[Monomorphic]\ no type variables])],

     pause,
     let hl_e_call(body) = {altHighlight(self, body, colour: green, visible: "6-7")},
     [#node((2.9,0), [#hl_e_call[E] #uncover("7")[#cross]])],
     //[#node((2.9,3), [#hl_e_call[E] #uncover("7")[#cross]])],

     [#edge(<zip.east>,   (2.9, 0), "->")],
     //[#edge(<leo.center>, (2.9, 3), "->")],
    )
    ]
    // TODO instead of Provers have multiple provers
    // show that some of these provers cannot be called because of the polymorphism mismatch
    // show that some provers cannot call their backends for the same reason
]})

== Solution
#slide[
  #align(center)[
    Polymorphic problem $arrow.double.long$ Monomorphic problem
  ]

  #pause \
  Two possibilities:
    + #alert[Encode] type variables in a monomorphic logic
    + #alert[Instantiate] type variables
]

== Rank-1 Polymorphism
#slide[

  $forall x: ty("list_int"),    f angle.l ty("list_int")    angle.r(x)$\
  #pause
  $forall x: ty("list_nat"),    f angle.l ty("list_nat")    angle.r(x)$\
  $forall x: ty("list_bool"),   f angle.l ty("list_bool")   angle.r(x)$\
  $forall x: ty("list_string"), f angle.l ty("list_string") angle.r(x)$\

  #pause

  $forall mathCol(alpha, #red), forall x: ty("list")\(mathCol(alpha, #red)), f angle.l ty("list")\(mathCol(alpha, #red)) angle.r\(x)$

  #pause

  Type variables are quantified #alert[universally] at the #alert[top level] of a formula.
]

= Iterative monomorphisation
//#slide(title: "Iterative monomorphisation algorithm")[
//  $forall alpha, forall x: ty("list")\(alpha), f angle.l ty("list")(alpha) angle.r(x)$
//  #pause
//
//  $forall x: ty("list")(ty("int")),    f angle.l ty("list")(ty("int"))    angle.r(x)$\
//  $forall x: ty("list")(ty("nat")),    f angle.l ty("list")(ty("nat"))    angle.r(x)$\
//  $forall x: ty("list")(ty("bool")),   f angle.l ty("list")(ty("bool"))   angle.r(x)$\
//  $forall x: ty("list")(ty("string")), f angle.l ty("list")(ty("string")) angle.r(x)$\
//
//
//]

//#slide(title: "Iterative monomorphisation algorithm")[
//  Match non-monomorphic type arguments against monomorphic type arguments to generate substitutions that we can use to instantiate type variables.
//]

== Algorithm

#let st(body) = text(weight: "semibold")[#body]

#let it_mon_algo = pseudocode-list(line-numbering: none)[
  + $P$ is the set of input formulae
  + #st[while] new formulae are added to $P$ #st[do]
    + #st[for all] occurrences $f angle.l tau angle.r (dots)$ and $f angle.l pi angle.r (dots)$ in $P$ #st[do]
      + #st[if] $pi$ is monomorphic #st[and] $tau$ matches against $pi$ #st[then]
        + add $sigma$, the unifier of $pi$ and $tau$ to $S$
    + #st[for all] $phi in P, sigma in S$ #st[do]
      + add $phi sigma$ to $P$
  + $R = {phi in P | phi #text(font: "Fira Sans")[is monomorphic]}$
  + #st[return] $R$
  ]

#slide[
  #it_mon_algo
]

#slide[

  #alert[Soundness]: instantiation of universally quantified type variables.

  #pause
  #alert[Completeness]: this algorithm is incomplete.

    #pause
    - Finding a #alert[finite equisatisfiable] set of monomorphic instances of a first-order polymorphic formula is #alert[undecidable]

    #pause
    - #alert[Bounds] limit the instantiations we perform
]

== Example

#slide(self => [
  #let (uncover, only, alternatives) = utils.methods(self)

  Initial problem:
  + $forall x: ty("int"), #altHighlight(self, $f angle.l ty("int") angle.r$, visible: "2-4")\(x) $
  + $forall x: alpha, y: ty("list")(alpha), #altHighlight(self, colour: good_col, $f angle.l alpha angle.r$, visible: "2,3,4")\(x) and #altHighlight(self, colour: bad_col, $f angle.l ty("list")(alpha) angle.r$, visible: "3")\(y)$

  #pause
  Successful match of $hl(colour: #good_col, alpha)$ against $hl(ty("int"))$.

  #pause
  #alternatives[
    Failure to match $hl(colour: #bad_col, ty("list")(alpha))$ against $hl(ty("int"))$.][
    Failure to match $hl(colour: #bad_col, ty("list")(alpha))$ against $hl(ty("int"))$.][
    Failure to match $hl(colour: #bad_col, ty("list")(alpha))$ against $hl(ty("int"))$.][
    We apply the substitution $hl(colour: #good_col, alpha) mapsto hl(ty("int"))$ to clause 2.]

  //#only("1-3")[Failure to match $hl(colour: #bad_col, ty("list")(alpha))$ against $hl(ty("int"))$]

  #pause

  #set enum(start: 3)
  + $forall x: ty("int"), y: ty("list")(ty("int")), f angle.l ty("int") angle.r(x) and #altHighlight(self, colour: good_col, $f angle.l ty("list")(ty("int")) angle.r$, visible: "6")\(y)$

  //#pause

  //#pause
  //Successful match of $alpha$ against $ty("list")(ty("int"))$:

  //#set enum(start: 4)
  //+ $forall x: ty("list")(ty("int")), y: ty("list")(ty("list")(ty("int"))), \ f angle.l ty("list")(ty("int")) angle.r(x) and f angle.l ty("list")(ty("list")(ty("int"))) angle.r(y)$

])

#slide(self => [
  + $forall x: ty("int"), f angle.l ty("int") angle.r (x) $
  + $forall x: alpha, y: ty("list")(alpha), #altHighlight(self, $f angle.l alpha angle.r$, colour: good_col, visible: "2-")\(x) and f angle.l ty("list")(alpha) angle.r (y)$
  + $forall x: ty("int"), y: ty("list")(ty("int")), f angle.l ty("int") angle.r (x) and #altHighlight(self, $f angle.l ty("list")(ty("int")) angle.r$, visible: "2-")\(y)$

  #pause
  Successful match of $hl(colour: #good_col, alpha)$ against $hl(hl("list")(ty("int")))$.

  #pause
  We apply the substitution $hl(colour: #good_col, alpha) mapsto hl(hl("list")(ty("int")))$ to clause 2.

  #set enum(start: 4)
  + $forall x: ty("list")(ty("int")), y: ty("list")(ty("list")(ty("int"))),\ f angle.l ty("list")(ty("int")) angle.r (x) and f angle.l ty("list")(ty("list")(ty("int"))) angle.r (y)$

  #pause
  This can generate an #alert[infinite] number of new formulae.
])

//#slide(title: "An easy(-ish) example", repeat: 5, self => [
//  We add another formula to our problem:
//#set enum(start: 5)
//  + $forall x: alpha, y: beta, z: ty("pair")(alpha, beta), #altHighlight(self, $f angle.l alpha angle.r$, visible: "3")\(x) and #altHighlight(self, $f angle.l beta angle.r$, visible: "4", colour: orange)\(y) and #altHighlight(self, $f angle.l ty("pair")(alpha,beta) angle.r$, visible: "5", colour: green)\(z)$
//  #pause
//#table(
//  stroke: none,
//  columns: (1fr, 1fr),
//  rows: 1.5em,
//  align: (x, _) => if x==0 {center} else {center},
//  table.header(
//    [Monomorphic],
//    [Non-monomorphic],
//  ),
//  [],[],
//  [$ty("int"), ty("list")(ty("int")), ty("list")(ty("list")(ty("int")))$],[$alpha, beta, ty("pair")(alpha, beta)$],
//  [], [#hide(self, altHighlight(self, $ty("pair")(ty("int"), beta), ty("pair")(ty("list")(ty("int")), beta)$, visible: "3"), invisible: "1-2")],
//  [], [#hide(self, altHighlight(self, $ty("pair")(ty("list")(ty("list")(ty("int"))), beta)$, visible: "3"), invisible: "1-2")],
//  [], [#hide(self, altHighlight(self, $ty("pair")(alpha, ty("int")), ty("pair")(alpha, ty("list")(ty("int")))$, visible: "4", colour: orange), invisible: "1-3")],
//  [], [#hide(self, altHighlight(self, $ty("pair")(alpha, ty("list")(ty("list")(ty("int"))))$, visible: "4", colour: orange), invisible: "1-3")],
//)
//])

//#slide(title: [An #strike(stroke: 3pt)[easy] explosive example])[
//
//$ty("pair")(ty("int"), ty("int"))$\
//$ty("pair")(ty("int"), ty("list")(ty("int")))$\
//$ty("pair")(ty("int"), ty("list")(ty("list")(ty("int"))))$\
//
//$ty("pair")(ty("list")(ty("int")), ty("int"))$\
//$ty("pair")(ty("list")(ty("int")), ty("list")(ty("int")))$\
//$ty("pair")(ty("list")(ty("int")), ty("list")(ty("list")(ty("int"))))$\
//
//$ty("pair")(ty("list")(ty("list")(ty("int"))), ty("int"))$\
//$ty("pair")(ty("list")(ty("list")(ty("int"))), ty("list")(ty("int")))$\
//$ty("pair")(ty("list")(ty("list")(ty("int"))), ty("list")(ty("list")(ty("int"))))$\
//]

#slide(title: "Bounds")[
  We cannot #alert[exhaustively enumerate] all type variables instantiations.

  We use #alert[heuristics] to determine which instantiations we perform:

  #pause
  - The number of #alert[iterations] of the algorithm is limited.

  #pause
  - We filter type arguments by #alert[function symbol].

  #pause
  - We limit the number of #alert[substitutions] we generate.

  #pause
  - We limit the number of #alert[applications] of the substitutions.

]

#slide(title: "Zipperposition and E")[
  #figure(
  image("architecture.svg", width: 95%),
)

]
= Evaluation
//#slide(title: "Parameter optimisation")[
//  Between newly introduced bounds and options related to E, 14 different parameters must be adjusted.
//  #pause
//  
//  The many options of the base version of Zipperposition also have to be set.
//]

== Benchmarks
#slide[

  We wanted to test the #alert[usefulness] of our implementation of iterative monomorphisation.

  We had two questions:

  #pause
  + Does Zipperposition benefit from the ability to call E on monomorphised problems?

  + Does E perform well on monomorphised problems?

]

== Methodology
#slide[
  We used the #alert[TPTP] (Thousand Problems for Theorem Provers) problem set for our evaluations.

  #pause
  We split the problem set into two:
    - 500 problems for adjusting bounds and parameters
    - 1034 problems for the benchmarks
]

== Zipperposition benefits from monomorphisation

#slide[
  #table(
    stroke: none,
    columns: (1fr, 1fr, 1fr, 1fr),
    rows: 1.5em,
    align: (x, _) => if x==0 {left} else {center},
    table.header(
      [],
      [Zipperposition without E],
      [Zipperposition with E],
      [Union],
    ),
    [],[],[],[],
    [500 problems] ,[168],[198],[207],
    [1034 problems],[337],[410],[434],
  )

  #pause \
  This is #alert[expected] Zipperposition benefits greatly from E in a monomorphic setting.
]

== E performs well on monomorphised problems
#slide(repeat: 4, self => [
  #let hide_leo(body) = hide(self, body, invisible: "1-2")
  #let hide_zip(body) = hide(self, body, invisible: "1")
  #let hide_u(body) = hide(self, body, invisible: "1-3")

#table(
  stroke: none,
  columns: (6em, 1fr, 1fr, 1fr),
  rows: 1.5em,
  align: (x, _) => if x==0 {left} else {center},
  table.header(
    [],
    [Native polymorphism],
    [Monomorphisation],
    [#hide_u([Union])],
  ),
  [],[],[],[],
  [E]                   ,[\- ]             ,[340]             ,[#hide_u([340])],
  [Zipperposition]      ,[339]             ,[#hide_zip([351])],[#hide_u([404])],
  [#hide_leo([Leo-III])],[#hide_leo([157])],[#hide_leo([231])],[#hide_u([274])],
)

  Calling E on monomorphised problems is a #alert[viable] option.

  #uncover("3-")[Polymorphic provers perform #alert[better] on monomorphised problems.]

])

= Conclusion
#slide(title: "Conclusion")[
  
  - Goal: Polymorphic problem $arrow.double.long$ Monomorphic problem.

  #pause
  - Algorithm works by #alert[instantiating] type variables with ground types.

  #pause
  - #alert[Bounds] are necessary in practice.

  #pause
  - It is a #alert[viable] means for extending monomorphic provers.

  #pause
  - Iterative monomorphisation can #alert[outperform] native implementations of polymorphism
]

#title-slide()
