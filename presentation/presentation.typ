#import "@preview/touying:0.6.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

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


#let ty(body) = {
  set text(
    font: "Fira Mono",
    size: 20pt
  )
  body
}

#let mathCol(x, color) = text(fill: color)[$#x$]

#let altHighlight(self, body, visible: "2-", colour: yellow) = {
  if utils.check-visible(self.subslide, visible) {box(fill: colour.lighten(20%),stroke: none, outset: 0.1em, body)}
  else {body}
}

#let hide(self, body, invisible: "1") = {
  if utils.check-visible(self.subslide, invisible) {}
  else {body}
}

//#show: slides

#title-slide()

= Introduction
#slide(title: "Context")[

  #align(center)[
  #set text(font: "Fira Sans")
  #diagram(
   //debug: 3,
   spacing: (3.5em, 1em),
   node((0, 1.5), [Isabelle/HOL]),

   node(name: <sl>, (0.88, 1.5), [Sledgehammer], defocus: 0.7, fill: white),

   //node(name: <ghost-zip>,  (2, 0), [a]),
   //node(name: <ghost-vamp>, (2, 1), [a]),
   //node(name: <ghost-e>,    (2, 2), [a]),

   node(name: <zip>,  (2,0), align(left)[Zipperposition], width: 7em, height: 2em),
   node(name: <vamp>, (2,1), align(left)[Vampire]       , width: 7em, height: 2em),
   node(name: <e>,    (2,2), align(left)[E]             , width: 7em, height: 2em),
   node(name: <leo>,  (2,3), align(left)[Leo-III]       , width: 7em, height: 2em),

   //node(name: <zip>,  <ghost-zip.west>,  [Zipperposition]),
   //node(name: <vamp>, <ghost-vamp.west>, [Vampire]),
   //node(name: <e>,    <ghost-e.west>,    [E]),

   edge((0,1.5),(1,1.5), "->"),

   edge((0.87, 1.5), <zip.west> , "->", layer: -1, shift: (-0pt ,0pt)),
   edge((0.87, 1.5), <vamp.west>, "->", layer: -1, shift: (-0pt ,0pt)),
   edge((0.87, 1.5), <e.west>   , "->", layer: -1, shift: (-0pt ,0pt)),
   edge((0.87, 1.5), <leo.west> , "->", layer: -1, shift: (-0pt ,0pt)),

   node((3,0), [E]),
   node((3,3), [E]),

   edge(<zip.east>, (3, 0), "->"),
   edge(<leo.center>, (3, 3), "->"),
  )
  ]
  // TODO instead of Provers have multiple provers
  // show that some of these provers cannot be called because of the polymorphism mismatch
  // show that some provers cannot call their backends for the same reason
]


#slide(title: "Rank-1 polymorphism")[

  $forall x: ty("list_int"),    f angle.l ty("list_int")    angle.r(x)$\
  #pause
  $forall x: ty("list_nat"),    f angle.l ty("list_nat")    angle.r(x)$\
  $forall x: ty("list_bool"),   f angle.l ty("list_bool")   angle.r(x)$\
  $forall x: ty("list_string"), f angle.l ty("list_string") angle.r(x)$\

  #pause

  $forall mathCol(alpha, #red), forall x: ty("list")\(mathCol(alpha, #red)), f angle.l ty("list")\(mathCol(alpha, #red)) angle.r\(x)$

  #pause

  Type variables are always quantified #emph[universally] at the #emph[top level] of a forumla.
]
#let approach(nb) = {"approach " + str(nb) + ": "}
#slide(title: "Monomorphisation")[
Not all automatic theorem provers support polymorphism.
#set enum(numbering: approach)
  + #pause Extend monomorphic provers to support polymorphism
  + #pause Monomorphise problems
]
//#slide(title: "Encoding approach")[
//  Adds side conditions and annotations to the problem's formulae.
//
//  #pause
//  $forall x: ty("int"), P(x)$ 
//
//  #pause
//  $forall x, g_("int")(x) arrow.r.double P(x)$
//
//]
= Iterative monomorphisation
#slide(title: "Iterative monomorphisation algorithm")[
  $forall alpha, forall x: ty("list")\(alpha), f angle.l ty("list")(alpha) angle.r(x)$
  #pause

  $forall x: ty("list")(ty("int")),    f angle.l ty("list")(ty("int"))    angle.r(x)$\
  $forall x: ty("list")(ty("nat")),    f angle.l ty("list")(ty("nat"))    angle.r(x)$\
  $forall x: ty("list")(ty("bool")),   f angle.l ty("list")(ty("bool"))   angle.r(x)$\
  $forall x: ty("list")(ty("string")), f angle.l ty("list")(ty("string")) angle.r(x)$\


]

//#slide(title: "Iterative monomorphisation algorithm")[
//  Match non-monomorphic type arguments against monomorphic type arguments to generate substitutions that we can use to instantiate type variables.
//]


#slide(title: "An easy example", self => [
  #let (uncover, only, alternatives) = utils.methods(self)

  Initial problem:
  + $forall x: ty("int"), #altHighlight(self, $f angle.l ty("int") angle.r$, visible: "2-4")\(x) $
  + $forall x: alpha, y: ty("list")(alpha), #altHighlight(self, $f angle.l alpha angle.r$, visible: "2,3,5")\(x) and #altHighlight(self, $f angle.l ty("list")(alpha) angle.r$, visible: "2,4")\(y)$

  #pause
  #pause
  Successful match of $alpha$ against $ty("int")$:

#set enum(start: 3)
  + $forall x: ty("int"), y: ty("list")(ty("int")), f angle.l ty("int") angle.r(x) and #altHighlight(self, $f angle.l ty("list")(ty("int")) angle.r$, visible: "5")\(y)$

  #pause
  Failure to match $ty("list")(ty("int"))$ against $ty("int")$

  #pause
  Successful match of $alpha$ against $ty("list")(ty("int"))$:

#set enum(start: 4)
  + $forall x: ty("list")(ty("int")), y: ty("list")(ty("list")(ty("int"))), \ f angle.l ty("list")(ty("int")) angle.r(x) and f angle.l ty("list")(ty("list")(ty("int"))) angle.r(y)$

])

#slide(title: "An easy(-ish) example", repeat: 5, self => [
  We add another formula to our problem:
#set enum(start: 5)
  + $forall x: alpha, y: beta, z: ty("pair")(alpha, beta), #altHighlight(self, $f angle.l alpha angle.r$, visible: "3")\(x) and #altHighlight(self, $f angle.l beta angle.r$, visible: "4", colour: orange)\(y) and #altHighlight(self, $f angle.l ty("pair")(alpha,beta) angle.r$, visible: "5", colour: green)\(z)$
  #pause
#table(
  stroke: none,
  columns: (1fr, 1fr),
  rows: 1.5em,
  align: (x, _) => if x==0 {center} else {center},
  table.header(
    [Monomorphic],
    [Non-monomorphic],
  ),
  [],[],
  [$ty("int"), ty("list")(ty("int")), ty("list")(ty("list")(ty("int")))$],[$alpha, beta, ty("pair")(alpha, beta)$],
  [], [#hide(self, altHighlight(self, $ty("pair")(ty("int"), beta), ty("pair")(ty("list")(ty("int")), beta)$, visible: "3"), invisible: "1-2")],
  [], [#hide(self, altHighlight(self, $ty("pair")(ty("list")(ty("list")(ty("int"))), beta)$, visible: "3"), invisible: "1-2")],
  [], [#hide(self, altHighlight(self, $ty("pair")(alpha, ty("int")), ty("pair")(alpha, ty("list")(ty("int")))$, visible: "4", colour: orange), invisible: "1-3")],
  [], [#hide(self, altHighlight(self, $ty("pair")(alpha, ty("list")(ty("list")(ty("int"))))$, visible: "4", colour: orange), invisible: "1-3")],
)
])

#slide(title: [An #strike(stroke: 3pt)[easy] explosive example])[

$ty("pair")(ty("int"), ty("int"))$\
$ty("pair")(ty("int"), ty("list")(ty("int")))$\
$ty("pair")(ty("int"), ty("list")(ty("list")(ty("int"))))$\

$ty("pair")(ty("list")(ty("int")), ty("int"))$\
$ty("pair")(ty("list")(ty("int")), ty("list")(ty("int")))$\
$ty("pair")(ty("list")(ty("int")), ty("list")(ty("list")(ty("int"))))$\

$ty("pair")(ty("list")(ty("list")(ty("int"))), ty("int"))$\
$ty("pair")(ty("list")(ty("list")(ty("int"))), ty("list")(ty("int")))$\
$ty("pair")(ty("list")(ty("list")(ty("int"))), ty("list")(ty("list")(ty("int"))))$\
]
#slide(title: "Bounds")[
  To curb explosive enumerations bounds are necessary, they limit the number of new:
  #pause
    - monomorphic type arguments (each iteration)
    #pause
    - non-monomorphic type arguments (each iteration)
    #pause
    - monomorphised formulae
]

= Implementation
#slide(title: "Improvements")[
  Key ideas:
  - Separating type arguments into "old" and "new" sets
  - Only applying substitutions to type argument
  - Generating the monomorphised formulae in a seperate phase
]

#slide(title: "Zipperposition and E")[
  #figure(
  image("architecture.svg", width: 80%),
)

]
= Evaluation
//#slide(title: "Parameter optimisation")[
//  Between newly introduced bounds and options related to E, 14 different parameters must be adjusted.
//  #pause
//  
//  The many options of the base version of Zipperposition also have to be set.
//]
#slide(title: "Methodology")[
  Two sets of TPTP (Thousands of Problems for Theorem Provers) problems:
    - 500 problems for testing and adjusting bounds
    - 1034 problems for the evaluations
]
#slide(title: "Zipperposition with E")[
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
//  Significant improvement:
//    - 160 problems solved without E vs 198 with E
//    - 337 problems solved without E vs 410 with E
]
//#slide(title: "Extending monomorphic provers")[
//  The iterative monomorphisation to monomorphic prover pipeline is viable.
//
//  #pause
//
//  E with monomorphisation solves 340 problems, as many as the base version of Zipperposition 
//]
#slide(title: "Extending a monomorphic prover", repeat: 4, self => [
#table(
  stroke: none,
  columns: (6em, 1fr, 1fr, 1fr),
  rows: 1.5em,
  align: (x, _) => if x==0 {left} else {center},
  table.header(
    [],
    [#hide(self, [Native polymorphism], invisible: "1-2")],
    [Monomorphisation],
    [#hide(self, [Union], invisible: "1-3")],
  ),
  [],[],[],[],
  [E]                            ,[#hide(self, [-]  , invisible: "1-2")],  [340]             ,[#hide(self, [340], invisible: "1-3")],
  [#hide(self, [Leo-III])]       ,[#hide(self, [157], invisible: "1-2")],[#hide(self, [231])],[#hide(self, [274], invisible: "1-3")],
  [#hide(self, [Zipperposition])],[#hide(self, [339], invisible: "1-2")],[#hide(self, [351])],[#hide(self, [404], invisible: "1-3")],
)
//  Significant improvement:
//    - 157 problems solved by Leo-III vs 231 by Leo-III with monomorphisation
//    - 339 problems solved by Zipperposition vs 351 by Zipperposition with monomorphisation
])

= Conclusion
#slide(title: "Conclusion")[
  
  - Iterative monomorphisation heuristically instantiates type variables of polymorphic formulae

  #pause
  - This approach needs bounds and limits to be viable

  #pause
  - Iterative monomorphisation can outperform native implementations of polymorphism

  #pause
  - It is a viable method for extending monomorphic provers
]

#title-slide()
