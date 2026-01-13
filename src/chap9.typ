#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/fletcher:0.5.8" as fl: *;
#import "@preview/tdtr:0.4.3": *;

#let accent = rgb(50, 150, 150)
#show ref: it => {
    if query(it.target) == ([#str(it.target)],) {
        emph(link(it.target, str(it.target)))
    } else {
        it
    }
}


#show: cyan-report.with(
    title: "Exercises",
    subtitle: "Chapter 9",
    authors: (
        (name: "Sean Li", affiliation: "Redacted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)
#let nat = $mono("nat")$
#let mark(content) = text(content, fill: accent)

// Scripts for correctly spacing juxtaposed applications
#let operators = ($exists$.body, $lambda$.body, $forall$.body, $Pi$.body)
#let isalpha(x) = x.match(regex("[A-Za-z]+")) != none
#let set-symbol(x) = {
    if isalpha(x.text) {
        math.class("binary", x)
    } else if x in operators {
        x + h(0em)
    } else {
        x
    }
};
#let symbol = $x$.body.func()
#show math.equation: it => {
    show symbol: set-symbol
    it
}
#let sort = $square$
#let defs = $gt.tri$
#let sorry = `sorry`

#definition[
    Extended Rules for $lambda D_0$
    #align(center, rule-set(
        prooftree(rule(
            name: "def",
            $Delta; Gamma tack K : L$,
            $Delta; overline(a) : overline(M) tack M : N$,
            $Delta, (overline(x) : overline(A) defs a(overline(x)) := M : N); Gamma tack K : L$,
        )),
        prooftree(rule(
            name: "inst",
            $Delta, cal(D); Gamma tack * : sort$,
            $Delta, cal(D); Gamma tack overline(U) : overline(A[overline(x) := overline(U)])$,
            $cal(D) equiv overline(x) : overline(A) defs a(overline(x)) := M : N$,
            $Delta, cal(D) ; Gamma tack a(overline(U)) : N[overline(x) := overline(U)]$,
        )),
        prooftree(rule(
            name: "conv",
            $Delta; Gamma tack x : A$,
            $Delta; Gamma tack A : s$,
            $A =^(Delta, beta) B$,
            $Delta; Gamma tack x : B$,
        )),
    ))
    #lemma[
        Given $cal(D) equiv overline(x) : overline(A) defs a(overline(x)) := M : N$ and $a in.not Delta$
        #align(center, prooftree(rule(
            name: "par",
            $Delta; overline(x) : overline(A) tack M : N$,
            $Delta, cal(D); overline(x) : overline(A) tack a(overline(x)) : N$,
        )))
    ]
]

// MARK: Q. 9.1
#problem(source: "9.1")[
    Given
    $
        (cal(D)_1) quad x : ZZ, y : ZZ quad defs & quad a(x, y) quad       && := x^2 + y^2           &&&  : ZZ \
        (cal(D)_2) quad x : ZZ, y : ZZ quad defs & quad b(x, y) quad       && := 2 dot (x dot y)     &&&  : ZZ \
        (cal(D)_3) quad x : ZZ, y : ZZ quad defs & quad c(x, y) quad       && := a(x, y) + b(x, y)   &&&  : ZZ \
        (cal(D)_4) quad x : ZZ, y : ZZ quad defs & quad "lemma"(x, y) quad && := c(x, y) = (x + y)^2 &&& : *_p \
    $
    Consider $Delta equiv cal(D)_1, cal(D)_2, cal(D)_3, cal(D)_4$. Describe the dependencies between the four definitions and give all possible linearizations of the corresponding partial order.
]
#solution[
    Hasse diagram given below

    #align(center, fl.diagram(
        node-stroke: 1pt,
        node((0, 0), [
            *$cal(D)_1$*
            $ a := x^2 + y^2 : ZZ $
        ]),
        node((2, 0), [
            *$cal(D)_2$*
            $ b := 2 dot (x dot y) : ZZ $
        ]),
        node((1, 0), [
            *$cal(D)_3$*
            $ c := a(x, y) + b(x, y) : ZZ $
        ]),
        node((1, 1), [
            *$cal(D)_4$*
            $ "lemma" := c(x, y) = (x + y)^2: *_p $
        ]),
        edge((2, 0), (1, 0), "->"),
        edge((0, 0), (1, 0), "->"),
        edge((1, 0), (1, 1), "->"),
    ))
    The only unordered pair is $(cal(D)_1, cal(D_2))$. Therefore there are two possible linearizations:
    $
        (1) quad & cal(D)_1 <= cal(D)_2 <= cal(D)_3 <= cal(D)_4 \
        (2) quad & cal(D)_2 <= cal(D)_1 <= cal(D)_3 <= cal(D)_4
    $
]
