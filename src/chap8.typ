#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/cetz:0.4.2" as cc: *;
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
    subtitle: "Chapter 8",
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


// MARK: Q. 8.1
#let coprime = "coprime"
#problem(source: "Q 8.1")[
    Let
    $
        Gamma equiv & ZZ : *_s, NN^+ : *_s \
               defs & p(m, n, u) := sorry : exists x,y : ZZ. (m x + n y = 1) \
               defs & coprime(m, n) := sorry : *_p \
               defs & q(m, n) := sorry : coprime(m, n) -> coprime(n, s) \
              equiv & n : NN^+, m : NN^+, u : coprime(m, n) \
    $
    Prove $exists x,y : ZZ. (n x + m y = 1)$ in $Gamma$.
]
#solution[
    #proof(ded-nat(arr: (
        (0, $q(m, n) : coprime(m, n) -> coprime(n, m)$, ""),
        (0, $q(m, n) u : coprime(n, m)$, ""),
        (0, $p(n, m, (q(m, n) u)) : exists x, y : ZZ. (n x + m y = 1)$, ""),
    )))
]

