
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
    subtitle: "Chapter 7",
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

#definition(prompt: [ Reference - Propositional Logic in $lambda C$ ])[
    #align(center, rule-set(
        prooftree(rule(
            name: [$bot$I or $not$E],
            $A$,
            $not A$,
            $bot$,
        )),
        prooftree(rule(
            name: [$bot$E],
            $bot$,
            $A$,
        )),
        prooftree(rule(
            name: [$and$I],
            $A$,
            $B$,
            $A and B$,
        )),
        prooftree(rule(
            name: [$and$EL],
            $A and B$,
            $A$,
        )),
        prooftree(rule(
            name: [$and$ER],
            $A and B$,
            $B$,
        )),
        prooftree(rule(
            name: [$or$IL],
            $a$,
            $a or b$,
        )),
        prooftree(rule(
            name: [$or$IR],
            $b$,
            $a or b$,
        )),
        prooftree(rule(
            name: [$=>$E],
            $A => B$,
            $A$,
            $B$,
        )),
        prooftree(rule(
            name: [$or$E],
            $A or B$,
            $A -> C$,
            $B -> C$,
            $C$,
        )),
        prooftree(rule(
            name: [$exists$I],
            $a in S$,
            $P(a)$,
            $exists a in S, P(a)$,
        )),
        prooftree(rule(
            name: [$not$I],
            ded-nat(arr: ((0, $A$, ""), (1, "...", ""), (1, $bot$, ""))),
            $not A$,
        )),
        prooftree(rule(
            name: [$=>$I],
            ded-nat(arr: ((0, $A$, ""), (1, $...$, ""), (1, $B$, ""))),
            $A => B$,
        )),
        prooftree(rule(
            name: [$forall I$],
            ded-nat(arr: ((0, $a in S$, ""), (1, $...$, ""), (1, $P(a)$, ""))),
            $forall a in S, P(a)$,
        )),
        prooftree(rule(
            name: [$exists$E],
            $exists x in S, P(x)$,
            $forall x in S, (P(x) => A)$,
            $A$,
        )),
        prooftree(rule(
            name: [$forall$E],
            $a in S$,
            $forall x in S, P(x)$,
            $P(a)$,
        )),
        prooftree(rule(
            name: "DN (Classical)",
            $not not A => A$,
        )),
        prooftree(rule(
            name: "ET (Classical)",
            $A or not A$,
        )),
    ))
]

#definition(prompt: "Reference - 2nd Encoding for Propositional Logic")[
    #table(
        columns: (.4fr, .6fr),
        stroke: none,
        row-gutter: -1mm,
        [*Proposition*], [*Minimal Propositional Logic*],
        $bot$, $forall A, A$,
        $A => B$, $A => B$,
        $not A$, $A => bot$,
        $A and B$, $forall C, (A => B => C) => C$,
        $A or B$, $forall C, (A => C) => (B => C) => C$,
        $forall a in S, P(a)$, $forall a in S. P(a)$,
        $exists a in S, P(a)$, $forall alpha, (forall a in S, (P(a) => alpha)) => alpha$,
    )
]

// MARK: Q. 7.1 (a)
#problem(source: "7.1 a")[
    Prove in natural deduction and $lambda C$ the tautology $ B => (A => B) $
]
#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, $B$, ""),
        (1, $A$, ""),
        (2, $B$, ""),
        (1, $A => B$, [$=>$I]),
        (0, $B => (A => B)$, [$=>$I]),
    )))
    #proof(prompt: $lambda C$, [
        Assuming context $Gamma equiv A : *, B : *$. By the PAT paradigm the proof is equivalent to an inhabitant of $B -> A -> B$.
        #ded-nat(arr: (
            (0, $A : *, B : *$, ""),
            (1, $x : B$, ""),
            (2, $y : A$, ""),
            (3, $x : B$, "Weak"),
            (2, $lambda y : A. x : A -> B$, "4 Abst"),
            (1, $lambda x : B. lambda y : A. x : B -> A -> B$, "5 Abst"),
        ))
    ])
]

// MARK: Q. 7.1 (b)
#problem(source: "7.1 b")[
    Prove in natural deduction and $lambda C$ the tautology $ not A => (A => B) $
]
#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, $not A$, ""),
        (1, $A$, ""),
        (2, $not A$, ""),
        (2, $A$, ""),
        (2, $bot$, [$bot$I]),
        (2, $B$, [$bot$E]),
        (1, $A => B$, [$=>$I]),
        (0, $not A => (A => B)$, [$=>$I]),
    )))
    #proof(prompt: $lambda C$)[
        Assuming context $Gamma equiv A : *, B : *$. By the PAT paradigm the proof is equivalent to an inhabitant of $(A -> bot) -> A -> B$.
        #ded-nat(arr: (
            (0, $A : *, B : *$, ""),
            (1, $x : not A$, ""),
            (2, $y : A$, ""),
            (3, $x y : Pi alpha : *. alpha$, "2,3 App (Neg Elim)"),
            (3, $x y B : B$, "4,1 App (Ex Falso)"),
            (2, $lambda y : A. x y B : A -> B$, "5 Abst"),
            (1, $lambda x : not A. lambda y : A. x y B : not A -> A -> B$, "6 Abst"),
        ))
    ]
]

// MARK: Q. 7.1 (c)
#problem(source: "7.1 c")[
    Prove in natural deduction and $lambda C$ the tautology $ (A => not B) => ((A => B) => not A) $
]

#solution[
    #proof(prompt: "Natural Deduction")[
        #ded-nat(arr: (
            (0, $A => not B$, ""),
            (1, $A => B$, ""),
            (2, $A$, ""),
            (3, $not B$, [1,3 $=>$E]),
            (3, $B$, [2,3 $=>$E]),
            (3, $bot$, [5,4 $bot$I]),
            (2, $not A$, [3,6 $not$I]),
            (1, $(A => B) => not A$, [2,7 $=>$I]),
            (0, $(A => not B) => ((A => B) => not A)$, [1,8 $=>$I]),
        ))
    ]
    #proof(prompt: $lambda C$)[
        Assuming context $Gamma equiv A : *, B : *$. The proof should be equivalent to an inhabitant of $(A -> B -> bot) -> (A -> B ) -> A -> bot$.
        #ded-nat(arr: (
            (0, $A : *, B : *$, ""),
            (1, $h : A -> not B$, ""),
            (2, $q : A -> B$, ""),
            (3, $a : A$, ""),
            (4, $q a : B$, "3,4 App"),
            (4, $h a : B -> bot$, "2,4 App"),
            (4, $h a (q a) : bot$, "6,5 App (Neg Elim)"),
            (3, $lambda a : A. h a (q a) : not A$, "7 Abst (Neg Intro)"),
            (2, $lambda q : A -> B. lambda a : A. h a (q a) : A -> B -> not A$, "8 Abst"),
            (
                1,
                $
                    & lambda h : A -> not B. lambda q : A -> B. lambda a : A. h a (q a) \
                    & quad : (A -> not B) -> A -> B -> not A
                $,
                "9 Abst",
            ),
        ))
    ]
]

// MARK: Q. 7.1 (d)
#problem(source: "7.1 d")[
    Prove in natural deduction and $lambda C$ the tautology
    $ not (A => B) => not B $
]
#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, $not (A => B)$, ""),
        (1, $B$, ""),
        (2, $A$, ""),
        (3, $B$, ""),
        (2, $A => B$, [3,4 $=>$I]),
        (2, $bot$, [5,1 $bot$I]),
        (1, $not B$, [6 $not$I]),
        (0, $not (A => B) => not B$, [1,7 $=>$I]),
    )))
    #proof(prompt: $lambda C$)[
        Assuming context $Gamma equiv A : *, B : *$. The proof should be equivalent to an inhabitant of $((A -> B) -> bot) -> B -> bot$.
        #ded-nat(arr: (
            (0, $n : not (A -> B)$, ""),
            (1, $b : B$, ""),
            (2, $a : A$, ""),
            (3, $b : B$, "Weak"),
            (2, $lambda a : A. b : A -> B$, "4 Abst"),
            (2, $n (lambda a : A. b) : bot$, "1,5 App (Neg Elim)"),
            (1, $lambda b : B. n (lambda a : A. b) : not B$, "6 Abst (Neg Intro)"),
            (
                0,
                $
                    & lambda n : not (A -> B). lambda b : B. n (lambda a : A. b) \
                    & quad : not (A -> B) -> not B
                $,
                "7 Abst",
            ),
        ))
    ]
]

// MARK: Q. 7.2
#problem(source: "7.2")[
    Formulate the double negation law as an axiom in $lambda C$, and prove the following tautology in $lambda C$ with DN.
    $ (not A => A) => A $
]
#solution[
    The rule
    #align(center, prooftree(rule(name: "DN-E", $not not A => A$)))
    Could be translated into lambda calculus as
    $ Pi A : *. ((A -> bot) -> bot) -> A $
    #proof[
        Assume context $Gamma equiv A : *.$
        #ded-nat(arr: (
            (0, $A : *$, ""),
            (1, $h : not A -> A$, ""),
            (2, $x : not A$, ""),
            (3, $h x : A$, "2,3 App"),
            (3, $x (h x) : bot$, "3,4 App (Contradiction)"),
            (2, $lambda x : not A. x (h x) : not not A$, "5 Abst (Neg Intro)"),
            (2, $"DN" A : not not A -> A$, "1,1 App"),
            (2, $"DN" A (lambda x : not A. x (h x)) : A$, "App (Axiom DN)"),
            (
                1,
                $
                    & lambda h : not A -> A. "DN" A (lambda x : not A. x (h x)) \
                    & quad : (not A -> A) -> A
                $,
                "8 Abst",
            ),
        ))
    ]
]