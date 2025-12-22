#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;
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
    title: "Excercises",
    subtitle: "Chapter 5",
    authors: (
        (name: "Sean Li", affiliation: "Reducted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)
#let nat = $mono("nat")$
#let mark(content) = text(content, fill: accent)

// Scripts for correctly spacing juxtaposed applications
#let operators = ($exists$.body, $lambda$.body, $forall$.body, $($.body, $)$.body)
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
#let kind = $square$

#definition[
    Some rules for reference.

    *$lambda P$ Calculus Rules*
    #align(center, rule-set(
        prooftree(
            rule(
                name: "Sort",
                $emptyset tack * : kind$,
            ),
        ),
        prooftree(
            rule(
                name: "Var",
                $Gamma tack A : s$,
                $Gamma, x : A tack x : A$,
            ),
        ),
        prooftree(
            rule(
                name: "Weak",
                $Gamma tack A : B$,
                $Gamma tack C : s$,
                $Gamma, x : C tack A : B$,
            ),
        ),
        prooftree(
            rule(
                name: "Form",
                $Gamma tack A : *$,
                $Gamma, x : A tack B : s$,
                $Gamma tack Pi x : A. B : s$,
            ),
        ),
        prooftree(
            rule(
                name: "App",
                $Gamma tack M : Pi x: A . B$,
                $Gamma tack N : A$,
                $Gamma tack M N : B[ x:=N ]$,
            ),
        ),
        prooftree(
            rule(
                name: "Abst",
                $Gamma, x : A tack M : B$,
                $Gamma tack Pi x : A. B : s$,
                $Gamma tack lambda x : A. M : Pi x:A. B$,
            ),
        ),
        prooftree(
            rule(
                name: "Conv",
                $Gamma tack A : B$,
                $B =^beta B'$,
                $Gamma tack B' : s$,
                $Gamma tack A : B'$,
            ),
        ),
    ))
    *Predicate Logic*
    #align(center, rule-set(
        prooftree(
            rule(
                name: [$=>$I],
                ded-nat(arr: (
                    (0, [Assume $A$], ""),
                    (1, $...$, ""),
                    (1, $B$, ""),
                )),
                $A => B$,
            ),
        ),
        prooftree(
            rule(
                name: [$=>$E],
                $A => B$,
                $A$,
                $B$,
            ),
        ),
        prooftree(rule(
            name: [$forall$I],
            ded-nat(arr: (
                (0, [Let $a in S$], ""),
                (1, $...$, ""),
                (1, $P(a)$, ""),
            )),
            $forall a in S, P(a)$,
        )),
        prooftree(rule(
            name: [$forall$E],
            $forall a in S$,
            $N in S$,
            $P(N)$,
        )),
    ))
]

#pagebreak()

// MARK: Q. 5.1
#problem(source: "5.1")[
    Give a diagram of the tree corresponding to the complete tree derivation of line 18 of Section 5.3 (P 107)
]
#solution[

    #tidy-tree-graph[
        - Abst (18)
            - Abst (17)
                - Var (16)
                    - App (11)
                        - Weak (10)
                            - Var (6)
                                - Form (5)
                                    - Var (2)
                                        - Sort (1)
                                    - Weak (4)
                                        - Weak (3)
                                            - Sort (1)
                                            - Sort(1)
                                        - Var (2)
                            - Weak (7)
                                - Var (2)
                                - Form (5)
                                    - Var (2)
                                    - Weak (4)
                        - Var (9)
                            - Weak (7)
                - Form (14)
                    - App (11)
                    - Weak (13)
                        - App (11)
                        - App (11)
            - Form (15)
                - Weak (7)
                - Form (14)
    ]
]

// MARK: Q. 5.2
#problem(source: "5.2")[
    Give a complete $lambda P$ derivation of
    $ S : * tack S -> S -> * : kind $
    In tree format and flag format.
]
#solution[
    #proof(prompt: "Tree Derivation")[
        #prooftree(
            rule(
                label: "(7)",
                $(3) S : * tack S : *$,
                rule(
                    label: "(6)",
                    name: "Weak",
                    rule(
                        label: "(4)",
                        name: "Weak",
                        $tack * : kind$,
                        $tack * : kind$,
                        $S : * tack * : kind$,
                    ),
                    $(3) S : * tack S : *$,
                    $S : *, x : S tack * : kind$,
                ),
                $S : * tack S -> * : kind$,
            ),
        )
        #prooftree(
            rule(
                name: "Form",
                rule(
                    label: "(3)",
                    name: "Var",
                    $tack * : kind$,
                    $S : * tack S : *$,
                ),
                rule(
                    label: "(9)",
                    name: "Weak",
                    $(7) S : * tack S ->* : kind$,
                    $(3) S : * tack S : *$,
                    $S : *, x : S tack S -> * : kind$,
                ),
                $S : * tack S -> S -> * : kind$,
            ),
        )
    ]
    #proof(prompt: "Flag Derivation")[
        #ded-nat(arr: (
            (0, $* : kind$, "Sort"),
            (0, $S : *$, ""),
            (1, $S : *$, "1 Var"),
            (1, $* : kind$, "1,1 Weak"),
            (1, $x : S$, ""),
            (2, $* : kind$, "4,3 Weak"),
            (1, $S -> * : kind$, "3,6 Form"),
            (1, $x : S$, ""),
            (2, $S -> * : kind$, "7,3 Weak"),
            (1, $S -> S -> * : kind$, "3,9 Form"),
        ))
    ]
]

// MARK: Q. 5.3
#problem(source: "5.3")[
    Derive
    $ S : *, Q : S -> S -> * tack Pi x : S. Pi y : S . Q x y : * $
]

#solution[
    #ded-nat(arr: (
        (0, $* : kind$, "Sort"),
        (0, $S : *$, ""),
        (1, $S : *$, "1 Var"),
        (1, $* : kind$, "1,1 Weak"),
        (1, $x : S$, ""),
        (2, $* : kind$, "4,3 Weak"),
        (1, $S -> * : kind$, "3,6 Form"),
        (1, $x : S$, ""),
        (2, $S -> * : kind$, "7,3 Weak"),
        (1, $S -> S -> * : kind$, "3,9 Form"),
        (1, $Q : S -> S -> *$, ""),
        (2, $Q : S -> S -> *$, "10 Var"),
        (2, $S : *$, "3,10 Weak"),
        (2, $* : kind$, "4,10 Weak"),
        (2, $x : S$, ""),
        (3, $* : kind$, "14,13 Weak"),
        (3, $S : *$, "13,13 Weak"),
        (3, $x : S$, "13 Var"),
        (3, $Q : S -> S -> *$, "12,13 Weak"),
        (3, $y : S$, ""),
        (4, $y : S$, "17 Var"),
        (4, $Q : S -> S -> *$, "19,17 Weak"),
        (4, $x : S$, "18,17 Weak"),
        (4, $Q x : S -> *$, "22,23 App"),
        (4, $Q x y : *$, "24,21 App"),
        (3, $Pi y : S. Q x y : *$, "17,25 Form"),
        (2, $Pi x : S. Pi y : S. Q x y : *$, "13,26 Form"),
    ))
]

// MARK: Q. 5.4
#problem(source: "5.4")[
    Prove that $ast$ is the only valid kind in $lambda P$.
]
#solution[
    #proof[
        The only possible way to construct a new kind is through the $"Form"$ rule and the $"Sort"$ axiom. Because we are trying to construct a kind, $s$ here stands for $kind$.

        #prooftree(
            rule(
                name: "Form",
                $Gamma tack A : *$,
                $Gamma, x : A tack B : kind$,
                $Gamma tack Pi x : A. B : kind$,
            ),
        )
        One could only construct new kinds with kinds, which requires $A : kind$ and $B : kind$. This contradicts with $A : *$.
    ]
]

// MARK: Q. 5.5
#problem(source: "5.5")[
    Prove that $A => ((A => B) => B)$ is a tautology by given a shorthand $lambda P$ derivation.
]
#solution[
    By the principle of PAT, this proposition is equivalent to the type
    $ A, B : * tack A -> (A -> B) -> B $
    And finding an inhabitant in a context only with definition of $A$ and $B$ is equivalent to a proof of tautologousness.
    #proof(ded-nat(arr: (
        (0, $A : *$, ""),
        (1, $B : *$, ""),
        (2, $x : A$, ""),
        (3, $y : A -> B$, ""),
        (4, $y x : B$, "4,3 App"),
        (3, $lambda y : A -> B. y x : (A -> B) -> B$, "5 Abst"),
        (2, $lambda x : A. lambda y : A -> B. y x : A -> (A -> B) -> B$, "5 Abst"),
    )))
]

// MARK: Q. 5.6 (a)
#problem(source: "5.6 a")[
    Prove $(A => (A => B)) => (A => B)$ a tautology using natural deduction.
]
#solution[
    #proof(ded-nat(arr: (
        (0, [Assume $A => (A => B)$], ""),
        (1, $A => (A => B)$, ""),
        (1, [Assume $A$], ""),
        (2, $A$, ""),
        (2, $A => B$, [2,4 $=>$E ]),
        (2, $B$, [5,4 $=>$E]),
        (1, $A => B$, [3,6 $=>$I]),
        (0, $(A => (A => B)) => (A => B)$, [1,7 $=>$I]),
    )))
]

// MARK: Q. 5.6 (b)
#problem(source: "5.6 b")[
    Prove $(A => (A => B)) => (A => B)$ using a shorthand $lambda P$ derivation
]
#solution[
    By the principle of PAT, this proposition is equivalent to the type
    $ A, B : * tack (A -> A -> B) -> A -> B $
    And finding an inhabitant in a context only with definition of $A$ and $B$ is equivalent to a proof of tautologousness.

    #proof(ded-nat(arr: (
        (0, $A : *$, ""),
        (1, $B : *$, ""),
        (2, $x : A -> A -> B$, ""),
        (3, $y : A$, ""),
        (4, $x y : A -> B$, "3,4 App"),
        (4, $x y y : B$, "5,4 App"),
        (3, $lambda y : A. x y y : A -> B$, "6 Abst"),
        (2, $lambda x : A -> A -> B. lambda y : A. x y y : (A -> A -> B) -> A -> B$, "7 Abst"),
    )))
]

// MARK: Q. 5.7 a
#problem(source: "5.7 a")[
    Proof $(A => B) => ((B => C) => (A => C))$ using a shorthand $lambda P$ derivation.
]

#solution[
    By the principle of PAT, this proposition is equivalent to the type
    $ A, B, C : * tack (A -> B) -> (B -> C) -> A -> C $
    And finding an inhabitant in a context only with definition of $A$, $B$, and $C$ is equivalent to a proof of tautologousness.
    #proof(ded-nat(arr: (
        (0, $A : *$, ""),
        (1, $B : *$, ""),
        (2, $C : *$, ""),
        (3, $x : A -> B$, ""),
        (4, $y : B -> C$, ""),
        (5, $a : A$, ""),
        (6, $x a : B$, "4,6 App"),
        (6, $y (x a) : C$, "5,7 App"),
        (5, $lambda a : A. y (x z) : A -> C$, "8 Abst"),
        (4, $lambda y : B -> C. lambda a : A. y (x z) : (B -> C) -> A -> C$, "9 Abst"),
        (
            2,
            $ lambda x : A -> B. lambda y : B -> C. lambda a : A. y (x z) \ : (A -> B) -> (B -> C) -> A -> C $,
            "10 Abst",
        ),
    )))
]

// MARK: Q. 5.7 b
#problem(source: "5.7 b")[
    Proof $((A => B) => A) => ((A => B) => B)$ using a shorthand $lambda P$ derivation.
]

#solution[
    By the principle of PAT, this proposition is equivalent to the type
    $ A, B : * tack ((A -> B) -> A) -> (A -> B) -> B $
    And finding an inhabitant in a context only with definition of $A$ and $B$ is equivalent to a proof of tautologousness.
    #proof(ded-nat(arr: (
        (0, $A : *$, ""),
        (1, $B : *$, ""),
        (2, $x : (A -> B) -> A$, ""),
        (3, $y : A -> B$, ""),
        (4, $x y : A$, "3,4 App"),
        (4, $y (x y) : B$, "4,5 App"),
        (3, $lambda y : A -> B. y (x y) : (A -> B) -> B$, "6 Abst"),
        (2, $ lambda x : (A -> B) -> A. lambda y : A -> B. y (x y) \ : ((A -> B) -> A) -> (A -> B) -> B $, "7 Abst"),
    )))
]

// MARK: Q. 5.7 c
#problem(source: "5.7 c")[
    Proof $(A => (B => C)) => ((A => B) => (A => C))$ using a shorthand $lambda P$ derivation.
]


#solution[
    By the principle of PAT, this proposition is equivalent to the type
    $ A, B, C : * tack (A -> B -> C) -> (A -> B) -> A -> C $
    And finding an inhabitant in a context only with definition of $A$, $B$, and $C$ is equivalent to a proof of tautologousness.
    #proof(ded-nat(arr: (
        (0, $A : *$, ""),
        (1, $B : *$, ""),
        (2, $C : *$, ""),
        (3, $x : A -> B -> C$, ""),
        (4, $y : A -> B$, ""),
        (5, $a : A$, ""),
        (6, $x a : B -> C$, "4,6 App"),
        (6, $y a : B$, "5,6 App"),
        (6, $x a (y a) : C$, "7,8 App"),
        (5, $lambda a : A. x a (y a) : A -> C$, "9 Abst"),
        (4, $lambda y : A -> B. lambda a : A. x a (y a) : (A -> B) -> A -> C$, "10 Abst"),
        (
            3,
            $
                lambda x : A -> B -> C. lambda y : A -> B. lambda a : A. x a (y a) \ : (A -> B -> C) -> (A -> B) -> A -> C
            $,
            "10 Abst",
        ),
    )))
]

// MARK: Q. 5.8 (a)
#problem(source: "5.8 a")[
    Let $Gamma equiv S : *, P : S -> *, Q : S -> *$, find an inhabitant of
    $ Pi x : S. P x -> Q x -> P x $
    with respect to $Gamma$ and give a shorthand $lambda P$ derivation
]
#solution(ded-nat(arr: (
    (0, $S : *$, ""),
    (1, $P : S -> *$, ""),
    (2, $Q : S -> *$, ""),
    (3, $x : S$, ""),
    (4, $a : P x$, ""),
    (5, $b : Q x$, ""),
    (6, $a : P x$, "2,4 App"),
    (5, $lambda b : Q x. S : Q x -> P x$, "7 Abst"),
    (4, $lambda a : P x. lambda b : Q x. a : P x -> Q x -> P x$, "8 Abst"),
    (3, $ lambda x : S. lambda a : P x. lambda b : Q x. a \ : Pi x : S. P x -> Q x -> P x $, "9 Abst"),
)))

// MARK: Q. 5.8 (b)
#problem(source: "5.8 b")[
    Let $Gamma equiv S : *, P : S -> *, Q : S -> *$, find an inhabitant of
    $ Pi x : S. P x -> Q x -> P x $
    By proving the corresponding proposition in natural deduction.
]
#solution[
    The corresponding proposition and premises are
    #prooftree(
        rule(
            $S in "Set"$,
            $P : S -> "Prop"$,
            $Q : S -> "Prop"$,
            $forall a in S, P(a) => (Q(a) => P(a))$,
        ),
    )
    #proof(ded-nat(arr: (
        (0, [Let $a in S$], ""),
        (1, [Assume $P(a)$], ""),
        (2, [Assume $Q(a)$], ""),
        (3, $P(a)$, ""),
        (2, $Q(a) => P(a)$, [3,4 $=>$I]),
        (1, $P(a) => (Q(a) => P(a))$, [2,5 $=>$I]),
        (0, $forall a in S, P(a) => (Q(a) => P(a))$, [1,6 $forall$I]),
    )))
]

// MARK: Q. 5.9 (a)
#problem(source: "5.9 a")[
    Give proof for $ (forall x in S, Q(x)) => (forall y in S, P(y) => Q(y)) $ by natural deduction and a $lambda P$ derivation.
]
#solution[
    #proof(prompt: "Natural Deduction", {
        ded-nat(arr: (
            (0, [Assume $forall x in S, Q(x)$], ""),
            (1, [Let $y in S$], ""),
            (2, [Assume $P(y)$], ""),
            (3, $Q(y)$, [1,2 $forall$E]),
            (2, $P(y) => Q(y)$, [3,4 $=>$I]),
            (1, $forall y in S, P(y) => Q(y)$, [2,5 $forall$I]),
            (0, $(forall x in S, Q(x) => (forall y in S, P(y) => Q(y))$, [1,6 $=>$I]),
        ))
    })
    #proof(prompt: [$lambda$P Derivation])[
        Corresponding type is $ S : *, P : S -> *, Q : S -> * tack (Pi x : S. Q x) -> (Pi y : S. P y -> Q y) $
        #ded-nat(arr: (
            (0, $S : *$, ""),
            (1, $P : S -> *$, ""),
            (2, $Q : S -> *$, ""),
            (3, $a : Pi x : S. Q x$, ""),
            (4, $y : S$, ""),
            (5, $z : P y$, ""),
            (6, $a y : Q y$, "4,5 App"),
            (5, $lambda z : P y. a y : P y -> Q y$, "7 Abst"),
            (4, $lambda y : S. lambda z : P y. a y : Pi y : S. P y -> Q y$, "7 Abst"),
            (
                3,
                $
                    lambda a : Pi x : S. Q x. lambda y : S. lambda z : P y. a y \ : (Pi x : S. Q x) -> (Pi y : S. P y -> Q y)
                $,
                "7 Abst",
            ),
        ))
    ]
]

// MARK: Q. 5.9 (b)
#problem(source: "5.9 b")[
    Give proof for
    $ forall x in S, (P(x) => Q(x)) => ((forall y in S, P(y)) => (forall z in S, Q(z))) $
    by natural deduction and a $lambda P$ derivation
]

#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, [Assume $forall x in S, (P(x) => Q(x))$], ""),
        (1, [Assume $forall y in S, P(y)$], ""),
        (2, [Let $z in S$], ""),
        (3, $P(z)$, [2,3 $forall$E]),
        (3, $P(z) => Q(z)$, [1,3 $forall$E]),
        (3, $Q(z)$, [5,4 $=>$E]),
        (2, $forall z in S, Q(z)$, [3,6 $forall$I]),
        (1, $forall y in S, P(y) => (forall z in S, Q(z))$, [2,7 $forall$I]),
        (0, $forall x in S, (P(x) => Q(x)) => ((forall y in S, P(y)) => (forall z in S, Q(z)))$, [1,8 $forall$I]),
    )))
    #proof(prompt: [$lambda P$ Derivation])[
        Corresponding type is
        $ S : *, P : S -> *, Q : S -> * \ tack (Pi x : S. P x -> Q x) -> (Pi y : S. P y) -> (Pi z : S. Q z) $
        #ded-nat(arr: (
            (0, $S : *$, ""),
            (1, $P : S -> *$, ""),
            (2, $Q : S -> *$, ""),
            (3, $a : Pi x : S. P x -> Q x$, ""),
            (4, $b : Pi y : S. P y$, ""),
            (5, $z : S$, ""),
            (6, $b z : P z$, "5,6 App"),
            (6, $a z : P z -> Q z$, "4,6 App"),
            (6, $a z (b z) : Q z$, "8,7 App"),
            (5, $lambda z : S. a z (b z) : Pi z: S. Q z$, "9 Abst"),
            (4, $ lambda b : (Pi y : S. P y). lambda z : S. a z (b z) \ : (Pi y : S. P y) -> Pi z: S. Q z $, "10 Abst"),
            (
                3,
                $
                    & lambda a : (Pi x : S. P x -> Q x) . lambda b : (Pi y : S. P y). \
                    & quad lambda z : S. a z (b z) \
                    & quad quad : (Pi x : S. P x -> Q x) -> \
                    & quad quad quad quad (Pi y : S. P y) -> Pi z: S. Q z
                $,
                "10 Abst",
            ),
        ))
    ]
]

// MARK: Q. 5.10
#problem(source: "5.10")[
    Given a context
    $
        Gamma equiv & S : *, P : S -> *, f : S -> S, g : S -> S, \
                    & u : Pi x : S. (P (f x) -> P (g x)), \
                    & v : Pi x, y : S. ((P x -> P y) -> P (f x))
    $
    Let $ M equiv lambda x : S. v (f x) (g x) (u x) $
    Type $M$ under $Gamma$.
]

#solution(ded-nat(arr: (
    (0, $x : S$, ""),
    (1, $f : S -> S$, ""),
    (1, $f x : S$, "2,1 App"),
    (1, $g : S -> S$, ""),
    (1, $g x : S$, "4,1 App"),
    (1, $u : Pi x : S. (P (f x) -> P (g x))$, ""),
    (1, $u x : P (f x) -> P (g x)$, "6,1 App"),
    (1, $v : Pi x, y : S. ((P x -> P y) -> P (f x))$, ""),
    (1, $v (f x) : Pi y : S. ((P (f x) -> P y) -> P (f (f x)))$, "8,3 App"),
    (1, $v (f x) (g x) : (P (f x) -> P (g x)) -> P (f (f x))$, "9,5 App"),
    (1, $v (f x) (g x) (u x) : P (f (f x))$, "10,7 App"),
    (0, $lambda x : S. v (f x) (g x) (u x) : S -> P (f (f x))$, "11 Abst"),
)))
