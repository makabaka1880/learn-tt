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
#let operators = ($exists$.body, $lambda$.body)
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
