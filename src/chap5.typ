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
                $Gamma tack A : s$,
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
