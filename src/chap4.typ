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
    subtitle: "Chapter 4",
    authors: (
        (name: "Sean Li", affiliation: "Reducted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)
#let nat = $mono("nat")$
#let bool = $mono("bool")$
#let ltrue = $"true"$
#let lfalse = $"false"$
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
}; #let symbol = $x$.body.func()
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
                $x in.not "dom" Gamma$,
                $Gamma, x : A tack x : A$,
            ),
        ),
        prooftree(
            rule(
                name: "Weak",
                $Gamma tack A : B$,
                $Gamma tack C : s$,
                $x in.not "dom" Gamma$,
                $Gamma, x : C tack A : B$,
            ),
        ),
        prooftree(
            rule(
                name: "Form",
                $Gamma tack A : s$,
                $Gamma tack B : s$,
                $Gamma tack A -> B : s$,
            ),
        ),
        prooftree(
            rule(
                name: "App",
                $Gamma tack M : A -> B$,
                $Gamma tack N : A$,
                $Gamma tack M N : B$,
            ),
        ),
        prooftree(
            rule(
                name: "Abst",
                $Gamma, x : A tack M : B$,
                $Gamma tack A -> B : s$,
                $Gamma tack lambda x : A. M : A -> B$,
            ),
        ),
        prooftree(
            rule(
                name: "Conv",
                $Gamma tack A : B$,
                $Gamma tack B' : s$,
                $B =^beta B'$,
                $Gamma tack A : B'$,
            ),
        ),
    ))
	Previously an alternative version of the flag derivation was used, only putting up a flag for a local premise (abstraction unwrapping) to save horizontal space. Currently, the standard flag derivation format will be used since now single lines will not be as long.
]
#pagebreak()


// MARK: Q. 4.1
#problem(source: "4.1")[
    Give a complete tree diagram of the derivation in section 4.5 (95)
]
#solution[

    #tidy-tree-graph[
        - conclusion (from O-App) (15)
            - abst (14)
                - form (13)
                    - weak (10) from sort (1)
                    - weak (10) from sort (1)
                - form (12)
                    - var (11)
                        - weak (10) from sort (1)
                    - var (11)
                        - weak (10) from sort (1)
            - var (15)
    ]
]


