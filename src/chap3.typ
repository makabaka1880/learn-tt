#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;

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
    subtitle: "Chapter 3",
    authors: (
        (name: "Sean Li", affiliation: "Reducted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)

#let mark(content) = text(content, fill: accent)

#definition[
    Some rules for reference.
    #align(center, rule-set(
        prooftree(
            rule(
                name: "(T-Var)",
                $x : sigma in Gamma$,
                [$Gamma$ is a $lambda 2$ context],
                $Gamma tack x : sigma$,
            ),
        ),
        prooftree(
            rule(
                name: "(T-App)",
                $Gamma tack M : sigma -> tau$,
                $Gamma tack N : sigma$,
                $Gamma tack M N : tau$,
            ),
        ),
        prooftree(
            rule(
                name: "(T-Abst)",
                $Gamma, x : sigma tack M : tau$,
                $Gamma tack lambda x : sigma. M : sigma -> tau$,
            ),
        ),
        prooftree(
            rule(
                name: "(T-Form)",
                $alpha in TT_2$,
                $forall tau in "FV" alpha, Gamma tack tau : *$,
                $alpha : * in Gamma$,
            ),
        ),
        prooftree(
            rule(
                name: "(T2-App)",
                $Gamma tack M : Pi_(alpha : *). A$,
                $Gamma tack B : *$,
                $Gamma tack M B : A[alpha := B]$,
            ),
        ),
        prooftree(
            rule(
                name: "(T2-Abst)",
                $Gamma, alpha : * tack M : A$,
                $Gamma tack lambda alpha : *. M : Pi_(alpha : *) : A$,
            ),
        ),
    ))
    In this document, convention is that all type judgements in a proof tree, unless stated otherwise, is derived from a single and unique $lambda 2$ context per tree. Multiple conclusions might be drawn on a single line from usage of the same inference rule for compactness. Eg:
    #ded-nat(
        arr: (
            ("ex", 0, $alpha, beta : *$, "T-Form"),
        ),
    )
    Is shorthand for
    #ded-nat(arr: (
        ("ex", 0, $Gamma tack alpha : *$, "T-Form"),
        ("ex", 0, $Gamma tack beta : *$, "T-Form"),
    ))
]

// MARK: Q. 3.1
#problem(source: "3.1")[
    How many $lambda 2$ contexts consisting of four and only four declarations
    $
        & "(1)" Gamma tack alpha : * quad         && "(2)" Gamma tack beta : * \
        & "(3)" Gamma tack f : alpha -> beta quad && "(4)" Gamma tack x : alpha
    $
]
#solution[
    The last two declarations depende on the first two. Therefore this is an easy combinatorics problem: $2! times 2! = 4$ contexts:
    $
        1 - 2 - 3- 4 quad 1 - 2 - 4 - 3 \
        2 - 1 - 3 - 4 quad 2 - 1 - 4 - 3
    $
]

// MARK: Q. 3.2
#problem(source: "3.2")[
    Give a full derivation in $lambda 2$ to show the following type term is legal:
    $
        M equiv lambda alpha, beta, gamma : *. lambda f : alpha -> beta. lambda g : beta -> gamma. lambda x : alpha. g (f x)
    $
]
#solution[
    #ded-nat(arr: (
        (0, $alpha : *$, "Bound"),
        (1, $beta : *$, "Bound"),
        (2, $gamma : *$, "Bound"),
        (3, $f : alpha -> beta$, "Bound"),
        (4, $g : beta -> gamma$, "Bound"),
        (5, $x : alpha$, "Bound"),
        (6, $alpha, beta, gamma: *$, "T-Form"),
        (6, $alpha -> beta, beta -> gamma: *$, "T-Form"),
        (6, $f : alpha -> beta, x : alpha$, "T-Var"),
        (6, $f x : beta$, "8,8 T-App"),
        (6, $g : beta -> gamma$, "T-Var"),
        (6, $g (f x) : gamma$, "11,10 T-App"),
        (5, $lambda x : alpha. g (f x) : alpha -> gamma$, "12 T-Abst"),
        (4, $lambda g : beta -> gamma. lambda x : alpha. g (f x) : (beta -> gamma) -> alpha -> gamma$, "13 T-Abst"),
        (
            3,
            $
                lambda f : alpha -> beta. lambda g : beta -> gamma. lambda x : alpha. g (f x) \ : (alpha -> beta) -> (beta -> gamma) -> alpha -> gamma
            $,
            "14 T-Abst",
        ),
        (
            2,
            $
                lambda gamma : *.lambda f : alpha -> beta. lambda g : beta -> gamma. lambda x : alpha. g (f x) \ : Pi gamma : * . (alpha -> beta) -> (beta -> gamma) -> alpha -> gamma
            $,
            "15 T2-Abst",
        ),
        (
            1,
            $
                lambda beta, gamma : *.lambda f : alpha -> beta. lambda g : beta -> gamma. lambda x : alpha. g (f x) \ : Pi beta, gamma : * . (alpha -> beta) -> (beta -> gamma) -> alpha -> gamma
            $,
            "16 T2-Abst",
        ),
        (
            0,
            $
                lambda alpha, beta, gamma : *.lambda f : alpha -> beta. lambda g : beta -> gamma. lambda x : alpha. g (f x) \ : Pi alpha, beta, gamma : * . (alpha -> beta) -> (beta -> gamma) -> alpha -> gamma
            $,
            "17 T2-Abst",
        ),
    ))
]
