#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;

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
    In this document, convention is that all type judgements in a proof tree, unless stated otherwise, is derived from a single and unique $lambda 2$ context per tree.
]

// MARK: Q. 3.1
#problem(source: "3.1")[
    How many $lambda 2$ contexts consisting of four and only four declarations
    $
        & "(1)" Gamma tack alpha : * quad         && "(2)" Gamma tack beta : * \
        & "(3)" Gamma tack f : alpha -> beta quad && "(3)" Gamma tack x : alpha
    $
]
#solution[
    The last two declarations depende on the first two. Therefore this is an easy combinatorics problem: $2! times 2! = 4$ contexts.
]
