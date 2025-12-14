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
#let nat = $mono("nat")$
#let bool = $mono("bool")$
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

// MARK: Q. 3.3 (a)
#problem(source: "3.3 a")[
    Given $M$ in 3.2, and a context $Gamma$ such that
    $ Gamma tack nat : * $
    $ Gamma tack bool : * $
    $ Gamma tack "succ" : nat -> nat $
    $ Gamma tack "even" : nat -> bool $
    Prove $M nat nat bool "succ" "even"$ is legal.
]
#solution[
    Proof by deriving the term's type.
    #proof(ded-nat(arr: (
        (0, $M : Pi alpha, beta, gamma : *. (alpha -> beta) -> (beta -> gamma) -> alpha -> gamma$, "T-Var"),
        (0, $nat, bool : *$, "T-Form"),
        (0, $M nat : Pi beta, gamma : *. (nat -> beta) -> (beta -> gamma) -> nat -> gamma$, "2,1 T2-App"),
        (0, $M nat nat : Pi gamma : *. (nat -> nat) -> (nat -> gamma) -> nat -> gamma$, "2,3 T2-App"),
        (0, $ M nat nat bool : (nat -> nat) -> (nat -> bool) -> nat -> bool $, "2,3 T2-App"),
        (0, $"succ": nat -> nat, "even": nat -> bool$, "T-Var"),
        (0, $M nat nat bool "succ" : (nat -> bool) -> nat -> bool$, "6,5 T-App"),
        (0, $M nat nat bool "succ" "even": nat -> bool$, "6,7 T-App"),
    )))
]

// MARK: Q. 3.3 (b i)
#problem(source: "3.3 b.i")[
    Prove $lambda x : nat. "even" ("succ" x)$ via 3.3 a.
]
#solution[
    The result of beta reduction on the term in 3.3 a is what we are proving.
    #proof[
        $
                     & M nat nat bool "succ" "even" \
               equiv & (lambda alpha, beta, gamma, f, g. lambda x : alpha. g (f x)) nat nat bool "succ" "even" \
            ->>_beta & (lambda f : nat -> nat. lambda g : nat -> bool. lambda x: nat. g (f (x))) "succ" "even" \
             ->_beta & (lambda x : nat. "even" ("succ" x))
        $
        By the subject reduction lemma, $lambda x:nat. "even" ("succ" x)) : nat -> bool$, thus is legal.
    ]
]

// MARK: Q. 3.3 (b ii)
#problem(source: "3.3 b.ii")[
    Prove $lambda x: nat. "even" ("succ" x)$ via derivation in the context provided in 3.3 a.
]
#solution[
    #proof(ded-nat(arr: (
        (0, $nat, bool : *$, "T-Form"),
        (0, $x : nat$, "Bound"),
        (1, $"succ" : nat -> nat$, "T-Var"),
        (1, $x : nat$, "T-Var"),
        (1, $"succ" x : nat$, "3,4 T-App"),
        (1, $"even" : nat -> bool$, "T-Var"),
        (1, $"even" ("succ" x) : bool$, "6,5 T-App"),
        (0, $lambda x : nat. "even" ("succ" x) : nat -> bool$, "7 T-Abst"),
    )))
]

// MARK: Q. 3.4
#problem(source: "3.4")[
    Give a shorthanded (omit T-Var and T-Form) derivation in $lambda 2$ to show the following term is valid in $Gamma equiv nat : *, bool : *$
    $
        (lambda alpha, beta: *. lambda f : alpha -> alpha. lambda g : alpha -> beta. lambda x : alpha. g (f (f x))) nat bool
    $
]
#solution[
    #proof(ded-nat(arr: (
        (0, $alpha, beta: *$, "Bound"),
        (1, $f : alpha -> alpha$, "Bound"),
        (2, $g : alpha -> beta$, "Bound"),
        (3, $x : alpha$, "Bound"),
        (4, $f x : alpha$, "*,* T-App"),
        (4, $f (f x) : alpha$, "*,5 T-App"),
        (4, $g (f (f x)) : beta$, "*,6 T-App"),
        (3, $lambda x : alpha. g (f (f x)) : alpha -> beta$, "7 T-Abst"),
        (2, $lambda g : alpha -> beta. lambda x : alpha. g (f (f x)) : (alpha -> beta) -> alpha -> beta$, "8 T-Abst"),
        (
            1,
            $
                lambda f : alpha -> alpha. lambda g : alpha -> beta. lambda x : alpha. g (f (f x)) \ : (alpha -> alpha) -> (alpha -> beta) -> alpha -> beta
            $,
            "9 T-Abst",
        ),
        (
            0,
            $
                lambda alpha, beta : *. lambda f : alpha -> alpha. lambda g : alpha -> beta. lambda x : alpha. g (f (f x)) \
                : Pi alpha, beta : *.(alpha -> alpha) -> (alpha -> beta) -> alpha -> beta
            $,
            "10 T2-Abst",
        ),
        (
            0,
            $
                (lambda alpha, beta : *. lambda f : alpha -> alpha. lambda g : alpha -> beta. lambda x : alpha. g (f (f x))) nat \
                : Pi beta : *.(nat -> nat) -> (nat -> beta) -> nat -> beta
            $,
            "*,11 T2-App",
        ),
        (
            0,
            $
                (lambda alpha, beta : *. lambda f : alpha -> alpha. lambda g : alpha -> beta. lambda x : alpha. g (f (f x))) nat bool \
                : Pi beta : *.(nat -> nat) -> (nat -> bool) -> nat -> bool
            $,
            "*,12 T2-App",
        ),
    )))
]
