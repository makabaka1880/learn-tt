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

// MARK: Q. 3.5 (a)
#problem(source: "3.5 a")[
    Let $bot equiv Pi alpha : *. alpha$. Prove $bot$ is legal.
]
#solution[
    Here a notion called kind checking is introduced. This has not yet been discussed in this book (?
    #proof(ded-nat(arr: (
        (0, $alpha: *$, "Bound"),
        (1, $alpha: *$, "T-Form"),
        (0, $Pi alpha : *. alpha : * -> *$, "T-Form"),
    )))
]

// MARK: Q. 3.5 (b)
#problem(source: "3.5 b")[
    Consider the context $Gamma equiv beta : *, x : bot$. Find an inhabitant of type $beta$ under $Gamma$.
]
#solution[
    $x beta$ is. Because $x$ is of second-order type, it must be parametric to a type, thus $x$ is of form $lambda alpha : *. M$ where $Gamma, alpha : * tack M : alpha$.
    #proof(ded-nat(arr: (
        (0, $x : Pi alpha: *. alpha$, "T-Var"),
        (0, $beta: *$, "T-Form"),
        (0, $x beta : beta$, "1,2 T2-App"),
    )))
]

// MARK: Q. 3.5 (c)
#problem(source: "3.5 c")[
    Give three inhabitants of $beta -> beta$ in $beta$-nf under $Gamma$ in 3.5 b.
]
#solution[
    1. $lambda y : beta. y$.
    #proof(ded-nat(arr: (
        (0, $y : beta$, "Bound"),
        (1, $y : beta$, "T-Var"),
        (0, $lambda y : beta. y : beta -> beta$, "2 T-Abst"),
    )))
    2. $lambda y : beta. x beta$.
    #proof(ded-nat(arr: (
        (0, $y : beta$, "Bound"),
        (1, $x : Pi alpha: *. alpha$, "T-Var"),
        (1, $beta: *$, "T-Form"),
        (1, $x beta : beta$, "2,3 T2-App"),
        (0, $lambda y : beta. x beta : beta -> beta$, "4 T-Abst"),
    )))
    3. $lambda y : beta. x (beta -> beta) y$.
    #proof(ded-nat(arr: (
        (0, $y : beta$, "Bound"),
        (1, $x : Pi alpha: *. alpha$, "T-Var"),
        (1, $beta -> beta: *$, "T-Form"),
        (1, $x (beta -> beta): beta -> beta$, "2,3 T2-App"),
        (1, $y : beta$, "T-Var"),
        (1, $x (beta -> beta) y : beta$, "4,5 T-App"),
        (0, $lambda y : beta. x (beta -> beta) y : beta -> beta$, "5 T-Abst"),
    )))
]

// MARK: Q. 3.5 (d)
#problem(source: "3.5 d")[
    Prove that the following terms inhabit the same type in $Gamma$:
    $ lambda f : beta -> beta -> beta. f (x beta) (x beta) $
    $ x ((beta -> beta -> beta) -> beta) $
]
#solution[
    We simply derive the types.
    #proof(prompt: "First Term", ded-nat(arr: (
        (0, $f : beta -> beta -> beta$, "Bound"),
        (1, $f : beta -> beta -> beta$, "T-Var"),
        (1, $x: Pi alpha : *. alpha$, "T-Var"),
        (1, $beta: *$, "T-Form"),
        (1, $x beta : beta$, "3,4 T2-App"),
        (1, $f (x beta): beta -> beta$, "2,5 T-App"),
        (1, $f (x beta) (x beta) : beta$, "6,5 T-App"),
        (0, $lambda f : beta -> beta -> beta. f (x beta) (x beta): (beta -> beta -> beta) -> beta$, "6 T-Abst"),
    )))
    #proof(prompt: "Second Term", ded-nat(arr: (
        (0, $(beta -> beta -> beta) -> beta : *$, "T-Form"),
        (0, $x : Pi alpha : *. alpha$, "T-Var"),
        (0, $x ((beta -> beta -> beta) -> beta): (beta -> beta -> beta) -> beta$, "2,1 T2-App"),
    )))
    The two terms were shown to both inhabit $(beta -> beta -> beta) -> beta$.
]

// MARK: Q. 3.6 (a)
#problem(source: "3.6 a")[
    Find inhabitant of type
    $ Pi alpha , beta: *. (nat -> alpha) -> (alpha -> nat -> beta) -> nat -> beta $
    In context $Gamma equiv nat: *$.
]
#solution[
    $ lambda alpha, beta: *. lambda x : nat -> alpha. lambda y : (alpha -> nat -> beta). lambda z : nat. y (x z) z $
    #proof(ded-nat(arr: (
        (0, $alpha, beta: *$, "Bound"),
        (0, $nat -> alpha: *$, "T-Form"),
        (1, $x : nat -> alpha$, "Bound"),
        (1, $alpha -> nat -> beta: *$, "T-Form"),
        (2, $y : alpha -> nat -> beta$, "Bound"),
        (2, $nat : *$, "Bound"),
        (3, $z : nat$, "Bound"),
        (4, $y : alpha -> nat -> beta$, "T-Var"),
        (4, $x : nat -> alpha$, "T-Var"),
        (4, $z : nat$, "T-Var"),
        (4, $x z : alpha$, "9,10 T-App"),
        (4, $y (x z) : nat -> beta$, "8,11 T-App"),
        (4, $y (x z) z : beta$, "12,10 T-App"),
        (3, $lambda z : nat. y (x z) z: nat -> beta$, "13 T-Abst"),
        (
            2,
            $
                lambda y : alpha -> nat -> beta. lambda z
                : nat. y (x z) z \ : (alpha -> nat -> beta) -> nat -> beta
            $,
            "14 T-Abst",
        ),
        (
            1,
            $
                lambda & x : nat -> alpha. y : alpha -> nat -> beta. lambda z : nat. y (x z) z \
                       & : (nat -> alpha) -> (alpha -> nat -> beta) -> nat -> beta
            $,
            "15 T-Abst",
        ),
        (
            0,
            $
                lambda & alpha, beta: *. x : nat -> alpha. y : alpha -> nat -> beta. lambda z : nat. y (x z) z \
                       & : Pi alpha, beta: *. (nat -> alpha) ->(alpha -> nat -> beta) -> nat -> beta
            $,
            "16 T2-Abst",
        ),
    )))
]

// MARK: Q. 3.6 (b)
#problem(source: "3.6 b")[
    Find inhabitant of type
    $ Pi delta : *. ((alpha -> gamma) -> delta) -> (alpha -> beta) -> (beta -> gamma) -> delta $
    In context $Gamma equiv alpha: *, beta: *, gamma: *$
]
#solution[
    $
        lambda delta: *. lambda x : (alpha -> gamma) -> delta. lambda y : alpha -> beta. lambda z : beta -> gamma. x (lambda u : alpha. z (y u))
    $
    A derivation in shorthand will be given (omitting T-Form / T-Var)
    #proof(ded-nat(arr: (
        (0, $delta: *$, "Bound"),
        (1, $x : (alpha -> gamma) -> delta$, "Bound"),
        (2, $y : alpha -> beta$, "Bound"),
        (3, $z : beta -> gamma$, "Bound"),
        (4, $u : alpha$, "Bound"),
        (5, $y u : beta$, "*,* T-App"),
        (5, $z (y u) : gamma$, "*,6 T-App"),
        (4, $lambda u : alpha. z (y u) : alpha -> gamma$, "7 T-Abst"),
        (4, $x (lambda u : alpha. z (y u)) : delta$, "8 T-Abst"),
        (3, $lambda z : beta -> gamma. x (lambda u : alpha. z (y u)) : (beta -> gamma) -> delta$, "9 T-Abst"),
        (
            2,
            $
                lambda & y : alpha -> beta. lambda z : beta -> gamma. x (lambda u : alpha. z (y u)) \
                       & : (alpha -> beta) -> (beta -> gamma) -> delta
            $,
            "10 T-Abst",
        ),
        (
            1,
            $
                lambda &x : (alpha -> gamma) -> delta. lambda y : alpha -> beta. lambda z : beta -> gamma. x (lambda u : alpha. z (y u)) \
                & : ((alpha -> gamma) -> beta) -> (alpha -> beta) -> (beta -> gamma) -> delta
            $,
            "11 T-Abst",
        ),
        (
            0,
            $
                lambda delta: *. lambda &x : (alpha -> gamma) -> delta. lambda y : alpha -> beta. lambda z : beta -> gamma. x (lambda u : alpha. z (y u)) \
                & : Pi delta : *. ((alpha -> gamma) -> delta) -> (alpha -> beta) -> (beta -> gamma) -> delta
            $,
            "12 T-Abst",
        ),
    )))
]

// MARK: Q. 3.6 (c)
#problem(source: "3.6 c")[
    Find inhabitant of type
    $ Pi alpha, beta, gamma: *. (alpha -> (beta -> alpha) -> gamma) -> alpha -> gamma $
    In the empty context
]
#solution[
    $
        lambda alpha, beta, gamma: *. lambda f : (alpha -> (beta -> alpha) -> gamma). lambda x : alpha. f x (lambda u : beta. x)
    $
    #proof(ded-nat(arr: (
        (0, $alpha, beta, gamma$, "Bound"),
        (1, $f : alpha -> (beta -> alpha) -> gamma$, "Bound"),
        (2, $x : alpha$, "Bound"),
        (3, $f x : (beta -> alpha) -> gamma$, "*,* T-App"),
        (3, $u : beta$, "Bound"),
        (4, $x : alpha$, "T-Var"),
        (3, $lambda u: beta. x: beta -> alpha$, "6 T-Abst"),
        (3, $f x (lambda u: beta. x) : gamma$, "4,7 T-App"),
        (2, $lambda x : alpha. f x (lambda u : beta. x) : alpha -> gamma$, "8 T-Abst"),
        (
            1,
            $
                lambda & f : alpha -> (beta -> alpha) -> gamma. lambda x : alpha. f x (lambda u : beta. x) \
                       & : (alpha -> (beta -> alpha) -> gamma) -> alpha -> gamma
            $,
            "9 T-Abst",
        ),
        (
            0,
            $
                lambda & alpha, beta, gamma: *. lambda f : alpha -> (beta -> alpha) -> gamma. lambda x : alpha. f x (lambda u : beta. x) \
                & : Pi alpha, beta, gamma: *. (alpha -> (beta -> alpha) -> gamma) -> alpha -> gamma
            $,
            "10 T2-Abst",
        ),
    )))
]

// MARK: Q. 3.7
#problem(source: "3.7")[
    Let $bot equiv Pi alpha: *. alpha$ and context $Gamma equiv alpha: *, beta: *, x : alpha -> bot, f : (alpha -> alpha) -> alpha$. Give a derivation that succesively calculate an inhabitant of $alpha$ and $beta$, both in context $Gamma$.
]
#solution[
    Have $M : alpha := f (lambda n : alpha. n)$. Then $Gamma tack x M beta : beta$.
    #proof(prompt: "Typing M", ded-nat(arr: (
        (0, $f : (alpha -> alpha) -> alpha$, "T-Var"),
        (0, $n : alpha$, "Bound"),
        (1, $n : alpha$, "T-Var"),
        (0, $lambda n : alpha. n : alpha -> alpha$, "3 T-Abst"),
        (0, $f (lambda n : alpha. n) : alpha$, "1,4 T-App"),
    )))
    #proof(prompt: [Typing $x M beta$], ded-nat(arr: (
        (0, $M : alpha$, "T-Var"),
        (0, $x : alpha -> Pi alpha: *. alpha$, "T-Var"),
        (0, $M x : Pi alpha: *. alpha$, "2,1 T-App"),
        (0, $M x beta : beta$, "3, * T2-App"),
    )))
]

// MARK: Q 3.8
#problem(source: "3.8")[
    Recall $K equiv lambda x y. x in Lambda$ from untyped lambda calculus.
    Consider the following types
    $
        T_1 equiv Pi alpha, beta: *. alpha -> beta -> alpha quad T_2 equiv Pi alpha : *. alpha -> (Pi beta : *. beta -> alpha)
    $
    Find inhabitants of both type $t_1 : T_1$ and $t_2 : T_2$ under the empty context, which may be considered the closed $lambda 2$ form of $K in Lambda_(TT 2)$.
]
#solution[
    $ lambda alpha, beta : *. lambda x : alpha. lambda y : beta. x $
    $ lambda alpha : *. lambda x : alpha. lambda beta : *. lambda y : beta. x $
    #proof(prompt: "First Form", ded-nat(arr: (
        (0, $alpha, beta : *$, "Bound"),
        (1, $x : alpha$, "Bound"),
        (2, $y : beta$, "Bound"),
        (3, $x : alpha$, "T-Var"),
        (2, $lambda y : beta. x : beta -> alpha$, "4 T-Abst"),
        (1, $lambda x : alpha. lambda y : beta. x : alpha -> beta -> alpha$, "5 T-Abst"),
        (
            0,
            $lambda alpha, beta : *.lambda x : alpha. lambda y : beta. x : Pi alpha, beta: *. alpha -> beta -> alpha$,
            "5 T-Abst",
        ),
    )))
    #proof(prompt: "Second Form", ded-nat(arr: (
        (0, $alpha: *$, "Bound"),
        (1, $x : alpha$, "Bound"),
        (2, $beta: *$, "Bound"),
        (3, $y : beta$, "Bound"),
        (4, $x : alpha$, "T-Var"),
        (3, $lambda y : beta. x : beta -> alpha$, "5 T-Abst"),
        (2, $lambda beta: *. lambda y : beta. x : Pi beta: *. beta -> alpha$, "6 T-Abst"),
        (1, $lambda x : alpha. lambda beta: *. lambda y : beta. x : alpha -> (Pi beta: *. beta -> alpha)$, "7 T-Abst"),
        (
            0,
            $lambda alpha: *. lambda x : alpha. lambda beta: *. lambda y : beta. x : Pi alpha : *. alpha -> (Pi beta: *. beta -> alpha)$,
            "8 T-Abst",
        ),
    )))
]

// MARK: Q. 3.9
#problem(source: "3.9")[
    Pretype the combinator $ S equiv lambda x y z. x z (y z) $
    In closed form (typable in an empty context) in $Lambda_(TT 2)$.
]
#solution[
    $
        S equiv lambda alpha, beta, gamma : *. lambda x : alpha -> beta -> gamma. lambda y : alpha -> beta. lambda z : alpha. x z (y z)
    $
    #proof(ded-nat(arr: (
        (0, $alpha, beta, gamma : *$, "Bound"),
        (1, $x : alpha -> beta -> gamma$, "Bound"),
        (2, $y : alpha -> beta$, "Bound"),
        (3, $z : alpha$, "Bound"),
        (4, $x z : beta -> gamma$, "*,* T-App"),
        (4, $y x : beta$, "*,* T-App"),
        (4, $x z (y x) : gamma$, "5,6 T-App"),
        (3, $lambda z : alpha. x z (y x) : alpha -> gamma$, "7 T-Abst"),
        (2, $lambda y : alpha -> beta. lambda z : alpha. x z (y x) : (alpha -> beta) -> alpha -> gamma$, "8 T-Abst"),
        (
            1,
            $
                lambda & x : alpha -> beta -> gamma. lambda y : alpha -> beta. lambda z : alpha. x z (y x) \
                       & : (alpha -> beta -> gamma) -> (alpha -> beta) -> alpha -> gamma
            $,
            "9 T-Abst",
        ),
        (
            0,
            $
                lambda & alpha, beta, gamma: *. lambda x : alpha -> beta -> gamma. lambda y : alpha -> beta. lambda z : alpha. x z (y x) \
                & : Pi alpha, beta, gamma:*.(alpha -> beta -> gamma) -> (alpha -> beta) -> alpha -> gamma
            $,
            "10 T-Abst",
        ),
    )))
]
