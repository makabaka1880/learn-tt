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
    subtitle: "Chapter 3",
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
            "15 T2-Abst",
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
            "12 T2-Abst",
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
        (0, $M x beta : beta$, "3,* T2-App"),
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
            "5 T2-Abst",
        ),
    )))
    #proof(prompt: "Second Form", ded-nat(arr: (
        (0, $alpha: *$, "Bound"),
        (1, $x : alpha$, "Bound"),
        (2, $beta: *$, "Bound"),
        (3, $y : beta$, "Bound"),
        (4, $x : alpha$, "T-Var"),
        (3, $lambda y : beta. x : beta -> alpha$, "5 T-Abst"),
        (2, $lambda beta: *. lambda y : beta. x : Pi beta: *. beta -> alpha$, "6 T2-Abst"),
        (1, $lambda x : alpha. lambda beta: *. lambda y : beta. x : alpha -> (Pi beta: *. beta -> alpha)$, "7 T-Abst"),
        (
            0,
            $lambda alpha: *. lambda x : alpha. lambda beta: *. lambda y : beta. x : Pi alpha : *. alpha -> (Pi beta: *. beta -> alpha)$,
            "8 T2-Abst",
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
            "10 T2-Abst",
        ),
    )))
]

// MARK: Q. 3.10 (a)
#problem(source: "3.10 a")[
    Consider the term $ M equiv lambda x : Pi alpha: *. alpha -> alpha. x (sigma -> sigma) (x sigma) $
    Prove that $M$ is legal.
]
#solution[
    For a term to be legal there must exist a context so that the term could be typed. Here, a witness context is $Gamma equiv sigma: *$.
    #proof(ded-nat(arr: (
        (0, $x : Pi alpha: *. alpha -> alpha$, "Bound"),
        (1, $x (sigma -> sigma): (sigma -> sigma) -> (sigma -> sigma)$, "*,* T2-App"),
        (1, $x sigma : sigma -> sigma$, "*,* T2-App"),
        (1, $x (sigma -> sigma) (x sigma) : sigma -> sigma$, "2,3 T-App"),
        (
            0,
            $
                lambda x : Pi alpha: *. alpha -> alpha. x (sigma -> sigma) (x sigma) \ : (Pi alpha : *. alpha -> alpha) -> sigma -> sigma
            $,
            "4 T-Abst",
        ),
    )))
]

// MARK: Q. 3.10 (b)
#problem(source: "3.10 b")[
    Find a term $N$ such that $M N$ is legal and may be considered to be a way to add type information to $(lambda x. x x) (lambda y. y)$
]
#solution[
    $ M sigma N equiv (lambda x : Pi alpha : *. alpha -> alpha. x (sigma -> sigma) (x sigma)) sigma (lambda y : sigma. y) $ Is the same as $(lambda x. x x) (lambda y. y)$ modulo type annotations.
    #proof(ded-nat(arr: (
        (0, $M : (Pi alpha: *. alpha -> alpha) -> sigma -> sigma$, "T-Var"),
        (0, $M sigma : (sigma -> sigma) -> sigma -> sigma$, "1,* T2-App"),
        (0, $y : sigma$, "Bound"),
        (1, $y : sigma$, "T-Var"),
        (0, $"have" N := lambda y: sigma. y : sigma -> sigma$, "4 T-Abst"),
        (0, $M sigma N : sigma -> sigma$, "2,5 T-Abst"),
    )))
]

// MARK: Q. 3.11
#problem(source: "3.11")[
    Recall $bot equiv Pi alpha:*. alpha$ from 3.5. Type and prove the following term legal:
    $ lambda x : bot . x (bot -> bot -> bot) (x (bot -> bot) x) (x (bot -> bot -> bot) x x) $
]

#solution(
    proof[
        The type $bot -> bot$ is closed and well formed. Therefore, the term is legal.
        #ded-nat(arr: (
            (0, $bot : * equiv Pi alpha: *. alpha$, "T-Form"),
            (0, $x : bot$, "Bound"),
            (1, $x (bot -> bot -> bot) : bot -> bot -> bot$, "*,* T2-App"),
            (1, $x (bot -> bot) : bot -> bot$, "*,* T2-App"),
            (1, $x (bot -> bot) x : bot$, "4,* T-App"),
            (1, $x (bot -> bot -> bot) (x (bot -> bot) x) : bot -> bot$, "3,5 T-App"),
            (1, $x (bot -> bot -> bot) x : bot -> bot$, "3,* T-App"),
            (1, $x (bot -> bot -> bot) x x : bot$, "7,* T-App"),
            (1, $x (bot -> bot -> bot) (x (bot -> bot) x) (x (bot -> bot -> bot) x x): bot$, "6,8 T-App"),
            (
                0,
                $ lambda x : bot. x (bot -> bot -> bot) (x (bot -> bot) x) \ (x (bot -> bot -> bot) x x): bot -> bot $,
                "9 T-Abst",
            ),
        ))
    ],
)

// MARK: Q. 3.12
#problem(source: "3.12")[
    Given the Polymorphic Church Numerals:
    $
        nat in TT_2 & := Pi alpha: *. (alpha -> alpha) -> alpha -> alpha \
        overline(0) & equiv lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. x : nat \
        overline(1) & equiv lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f x : nat \
        overline(2) & equiv lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f (f x) : nat \
             "succ" & equiv lambda n : nat. lambda beta: *. lambda f : beta -> beta. lambda x: beta. f (n beta f x)
    $
    Prove that
    $
        "succ" overline(0) & =_beta overline(1) \
        "succ" overline(1) & =_beta overline(2)
    $
]

#solution[
    $
        & "succ" overline(0) \
        equiv & (lambda n : nat. lambda beta: *. lambda f : beta -> beta. lambda x: beta. f (n beta f x)) (lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. x) \
        ->_beta & (lambda beta: *. lambda f : beta -> beta. lambda x: beta. f ((lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. x) beta f x)) \
        ->_(beta_(TT 2)) & (lambda beta: *. lambda f : beta -> beta. lambda x: beta. f ((lambda f : beta -> beta. lambda x : beta. x) f x)) \
        ->>_beta & (lambda beta: *. lambda f : beta -> beta. lambda x: beta. f x) equiv^(beta -> alpha)_(alpha_(TT 2)) overline(1)
    $
    $
        & "succ" overline(1) \
        equiv & (lambda n : nat. lambda beta: *. lambda f : beta -> beta. lambda x: beta. f (n beta f x)) (lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f x) \
        ->_beta & (lambda beta: *. lambda f : beta -> beta. lambda x: beta. f ((lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f x) beta f x)) \
        ->_(beta_(TT 2)) & (lambda beta: *. lambda f : beta -> beta. lambda x: beta. f ((lambda f : beta -> beta. lambda x : beta. f x) f x)) \
        ->>_beta & (lambda beta: *. lambda f : beta -> beta. lambda x: beta. f(f x)) equiv^(beta -> alpha)_(alpha_(TT 2)) overline(2)
    $
]

// MARK: Q. 3.13 (a)
// The original problem
#problem(source: "3.13 a")[
    We define  addition in Polymorphic Church Numerals as
    $
        "add" equiv lambda m, n : nat. lambda alpha: *. lambda f: alpha -> alpha. lambda x : nat. m alpha f (n alpha f x)
    $
    Show that $ "add" overline(1) " " overline(1) =_beta overline(2) $
]

#solution[
    $
        & "add" overline(1) " " overline(1) \
        equiv & (lambda m, n : nat. lambda alpha: *. lambda f: alpha -> alpha. lambda x : alpha. m alpha f (n alpha f x)) overline(1) " " overline(1) \
        ->>_beta & lambda alpha: *. lambda f: alpha -> alpha. lambda x : alpha. overline(1) alpha f (overline(1) alpha f x) \
        equiv & lambda alpha: *. lambda f: alpha -> alpha. lambda x : alpha. overline(1) alpha f ((lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f x) alpha f x) \
        ->>_beta & lambda alpha: *. lambda f: alpha -> alpha. lambda x : alpha. overline(1) alpha f (f x) \
        equiv & lambda alpha: *. lambda f: alpha -> alpha. lambda x : alpha. (lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f x) alpha f (f x) \
        ->>_beta & lambda alpha: *. lambda f: alpha -> alpha. lambda x : alpha. f (f x) equiv_alpha overline(2)
    $
]

// MARK: Q. 3.13 (b)
#problem(source: "3.13 b")[
    Find a term $"mul"$ simulates multiplication on $nat$.
]
#solution[
    $
        "mul" equiv lambda m,n : nat. lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. m alpha (n alpha f) x
    $
    #proof[
        We derive the type first to prove a legal term.
        #ded-nat(arr: (
            (0, $m, n : nat$, "Bound"),
            (1, $alpha : *$, "Bound"),
            (2, $f : alpha -> alpha$, "Bound"),
            (3, $x : alpha$, "Bound"),
            (4, $m alpha : (alpha -> alpha) -> alpha -> alpha$, "*,* T2-App"),
            (4, $n alpha : (alpha -> alpha) -> alpha -> alpha$, "*,* T2-App"),
            (4, $n alpha f : alpha -> alpha$, "6,* T-App"),
            (4, $m alpha (n alpha f) : alpha -> alpha$, "5,7 T-App"),
            (4, $m alpha (n alpha f) x : alpha$, "8,* T-App"),
            (3, $lambda x : alpha. m alpha (n alpha f) x : alpha -> alpha$, "9 T-Abst"),
            (
                2,
                $lambda f : alpha -> alpha. lambda x : alpha. m alpha (n alpha f) x : (alpha -> alpha) -> alpha -> alpha$,
                "10 T-Abst",
            ),
            (
                1,
                $lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. m alpha (n alpha f) x :nat$,
                "11 T2-Abst",
            ),
            (
                0,
                $
                    lambda & m, n : nat. lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. m alpha (n alpha f) x \
                           & : nat -> nat -> nat
                $,
                "12 T-Abst",
            ),
        ))
        This proves that the term does indeed produce a natural number from two.  Next let's prove that
        $ forall overline(n), overline(m) : nat quad "mul" overline(n) " " overline(m) = overline(n times m) $
        It could be proven by induction that
        $
            forall overline(a) : nat quad overline(a) equiv lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. f^a x
        $
        $
            "mul" overline(n) " " overline(m)
            equiv & (lambda m,n : nat. lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. m alpha (n alpha f) x) (overline(n)) (overline(m)) \
            ->>_beta & lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. overline(n) alpha (overline(m) alpha f) x \
            ->>_beta & lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. overline(n) alpha (lambda u : alpha. f^m u) x \
            ->>_beta & lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. (lambda f : alpha -> alpha. lambda x : alpha. f^n x)(lambda u : alpha. f^m u) x \
            ->>_beta & lambda alpha : *. lambda f : alpha -> alpha. lambda x : alpha. (lambda u : alpha. f^m u)^n x \
        $
        By induction this can be further beta-reduced to
        $
            ->>_beta & lambda alpha : *. lambda f: alpha -> alpha. lambda x : alpha. f^(m n) x equiv overline(m n)
        $
    ]
]

// MARK: Q. 3.14
#problem(source: "3.14")[
    We present the Church-Encoded Boolean:
    $
        bool in TT_2 & := Pi alpha : *. alpha -> alpha -> alpha \
               ltrue & equiv lambda alpha : *. lambda x, y : alpha. x \
              lfalse & equiv lambda alpha : *. lambda x, y : alpha. y \
    $
    Construct a $lambda 2$ term $"neg"$ such that $"neg" ltrue =_beta lfalse$ and $"neg" lfalse =_beta ltrue$.
]
#solution[
    $ "neg" equiv lambda b : bool. lambda alpha : *. b alpha (lfalse alpha) (ltrue alpha) $
    #proof(prompt: "Neg True")[
        $
            "neg" ltrue & equiv (lambda b : bool. lambda alpha : *. b alpha (lfalse alpha) (ltrue alpha)) ltrue \
                        & ->>_beta lambda alpha: *. (lambda x, y: alpha. x) (lfalse alpha) (ltrue alpha) \
                        & ->_beta lambda alpha: *. lfalse alpha ->_eta lfalse
        $
    ]
    #proof(prompt: "Neg False")[
        $
            "neg" lfalse & equiv (lambda b : bool. lambda alpha : *. b alpha (lfalse alpha) (ltrue alpha)) lfalse \
                         & ->>_beta lambda alpha: *. (lambda x, y: alpha. y) (lfalse alpha) (ltrue alpha) \
                         & ->_beta lambda alpha: *. ltrue alpha ->_eta ltrue
        $
    ]
]

// MARK: Q. 3.15
#problem(source: "3.15")[
    Define
    $ M equiv lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta x y) (v beta y y) $
    And reduce $M ltrue ltrue$, $M ltrue lfalse$, $M lfalse ltrue$, $M lfalse lfalse$, and decide which logical operator is represented by $M$.
]
#solution[
    $
        M ltrue ltrue &equiv (lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta x y) (v beta y y)) ltrue ltrue \
        ->>_beta& lambda beta: *. lambda x, y : beta. ltrue beta (ltrue beta x y)(ltrue beta y y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. (ltrue beta x y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. x equiv_alpha ltrue \
    $
    $
        M ltrue lfalse &equiv (lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta x y) (v beta y y)) ltrue lfalse \
        ->>_beta& lambda beta: *. lambda x, y : beta. ltrue beta (lfalse beta x y)(lfalse beta y y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. (lfalse beta x y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. y equiv_alpha lfalse \
    $
    $
        M lfalse ltrue &equiv (lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta x y) (v beta y y)) lfalse ltrue \
        ->>_beta& lambda beta: *. lambda x, y : beta. lfalse beta (ltrue beta x y)(ltrue beta y y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. (ltrue beta y y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. y equiv_alpha lfalse \
    $
    $
        M lfalse lfalse &equiv (lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta x y) (v beta y y)) lfalse lfalse \
        ->>_beta& lambda beta: *. lambda x, y : beta. lfalse beta (lfalse beta x y)(lfalse beta y y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. (lfalse beta y y) \
        ->>_beta& lambda beta: *. lambda x, y : beta. y equiv_alpha lfalse \
    $
    Therefore $M$ is equivalent to logical AND.
]

// MARK: Q. 3.16
#problem(source: "3.16")[
    Find $lambda 2$ term representing the logical OR, XOR, IMP.
]
#solution[
    $
         "OR" & equiv lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta x (v beta x y) \
        "XOR" & equiv lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta y x) (v beta x y) \
        "IMP" & equiv lambda u, v : bool. lambda beta: *. lambda x, y : beta. u beta (v beta x y) x
    $
    All of them could be checked by finite enumeration over $bool times bool$.
]

// MARK: Q. 3.17
#problem(source: "3.17")[
    Find $"isZero" : nat -> bool$ such that $forall n : nat, "isZero" n =_beta lfalse$ except when $n equiv overline(0)$.
]

#solution[
    $
        "isZero" equiv lambda n : nat. n bool (lambda u : bool. lfalse) ltrue
    $
    #proof[
        $
            "isZero" overline(0) & equiv (lambda n : nat. n bool (lambda u : bool. lfalse) ltrue) overline(0) \
            & ->>_beta (lambda alpha: *. lambda f : alpha -> alpha. lambda x : alpha. x) bool (lambda u : bool. lfalse) ltrue \
            & ->>_beta (lambda f : bool -> bool. lambda x : bool. x) (lambda u : bool. lfalse) ltrue \
            & ->>_beta ltrue
        $
    ]
    By induction it could be proven that any other natural numbers must be applied $lambda u : bool. lfalse$ to the body, making the result false, except for $overline(0)$, where the function $f: alpha -> alpha$ never got applied.
]


// MARK: Q. 3.18 a
#problem(source: "3.18 a")[
    Define type
    $ mono("tree") equiv Pi alpha: *. (bool -> alpha) -> (bool -> alpha -> alpha -> alpha) -> alpha $
    Then we construct an inhabitant
    $ lambda alpha. *. lambda u : bool -> alpha. lambda v : bool -> alpha -> alpha -> alpha. M $
    Is a node of a binary tree.
    Sketch graphs of trees where $M$ is
    $
        u lfalse \
        v ltrue (u lfalse) (u ltrue) \
        v ltrue (u ltrue) (v lfalse (u ltrue) (u lfalse))
    $
]
#solution[
    A binary tree is usually defined as this:
    ```lean
    inductive Tree (α : Type) where
      | leaf (value : α) : Tree α
      | node (left right : Tree α) : Tree α
    ```
    With two constructors: a leaf or a node. Here $alpha$ is the type of the payload at each node. There are two constructors: $u$ is the left constructor, taking a $bool$ value for the direction of the node. The $v$ term is the node constructor, taking a $bool$ as the direction, two $alpha$-typed terms as it's children.


    #align(center + bottom, grid(
        columns: 3,
        tidy-tree-graph[
            - ROOT
                + $<-$
                - $u lfalse$
        ],
        tidy-tree-graph[
            - ROOT
                + $->$
                - $v ltrue$
                    + $<-$
                    - $u lfalse$
                    + $->$
                    - $u ltrue$
        ],
        tidy-tree-graph[
            - ROOT
                + $->$
                - $v ltrue$
                    + $<-$
                    - $v lfalse$
                        + $<-$
                        - $u ltrue$
                        + $->$
                        - $u lfalse$
                    + $->$
                    - $u ltrue$
        ],

        column-gutter: 10%,
    ))
]

// MARK: Q. 3.18 (b)
#problem(source: "3.18 b")[
    Give a $lambda 2$ term, which, given input a polymorphic boolean $p$ and two trees $s$ and $t$, delivers the combined tree with $p$ on top, left subtree $s$ and right subtree $t$.
]
#solution[
    $
        "leaf" := & lambda p : bool. lambda s, t : mono("tree"). \
                  & wide lambda alpha. lambda u. bool -> alpha. lambda v: bool -> alpha -> alpha -> alpha. \
                  & wide wide v p (s alpha u v) (t alpha u v)
    $
    #proof[
        We suppose
        $
            s equiv lambda beta : *. lambda u_s : bool -> beta. lambda v_s : bool -> beta -> beta -> beta. S \
            t equiv lambda gamma : *. lambda u_t : bool -> gamma. lambda v_t : bool -> gamma -> gamma -> gamma. T \
        $
        We want
        $
            "leaf" p s t =_beta lambda alpha: *. lambda u : bool -> alpha. lambda v : bool -> alpha -> alpha -> alpha. v p S T
        $
        For compactness we denote
        $
            alpha : * tack tau_"mkleaf" & equiv bool -> alpha \
            alpha : * tack tau_"mknode" & equiv bool -> alpha -> alpha -> alpha
        $
        By beta reduction we have
        $
            "leaf" p s t & equiv (lambda p : bool. lambda s, t : mono("tree"). ...) p s t \
            &->>_beta (lambda alpha : *. lambda u. tau_"mkleaf". lambda v : tau_"mknode". v p (s alpha u v) (t alpha u v)) \
            &->>_beta (lambda alpha : *. lambda u. tau_"mkleaf". lambda v : tau_"mknode" . v p (s alpha u v) (t alpha u v)) \
            &->>_beta lambda alpha : *. lambda u. tau_"mkleaf". lambda v : tau_"mknode" . v p S T \
        $
    ]
]

// MARK: Q. 3.19
#problem(source: "3.19")[
    If $Gamma tack L : sigma$, then $Gamma$ is a valid $lambda 2$ context.
]
#solution[
    The definition of "valid" here would be taken as relative to a judgement as the fact to be able to derive the judgement. Thus, it meant a complete inference path could be made using only statements and judgements derived from the context. Now proof by induction on inference rule that deducted $L : sigma$.
    #proof(prompt: "Case 1 : T-Var")[
        The premise is that $Gamma$ is a $lambda$2 context.
    ]
    #proof(prompt: "Case 2 : T-App")[
        Therefore $L equiv M N$ for some $M, N in Lambda_(TT 2)$. Therefore, $ Gamma tack M : tau -> sigma wide Gamma tack N : tau $  for some $tau in TT_2$. By the inductive hypothesis on any premise $Gamma$ is a valid $lambda$2 context.
    ]
    #proof(prompt: "Case 3 : T-Abst")[
        Therefore $L equiv lambda x : alpha. N$ such that
        $ Gamma, x : alpha tack N : beta $
        for some $alpha, beta in TT_2$ such that $sigma equiv alpha -> beta$. By the inductive hypothesis, $Gamma, x : alpha$. By the recursive definition of $lambda$2 contexts, for some valid context $Delta$, $forall n in "dom" Delta$, $n$ could not depende on statement declared after $n$ in the context. Therefore, no statement in $Gamma$ could depend on $x : alpha$. Therefore, $Gamma$ is a valid context.
    ]
    #proof(prompt: "Case 4 : T-Form")[
        The premise is that $Gamma$ is a valid $lambda$2 context.
    ]
    #proof(prompt: "Case 5 : T2-App")[
        Therefore $L equiv N B$ for some $N, B in VV_2$ such that
        $ Gamma tack N : Pi alpha : *. beta wide Gamma tack A : * $
        By the inductive hypothesis on the any premise $Gamma$ is a valid $lambda 2$ context.
    ]
    #proof(prompt: "Case 6 : T2-Abst")[
        Therefore $L equiv lambda alpha : *. M$ for some $M in Lambda_(TT 2)$ such that
        $ Gamma, alpha : * tack M : beta $
        and $sigma equiv Pi alpha : *. beta$. By reasoning in _Case 3_ no statement in the context could depend on any statement before the latter's declaration. Therefore no statement in $Gamma$ could depend on $alpha : *$, making it a valid context.
    ]
]