#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/tdtr:0.4.2": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/commute:0.3.0": arr, commutative-diagram, node;

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
    subtitle: "Chapter 2",
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
            rule(name: "(T-Var)", $x : sigma in Gamma$, $Gamma tack x : sigma$),
        ),
        prooftree(
            rule(name: "(T-App)", $Gamma tack M : sigma -> tau$, $Gamma tack N : sigma$, $Gamma tack M N : tau$),
        ),
        prooftree(
            rule(name: "(T-Abst)", $Gamma, x : sigma tack M : tau$, $Gamma tack lambda x : sigma. M : sigma -> tau$),
        ),
    ))
    In this document, convention is that all type judgements in a proof tree, unless stated otherwise, is derived from a single context per tree.
]

// MARK: Q. 2.1
#problem(source: "2.1")[
    Type the following terms
    $ x x y quad x y y quad x y x quad x (x y) quad x (y x) $
]
#solution[
    The first term cannot be typed.
    #proof[
        $x x y$ = $(x x) y$. Therefore, $x$ is a function type, denote it as $tau -> sigma$. By the application rule, a subterm applied to $x$ must be of $tau$, which means that the application $x x$ is not legally typed.
    ]
    The second one is typable where $x:tau -> tau -> sigma$ and $y: tau$.

    #ded-nat(stcolor: black, arr: (
        (0, $x:tau -> tau -> sigma$, $tack.l Gamma$),
        (0, $y: tau$, $tack.l Gamma$),
        (0, $x y : tau -> sigma$, "1,2 T-App"),
        (0, $x y y : sigma$, "3,2 T-App"),
    ))

    The third term is not typable.
    #proof[
        Assume $x y x = (x y) x$ is typable. Therefore, $x: tau$ where $tau = sigma -> tau -> alpha$ and $y : sigma$. One can construct an infinite chain of function type by substituting $tau$: $tau = sigma -> (sigma -> (sigma -> ... -> alpha) -> alpha) -> alpha$. By induction, it can be proven that only lambda abstractions can construct function types, meaning that the term is of form
        $
            (lambda n: tau. lambda m: tau. ... (lambda a: sigma. lambda b:sigma. ...)) y (lambda n: tau. lambda m: tau. ... (lambda a: sigma. lambda b:sigma. ...))
        $
        meaning that an infinite reduction path is needed. This is impossible in STLC.
    ]

    The fourth type is typable where $x: (tau -> tau)$ and $y: tau$.


    #ded-nat(stcolor: black, arr: (
        (0, $x: tau -> tau$, $tack.l Gamma$),
        (0, $y: tau$, $tack.l Gamma$),
        (0, $x y : tau$, "1,2 T-App"),
        (0, $x (x y) : tau$, "1,3 T-App"),
    ))

    The fifth term is typable where $x : (tau -> sigma)$ and $y : (tau -> sigma) -> tau$:

    #ded-nat(stcolor: black, arr: (
        (0, $x : tau->sigma$, $tack.l Gamma$),
        (0, $y : (tau -> sigma) -> tau$, $tack.l Gamma$),
        (0, $y x : tau$, "2,1 T-App"),
        (0, $x (y x) : sigma$, "1,3 T-App"),
    ))
]

// MARK: Q. 2.2
#problem(source: "2.2")[
    Find types for $"zero"$, $"one"$, and $"two"$
]

#solution[
    Term for $"zero"$ is
    $ "zero" := lambda f x. x $
    Here $x$ is only used as a
    $ "zero" := lambda f : alpha. lambda x : beta. x $
    Type derivation shown as below:
    #ded-nat(stcolor: black, arr: (
        (0, $f : alpha$, "Bound"),
        (1, $x : beta$, "Bound"),
        (2, $x : beta$, "T-Var"),
        (1, $lambda x. x : beta -> beta$, "3 T-Abst"),
        (0, $lambda f: alpha. x: beta. x : alpha -> beta -> beta$, "4 T-Abst"),
    ))
    Term for $"one"$ is
    $ "one" := lambda f x. f x $
    Let $f$ be an arbitrary function type that consumes $x$
    $ "one" := lambda f : alpha -> beta. x : alpha. f x $
    Type derivation shown as below
    #ded-nat(stcolor: black, arr: (
        (0, $f : alpha -> beta$, "Bound"),
        (1, $x : alpha$, "Bound"),
        (2, $f : alpha -> beta$, "T-Var"),
        (2, $x : alpha$, "T-Var"),
        (2, $f x : beta$, "3,4 T-App"),
        (1, $lambda x. f x : alpha -> beta$, "5 T-Abst"),
        (0, $lambda f: alpha -> beta. x: alpha. f x : (alpha -> beta) -> alpha -> beta$, "6 T-Abst"),
    ))

    Same type signatures can be given to $"two"$
    $ "two" := lambda f : alpha -> beta. lambda x : alpha. f f x $
    Type derivation shown as below
    #ded-nat(stcolor: black, arr: (
        (0, $f: alpha -> beta$, "Bound"),
        (1, $x: alpha$, "Bound"),
        (2, $f: alpha -> beta$, "T-Var"),
        (2, $x: alpha$, "T-Var"),
        (2, $f x : beta$, "3,4 T-App"),
        (2, $f f x : beta$, "3,5 T-App"),
        (1, $lambda x. f f x : alpha -> beta$, "6 T-Abst"),
        (0, $lambda f: alpha -> beta. x: alpha. f f x : (alpha -> beta) -> alpha -> beta$, "7 T-Abst"),
    ))
]

// MARK: Q. 2.3
#problem(source: "2.3")[
    Find types for
    $
        K & := lambda x y. x \
        S & := lambda x y z. x z (y z)
    $
]

#solution[
    There are no occurences of application in $K$'s subterms. Therefore all its binding variables could be given a simple base type.
    $ K := lambda x: alpha. lambda y: beta. x $
    Type derivation shown as below
    #ded-nat(stcolor: black, arr: (
        (0, $x : alpha$, "Bound"),
        (1, $y : beta$, "Bound"),
        (2, $x : alpha$, "T-Var"),
        (1, $lambda y: beta. x: beta -> alpha$, "3 T-Abst"),
        (0, $lambda x: alpha. lambda y: beta. x : alpha -> beta -> alpha$, "4 T-Abst"),
    ))
    For the $S$ combinator, no term was applied to $z$. Therefore it can be given a simple base type $alpha$. As $z$ was applied to $y$, it implies that $y : alpha -> beta$ for some output type $beta$. As $x$ takes $z$ and $(y z)$, it must be of type $alpha -> beta -> delta$.

    $ S := lambda x : alpha -> beta -> delta . lambda y : alpha -> beta. lambda z . alpha. x z (y z) $

    Complete type derivation shown as below:

    #ded-nat(arr: (
        (0, $x : alpha -> beta -> delta$, "Bound"),
        (1, $y : alpha -> beta$, "Bound"),
        (2, $z : alpha$, "Bound"),
        (3, $y : alpha -> beta$, "T-Var"),
        (3, $z : alpha$, "T-Var"),
        (3, $y z : beta$, "4,5 T-App"),
        (3, $x : alpha -> beta -> delta$, "T-Var"),
        (3, $x z : beta -> delta$, "7,5 T-App"),
        (3, $x z (y z) : delta$, "8,6 T-App"),
        (2, $lambda z: alpha. x z (y z) : alpha -> delta$, "9 T-Abstr"),
        (
            1,
            $lambda y: alpha -> beta. lambda z. alpha . x z (y z) : (alpha -> beta) -> alpha -> delta$,
            "10 T-Abstr",
        ),
        (
            0,
            $
                lambda x: alpha -> beta -> delta. lambda y: alpha -> beta. lambda z \
                : alpha. x z (y z) : (alpha -> beta -> delta) -> (alpha -> beta) -> alpha -> delta
            $,
            "11 T-Abstr",
        ),
    ))
]

// MARK: Q. 2.4
#problem(source: "2.4")[
    Type the bound variables
    $
        lambda x y z. x (y z) \
        lambda x y z . y (x z) z
    $
]
#solution[
    For the first term, $z$	had nothing applied to it. Therefore it could be given a simple base type $alpha$. $z$ was applied to $y$, therefore $y: alpha -> beta$ to satisfy the application rule. Because the application yielded a type of $beta$, by the application rule $x : beta -> delta$ for some type $delta$.
    $ lambda x : beta -> delta. lambda y : alpha -> beta. lambda z : alpha. x (y z) $
    Complete type derivation shown below
    #ded-nat(arr: (
        (0, $x : beta -> delta$, "Bound"),
        (1, $y : alpha -> beta$, "Bound"),
        (2, $z : alpha$, "Bound"),
        (3, $y : alpha -> beta$, "T-Var"),
        (3, $z : alpha$, "T-Var"),
        (3, $y z : beta$, "4,5 T-App"),
        (3, $x : beta -> delta$, "T-Var"),
        (3, $x (y z) : delta$, "7,6 T-App"),
        (2, $lambda z: alpha. x (y z) : alpha -> delta$, "8 T-Abst"),
        (
            1,
            $ lambda y: alpha -> beta. lambda z: alpha. x (y z) : (alpha -> beta) -> alpha -> delta $,
            "9 T-Abst",
        ),
        (
            0,
            $
                lambda x: beta -> delta. lambda y: alpha -> beta. lambda z: alpha. x (y z) \ : (beta -> delta) -> (alpha -> beta) -> alpha -> delta
            $,
            "10 T-Abst",
        ),
    ))
    In the second term $z$ could still be given a simple base type $z : alpha$. Therefore $x : alpha -> beta$ for some type $beta$. $y$ takes $x z : beta$ and $z : alpha$, therefore it is of type $y : beta -> alpha -> delta$ for some $delta$.
    $ lambda x: alpha -> beta. lambda y: beta -> alpha -> delta. lambda z: alpha. y (x z) z $.
    Complete type derivation shown below
    #ded-nat(arr: (
        (0, $x : alpha -> beta$, "Bound"),
        (1, $y : beta -> alpha -> delta$, "Bound"),
        (2, $z : alpha$, "Bound"),
        (3, $x : alpha -> beta$, "T-Var"),
        (3, $z : alpha$, "T-Var"),
        (3, $x z : beta$, "4,5 T-App"),
        (3, $y : beta -> alpha -> delta$, "T-Var"),
        (3, $y (x z) : alpha -> delta$, "7,6 T-App"),
        (3, $y (x z) z : delta$, "8,5 T-App"),
        (2, $lambda z: alpha. y (x z) z : alpha -> delta$, "9 T-Abst"),
        (
            1,
            $lambda y: beta -> alpha -> delta. lambda z. y (x z) z : (beta -> alpha -> delta) -> alpha -> delta$,
            "10 T-Abst",
        ),
        (
            0,
            $
                lambda x : alpha -> beta. lambda y: beta -> alpha -> delta. lambda z. y (x z) z : \ (alpha -> beta) -> (beta -> alpha -> delta) -> alpha -> delta
            $,
            "11 T-Abst",
        ),
    ))
]

// MARK: Q. 2.5
#problem(source: "2.5")[
    Try to type the following terms, and prove if not typable.
    $
        lambda x y. x (lambda z. y) y \
        lambda x y. x (lambda z. x) y.
    $
]

#solution[
    The first term is trivially typable.
    #ded-nat(arr: (
        (0, $x : (delta -> alpha) -> alpha -> beta$, "Bound"),
        (1, $y : alpha$, "Bound"),
        (2, $x : (delta -> alpha) -> alpha -> beta$, "T-Var"),
        (2, $z : delta$, "Bound"),
        (3, $y : alpha$, "T-Var"),
        (2, $lambda z: delta. y : delta -> alpha$, "5 T-Abst"),
        (2, $x (lambda z: delta. y) : alpha -> beta$, "3,6 T-App"),
        (2, $y : alpha$, "T-Var"),
        (2, $x (lambda z: delta. y) y : beta$, "7,8 T-App"),
        (1, $lambda y: alpha. x (lambda z: delta. y) y : alpha -> beta$, "9 T-Abst"),
        (
            0,
            $
                lambda x : ((delta -> alpha) -> alpha -> beta) lambda y: alpha. x (lambda z: delta. y) y \ : ((delta -> alpha) -> alpha -> beta) -> alpha -> beta
            $,
            "10 T-Abst",
        ),
    ))
    The second term is not typable in STLC.
    #proof[
        By induction on the type inference rule that constructed the type judgement for subterm $x (lambda z. x)$. Because the term is an application, the only rule that applies is the application rule.

        We denote the context inside the abstraction as $Gamma'$.
        Suppose $cal(J) equiv Gamma' tack x (lambda z.x) : tau$. By the inference rule of application, $x$ must be a function type that accepts the type of $(lambda z. x)$. Let $Gamma' tack z:alpha$, and type of $x$ as $tau_x$. Therefore, $Gamma' tack lambda z:alpha . x : alpha -> tau_x$. Therefore, $tau_x = (alpha -> tau_x) -> tau$. This is a recursive type, which is not constructable as it requires infinitely nested lambda abstractions that requires infinite reduction paths to reach a normal form.
    ]
]

// MARK: Q. 2.6
#problem(source: "2.6")[
    Prove the pretyped term below is legal.
    $ lambda x: ((alpha -> beta) -> alpha). x (lambda z : alpha. y) $
    Using the tree format and the flag format.
]
#solution[
    We suppose a context $Gamma tack y : beta$ that obviously exists.
    #proof[
        #prooftree(
            rule(
                name: "(T-Abst)",
                rule(
                    name: "(T-App)",
                    rule(
                        name: "(Bound)",
                        $x : (alpha -> beta) -> alpha$,
                    ),
                    rule(
                        name: "(T-Abst)",
                        $Gamma, z : alpha tack y : beta$,
                        $Gamma tack (lambda z : alpha. y) : alpha -> beta$,
                    ),
                    $Gamma, x : (alpha -> beta) -> alpha tack (x (lambda z : alpha. y)) : alpha$,
                ),
                $Gamma tack lambda x : ((alpha -> beta) -> alpha). x (lambda z : alpha. y) : ((alpha -> beta) -> beta) -> alpha$,
            ),
        )
        A valid type could be given to the term. Therefore, the term is typable under an existing context.
    ]
    The flag derivation is given below:
    #ded-nat(arr: (
        (0, $x : (alpha -> beta) -> alpha$, "Bound"),
        (1, $z : alpha$, "Bound"),
        (2, $y : beta$, $tack.l Gamma$),
        (1, $(lambda z: alpha. y) : alpha -> beta$, "3 T-Abst"),
        (1, $x : (alpha -> beta) -> alpha$, "T-Var"),
        (1, $x (lambda z: alpha. y) : beta$, "5,4 T-App"),
        (
            0,
            $ lambda x : ((alpha -> beta) -> beta). x (lambda z: alpha. y) \ : (alpha -> beta) -> beta -> alpha $,
            "6 T-Abst",
        ),
    ))
]

// MARK: Q. 2.7 (a)
#problem(source: "2.7 a")[
    Derive $ f : A -> B and g : B -> C => g compose f : A -> C $
    Using the rules
    #align(center, rule-set(
        prooftree(
            rule(name: "(F-App)", $f: A -> B, x in A$, $f(x) in B$),
        ),
        prooftree(
            rule(name: "(F-Abst)", $forall x in A, f(x) in B$, $f: A -> B$),
        ),
    ))
]

#solution[
    #proof[
        #ded-nat(arr: (
            (0, $f : A -> B and g : B -> C$, "Assumption"),
            (1, $f : A -> B$, $1 and E$),
            (1, $g : B -> C$, $1 and E$),
            (1, $a in A$, ""),
            (2, $f(a) in B$, "3, 4 F-App"),
            (2, $g(f(a)) in C$, "5, 4 F-App"),
            (2, $(g compose f) (a) in C$, "6 Compose Def"),
            (1, $forall x in A, (g compose f) (x) in C$, $7 forall E$),
            (1, $g compose f : A -> C$, "8 F-Abst"),
            (0, $f: A -> B, g: B -> C => g compose f : A -> C$, $9 =>I$),
        ))
    ]
]

// MARK: Q. 2.7 (b)
#problem(source: "2.7 b")[
    Give a derivation in natural deduction of the following:
    $ (A => B) => ((B => C) => (A => C)) $
    Using the rules
    #align(center, rule-set(
        prooftree(
            rule(name: $(=> E)$, $A => B$, $A$, $B$),
        ),
        prooftree(
            rule(name: $(=> I)$, ded-nat(arr: ((0, $A$, "Premise"), (1, $...$, ""), (1, $B$, ""))), $A => B$),
        ),
    ))
]

#solution(proof[
    #ded-nat(arr: (
        (0, $A => B$, "Premise"),
        (1, $B => C$, "Premise"),
        (2, $A$, "Premise"),
        (3, $B$, $1, 3 => E$),
        (3, $C$, $2, 4 => E$),
        (2, $A => C$, $"3-5" => I$),
        (1, $(B => C) => (A => C)$, $"2-6" => I$),
        (0, $(A => B) => ((B => C) => (A => C))$, $"1-7" => I$),
    ))
])

// Q. 2.7 (c)
#problem(source: "2.7 c")[
    Prove the following pre-typed term is legal using flag notation
    $ lambda z : alpha. y (x z) $
]
#solution(proof[
    Let $Gamma tack x:alpha -> beta, y: beta -> delta$ for some type $beta$ and $delta$.
    #ded-nat(arr: (
        (0, $z : alpha$, "Bound"),
        (1, $x : alpha -> beta$, $tack.l Gamma$),
        (1, $z : alpha$, "T-Var"),
        (1, $x z : beta$, "2,3 T-App"),
        (1, $y : beta -> delta$, $tack.l Gamma$),
        (1, $y (x z) : delta$, "5,4 T-App"),
        (0, $lambda z: alpha. y (x z) : alpha -> delta$, "6 T-Abst"),
    ))
])

// Q. 2.7 (d)
#problem(source: "2.7 d")[
    State the similarity between Q. 2.7 (a), (b), and (c).
]
#solution[
    All of these examples requires proving something about composing two maps together as like this:

    #commutative-diagram(
        node((0, 0), $B$),
        node((1, 0), $A$),
        node((0, 1), $C$),
        arr($A$, $B$, $f$),
        arr($B$, $C$, $g$),
        arr($A$, $C$, $g compose f$),
    )
]

// MARK: Q. 2.8 (a)
#problem(source: "2.8 a")[
    Pre-type the bounding variables for the following term
    $ lambda x y. y (lambda z. y x) : (gamma -> beta) -> ((gamma -> beta) -> beta) -> beta $
]
#solution[
    $
        lambda x : (gamma -> beta) . y : ((gamma -> beta) -> beta). y (lambda z: gamma. y x)
    $
]

// MARK: Q. 2.8 (b)
#problem(source: "2.8 b")[Give a derivation in tree format]
#solution(prooftree(
    rule(
        name: "T-Abst",
        label: "(viii)",
        rule(
            name: "T-Abst",
            label: "(vii)",
            rule(
                name: "T-App",
                label: "(vi)",
                rule(
                    label: "(v)",
                    $y : ((gamma -> beta) -> beta)$,
                ),
                rule(
                    name: "T-Abst",
                    label: "(iv)",
                    rule(
                        name: "T-App",
                        label: "(iii)",
                        rule(
                            label: "(i)",
                            $x : (gamma -> beta)$,
                        ),
                        rule(
                            label: "(ii)",
                            $y : (gamma -> beta) -> beta$,
                        ),
                        $x : (gamma -> beta), y : ((gamma -> beta) -> beta), z : gamma tack y x : beta$,
                    ),
                    $x : (gamma -> beta), y : ((gamma -> beta) -> beta)tack lambda z : gamma . y x : gamma -> beta$,
                ),
                $x : (gamma -> beta), y : ((gamma -> beta) -> beta) tack y(lambda z. gamma. y x) : beta$,
            ),
            $x : (gamma -> beta) tack lambda y : ((gamma -> beta) -> beta). y(lambda z : gamma. y x) : ((gamma -> beta) -> beta) -> beta$,
        ),
        $
            (lambda x : (gamma -> beta) . y : ((gamma -> beta) -> beta). y (lambda z: gamma. y x))
            : (gamma -> beta) -> ((gamma -> beta) -> beta) -> beta
        $,
    ),
))

// MARK: Q. 2.8 (c)
#problem(source: "2.8 c")[Sketch a diagram of tree structure of derivation]
#solution("Trivial.")

// MARK: Q. 2.8 (d)
#problem(source: "2.8 d")[
    Transform the derivation into flag notation
]
#solution(ded-nat(arr: (
    ("", 0, $x : gamma -> beta$, "Bound"),
    ("", 1, $y : (gamma -> beta) -> beta$, "Bound"),
    ("", 2, $z : gamma$, "Bound"),
    ("(ii)", 3, $y : (gamma -> beta) -> beta$, "T-Var"),
    ("(i)", 3, $x : gamma -> beta$, "T-Var"),
    ("(iii)", 3, $y x : beta$, "4,5 T-App"),
    ("(iv)", 2, $lambda z : gamma. y x : gamma -> beta$, "6 T-Abst"),
    ("(v)", 2, $y : (gamma -> beta) -> beta$, "T-Var"),
    ("(vi)", 2, $y (lambda z : gamma. y x) : beta$, "8,7 T-App"),
    (
        "(vii)",
        1,
        $ lambda y : (gamma -> beta) -> beta. y (lambda z : gamma. y x) \ : ((gamma -> beta) -> beta) -> beta $,
        "9 T-Abst",
    ),
    (
        "(viii)",
        0,
        $
            lambda x: (gamma -> beta). lambda y : (gamma -> beta) -> beta. y (lambda z : gamma. y x) \ : (gamma -> beta) -> ((gamma -> beta) -> beta) -> beta
        $,
        "10 T-Abst",
    ),
)))

// MARK: Q. 2.9 (a)
#problem(source: "2.9 a")[
    Give derivations of the following judgement
    $
        x : delta -> delta -> alpha, y : gamma -> alpha, z: alpha -> beta tack \
        lambda u: delta. lambda v: gamma. z (y v) : delta -> gamma -> beta
    $
]
#solution(ded-nat(arr: (
    (0, $u : delta$, "Bound"),
    (1, $v : gamma$, "Bound"),
    (2, $y : gamma -> alpha$, "T-Var"),
    (2, $v : gamma$, "T-Var"),
    (2, $y v : alpha$, "3,4 T-App"),
    (2, $z : alpha -> beta$, "T-Var"),
    (2, $z (y v) : beta$, "6,5 T-App"),
    (1, $lambda v: gamma. z (y v) : gamma -> beta$, "7 T-Abst"),
    (1, $lambda u : delta. lambda v: gamma. z (y v) : delta -> gamma -> beta$, "8 T-Abst"),
)))

// MARK: Q. 2.9 (b)
#problem(source: "2.9 b")[
    Give derivations of the following judgement
    $
        x : delta -> delta -> alpha, y : gamma -> alpha, z: alpha -> beta tack \
        lambda u: delta. lambda v: gamma. z (x u u) : delta -> gamma -> beta
    $
]

#solution(ded-nat(arr: (
    (0, $u : delta$, "Bound"),
    (1, $v : gamma$, "Bound"),
    (2, $x : delta -> delta -> alpha$, "T-Var"),
    (2, $u : delta$, "T-Var"),
    (2, $x u : delta -> alpha$, "3,4 T-App"),
    (2, $x u u : alpha$, "5,4 T-App"),
    (2, $z : alpha -> beta$, "T-Var"),
    (2, $z (x u u) : beta$, "7,6 T-App"),
    (1, $lambda v : gamma. z (x u u) : gamma -> beta$, "8 T-Abst"),
    (1, $lambda u : delta. lambda v : gamma. z (x u u) : delta -> gamma -> beta$, "9 T-Abst"),
)))

// MARK: Q. 2.10 (a)
#problem(source: "2.10 a")[
    Give derivation for
    $
        x z (y z)
    $
]

#solution[
    Assume an context
    $
        Gamma & tack x : alpha -> beta -> gamma \
        Gamma & tack y : alpha -> beta \
        Gamma & tack z : alpha
    $
    #ded-nat(arr: (
        (0, $x : alpha -> beta -> gamma$, "T-Var"),
        (0, $y : alpha -> beta$, "T-Var"),
        (0, $z : alpha$, "T-Var"),
        (0, $x z : beta -> gamma$, "1,3 T-App"),
        (0, $y z : beta$, "2,3 T-App"),
        (0, $x z (y z) : gamma$, "4,5 T-App"),
    ))
]

// MARK: Q. 2.10 (b)
#problem(source: "2.10 b")[
    Give derivation for
    $ lambda x : (alpha -> beta) -> beta. x (y z) $
]

#solution[
    Assume an context
    $
        Gamma & tack y : gamma -> (alpha -> beta) \
        Gamma & tack z : gamma
    $
    #ded-nat(arr: (
        (0, $x : (alpha -> beta) -> beta$, "Bound"),
        (1, $x : (alpha -> beta) -> beta$, "T-Var"),
        (1, $y : gamma -> alpha -> beta$, "T-Var"),
        (1, $z : gamma$, "T-Var"),
        (1, $y z : alpha -> beta$, "3,4 T-App"),
        (1, $x (y z) : beta$, "2,5 T-App"),
        (0, $lambda x : (alpha -> beta) -> beta. x (y z) : ((alpha -> beta) -> beta) -> beta$, "6 T-Abst"),
    ))
]

// MARK: Q. 2.10 (c)
#problem(source: "2.10 c")[
    Give derivation for
    $ lambda y : alpha. lambda z : beta -> gamma. z (x y y) $
]

#solution[
    Assume a context
    $
        Gamma & tack x : alpha -> alpha -> beta
    $
    #ded-nat(arr: (
        (0, $y : alpha$, "Bound"),
        (1, $z : beta -> gamma$, "Bound"),
        (2, $z : beta -> gamma$, "T-Var"),
        (2, $x : alpha -> alpha -> beta$, "T-Var"),
        (2, $y : alpha$, "T-Var"),
        (2, $x y : alpha -> beta$, "4,5 T-App"),
        (2, $x y y : beta$, "6,5 T-App"),
        (2, $z (x y y) : gamma$, "3,6 T-App"),
        (1, $lambda z : beta -> gamma. z (x y y) : (beta -> gamma) -> gamma$, "8 T-Abst"),
        (0, $lambda y: alpha. lambda z : beta -> gamma. z (x y y) : alpha -> (beta -> gamma) -> gamma$, "8 T-Abst"),
    ))
]

// MARK: Q. 2.10 (d)
#problem(source: "2.10 d")[
    Give derivation for
    $ lambda x: alpha -> beta. y (x z) z $
]
#solution[
    Consider a context
    $
        Gamma & tack z : alpha \
        Gamma & tack y : beta -> alpha -> gamma
    $
    #ded-nat(arr: (
        (0, $x : alpha -> beta$, "Bound"),
        (1, $x : alpha -> beta$, "T-Var"),
        (1, $z: alpha$, "T-Var"),
        (1, $x z : beta$, "2,3 T-App"),
        (1, $y : beta -> alpha -> gamma$, "T-Var"),
        (1, $y (x z) : alpha -> gamma$, "5,4 T-App"),
        (1, $y (x z) z : gamma$, "3,5 T-App"),
        (0, $lambda x : alpha -> beta. y (x z) z : (alpha -> beta) -> gamma$, "7 T-Abst"),
    ))
]

// MARK: Q. 2.11 (a)
#problem(source: "2.11 a")[
    Find an inhabitant of type and prove through derivation
    $ (alpha -> alpha -> gamma) -> alpha -> beta -> gamma $
]

#solution[
    $ lambda x : (alpha -> alpha -> gamma). lambda y : (alpha). lambda z: (beta). x y y $
    #proof(ded-nat(arr: (
        (0, $x : alpha -> alpha -> gamma$, "Bound"),
        (1, $y : alpha$, "Bound"),
        (2, $z : beta$, "Bound"),
        (3, $x : alpha -> alpha -> gamma$, "T-Var"),
        (3, $y : alpha$, "Bound"),
        (3, $x y : alpha -> gamma$, "4,5 T-App"),
        (3, $x y y : gamma$, "6,5 T-App"),
        (2, $lambda z: beta. x y y : beta -> gamma$, "7 T-Abst"),
        (1, $lambda y: alpha. lambda z: beta. x y y : alpha -> beta -> gamma$, "8 T-Abst"),
        (
            0,
            $
                lambda x : alpha -> alpha -> gamma. lambda y: alpha. lambda z: beta. x y y \ : (alpha -> alpha -> gamma) -> alpha -> beta -> gamma
            $,
            "8 T-Abst",
        ),
    )))
]

// MARK: Q. 2.11 (b)
#problem(source: "2.11 b")[
    Find an inhabitant of type and prove through derivation
    $ ((alpha -> gamma) -> alpha) -> (alpha -> gamma) -> beta -> gamma $
]
#solution[
    $ lambda x : (alpha -> gamma) -> alpha. lambda y:(alpha -> gamma). lambda z : beta. y (x y) $
    #proof(ded-nat(arr: (
        (0, $x : (alpha -> gamma) -> alpha$, "Bound"),
        (1, $y : alpha -> gamma$, "Bound"),
        (2, $z : beta$, "Bound"),
        (3, $x : (alpha -> gamma) -> alpha$, "T-Var"),
        (3, $y : alpha -> gamma$, "T-Var"),
        (3, $x y : alpha$, "4,5 T-App"),
        (3, $y (x y) : gamma$, "5,6 T-App"),
        (2, $lambda z:beta. x (x y) : beta -> gamma$, "7 T-Abst"),
        (1, $lambda y : alpha -> gamma. lambda z:beta. x (x y) : (alpha -> gamma) -> beta -> gamma$, "7 T-Abst"),
        (
            0,
            $
                lambda x : (alpha -> gamma) -> alpha. lambda y : alpha -> gamma. lambda z : beta. x (x y) \ : ((alpha -> gamma) -> alpha) -> (alpha -> gamma) -> beta -> gamma
            $,
            "7 T-Abst",
        ),
    )))
]

// MARK: Q. 2.12 (a)
#problem(source: "2.12 a")[
    Construct a term of type
    $ ((alpha -> beta) -> alpha) -> (alpha -> alpha -> beta) -> alpha $
]
#solution[
    $
        lambda x : (alpha -> beta) -> alpha.
        lambda y : alpha -> alpha -> beta.
        x ( lambda z : alpha. y z z)
    $
    #proof(ded-nat(arr: (
        (0, $x : (alpha -> beta) -> alpha$, "Bound"),
        (1, $y : alpha -> alpha -> beta$, "Bound"),
        (2, $x : (alpha -> beta) -> alpha$, "T-Var"),
        (2, $z : alpha$, "Bound"),
        (3, $y : alpha -> alpha -> beta$, "T-Var"),
        (3, $z : alpha$, "Bound"),
        (3, $y z : alpha -> beta$, "5,6 T-App"),
        (3, $y z z : beta$, "7,6 T-App"),
        (2, $lambda z : alpha. y z z : alpha -> beta$, "8 T-Abst"),
        (2, $x (lambda z : alpha. y z z) : alpha$, "3,9 T-App"),
        (
            1,
            $lambda y : alpha -> alpha -> beta. x (lambda z : alpha. y z z) : (alpha -> alpha -> beta) -> alpha$,
            "3,9 T-App",
        ),
        (
            0,
            $
                lambda x : (alpha -> beta) -> alpha. lambda y : alpha -> alpha -> beta. x (lambda z : alpha. y z z) \
                : ((alpha -> beta) -> alpha) -> (alpha -> alpha -> beta) -> alpha
            $,
            "3,9 T-App",
        ),
    )))
]

// MARK: Q. 2.12 (b)
#problem(source: "2.12 b")[
    Construct a term of type
    $ ((alpha -> beta) -> alpha) -> (alpha -> alpha -> beta) -> beta $
]
#solution[
    $
        lambda x : (alpha -> beta) -> alpha.
        lambda y : alpha -> alpha -> beta.
        (lambda z : alpha. y z z) (x (lambda z : alpha. y z z))
    $
    #proof(ded-nat(arr: (
        (0, $x : (alpha -> beta) -> alpha$, "Bound"),
        (1, $y : alpha -> alpha -> beta$, "Bound"),
        (2, $x : (alpha -> beta) -> alpha$, "T-Var"),
        (2, $z : alpha$, "Bound"),
        (3, $y : alpha -> alpha -> beta$, "T-Var"),
        (3, $z : alpha$, "Bound"),
        (3, $y z : alpha -> beta$, "5,6 T-App"),
        (3, $y z z : beta$, "7,6 T-App"),
        (2, $"have" f := lambda z : alpha. y z z : alpha -> beta$, "8 T-Abst"),
        (2, $x f : alpha$, "3,9 T-App"),
        (2, $f (x f) : beta$, "9,10 T-App"),
        (1, $lambda y : alpha -> alpha -> beta. f (x f) : (alpha -> alpha -> beta) -> beta$, "9,10 T-App"),
        (
            1,
            $
                lambda x : (alpha -> beta) -> alpha. lambda y : alpha -> alpha -> beta. f (x f) \
                : (alpha -> beta) -> alpha -> (alpha -> alpha -> beta) -> beta
            $,
            "9,10 T-App",
        ),
    )))
]

// MARK: Q. 2.13 (a)
#problem(source: "2.13 a")[
    Find a term of type
    $ (alpha -> beta) -> alpha -> gamma $
    in context $Gamma$
    $ x : alpha -> beta -> gamma in Gamma $
]

#solution[
    $ lambda u : alpha -> beta. lambda v: alpha . x v (u v) $
    #proof(ded-nat(arr: (
        (0, $u : alpha -> beta$, "Bound"),
        (1, $v : alpha$, "Bound"),
        (2, $x : alpha -> beta -> gamma$, "T-Var"),
        (2, $v : alpha$, "T-Var"),
        (2, $x v : beta -> gamma$, "3,4 T-App"),
        (2, $u : alpha -> beta$, "T-Var"),
        (2, $u v : beta$, "6,4 T-App"),
        (2, $x v (u v) : gamma$, "5,7 T-App"),
        (1, $lambda v : alpha. x v (u v) : alpha -> gamma$, "8 T-Abst"),
        (0, $lambda u : alpha -> beta. lambda v : alpha. x v (u v) : (alpha -> beta) -> alpha -> gamma$, "9 T-Abst"),
    )))
]

// MARK: Q. 2.13 (b)
#problem(source: "2.13 b")[
    Find a term of type $ alpha -> (alpha -> beta) -> gamma $
    in context $Gamma$
    $ x : alpha -> beta -> alpha -> gamma in Gamma $
]

#solution[
    $ lambda u: alpha . lambda v : alpha -> beta. x u (v u) u $
    #proof(ded-nat(arr: (
        (0, $u : alpha$, "Bound"),
        (1, $v : alpha -> beta$, "Bound"),
        (2, $x : alpha -> beta -> alpha -> gamma$, "T-Var"),
        (2, $u : alpha$, "Bound"),
        (2, $v : alpha -> beta$, "Bound"),
        (2, $v u : beta$, "5,4 T-App"),
        (2, $x u : beta -> alpha -> gamma$, "3,4 T-App"),
        (2, $x u (v u) : alpha -> gamma$, "7,6 T-App"),
        (2, $x u (v u) u : gamma$, "8,4 T-App"),
        (1, $lambda v : alpha -> beta. x u (v u) u : (alpha -> beta) gamma$, "9 T-Abst"),
        (0, $lambda u : alpha. lambda v : alpha -> beta. x u (v u) u : alpha -> (alpha -> beta) gamma$, "10 T-Abst"),
    )))
]

// MARK: Q. 2.13 (c)
#problem(source: "2.13 c")[
    Find a term of type $ (alpha -> gamma) -> (beta -> alpha) -> gamma $
    in context $Gamma$
    $ x : (beta -> gamma) -> gamma in Gamma $
]

#solution[
    $ lambda u : alpha -> gamma. lambda v : beta -> alpha. x (lambda y : beta. u (v y)) $
	#proof(ded-nat(arr: (
		(0, $u : alpha -> gamma$, "Bound"),
		(1, $v : beta -> alpha$, "Bound"),
		(2, $x : (beta -> gamma) -> gamma$, "T-Var"),
		(2, $y : beta$, "Bound"),
		(3, $v : beta -> alpha$, "T-Var"),
		(3, $y : beta$, "T-Var"),
		(3, $v y : alpha$, "5,6 T-App"),
		(3, $u : alpha -> gamma$, "T-Var"),
		(3, $u (v y) : gamma$, "8,7 T-App"),
		(2, $lambda y : beta. u (v y) : beta -> gamma$, "9 T-Abst"),
		(2, $x (lambda y : beta. u (v y)) : gamma$, "10,3 T-App"),
		(1, $lambda v : beta -> alpha. x (lambda y : beta. u (v y)) : (beta -> alpha) -> gamma$, "11 T-Abst"),
		(0, $ lambda u : alpha -> gamma. lambda v : beta -> alpha. x (lambda y : beta. u (v y)) \ : (alpha -> gamma) -> (beta -> alpha) -> gamma $, "12 T-Abst"),
	)))
]
