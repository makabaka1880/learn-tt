#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/tdtr:0.4.2": *
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
			rule(name: "(T-Abst)", $Gamma, x : sigma tack M : tau$, $Gamma tack lambda x : sigma. M : sigma -> tau$)
		)
    ))
	In this document, convention is that all type judgements in a proof tree, unless stated otherwise, is derived from a single context per tree.
]

// MARK: Q. 2.1
#problem[
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
        (0, $x (x y) : tau$, "1,3 T-App")
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
#problem[
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
#problem[
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
#problem[
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
            $ lambda x: beta -> delta. lambda y: alpha -> beta. lambda z: alpha. x (y z) \ : (beta -> delta) -> (alpha -> beta) -> alpha -> delta $,
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
            $ lambda x : alpha -> beta. lambda y: beta -> alpha -> delta. lambda z. y (x z) z : \ (alpha -> beta) -> (beta -> alpha -> delta) -> alpha -> delta $,
            "11 T-Abst",
        ),
    ))
]

// MARK: Q. 2.5
#problem[
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
#problem[
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
#problem[
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

#problem[
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

// MARK: Q. 2.7 (b)
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
