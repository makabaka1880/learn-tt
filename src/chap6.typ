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
#let operators = ($exists$.body, $lambda$.body, $forall$.body)
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
#let sort = $square$

#definition[
    Some rules for reference.

    *$lambda C$ Calculus Rules*
    #align(center, rule-set(
        prooftree(
            rule(
                name: "Sort",
                $emptyset tack * : sort$,
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
                $Gamma tack A : s_1$,
                $Gamma, x : A tack B : s_2$,
                $Gamma tack Pi x : A. B : s_2$,
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

// MARK: Q. 6.1 (a)
#problem(source: "6.1 a")[
    Give a complete derivation in tree format showing that
    $ bot equiv Pi alpha : *. alpha $
    is legal in $lambda C$.
]
#solution[
    Here we will show that there exists $s in "sort"$ and $Gamma$ such that $Gamma tack bot : s$.
    #proof(align(center, prooftree(
        rule(
            name: "Form",
            $tack * : sort$,
            rule(
                name: "Var",
                $tack * : sort$,
                $alpha : * tack alpha : *$,
            ),
            $tack Pi alpha : *. alpha : *$,
        ),
    )))
]

// MARK: Q. 6.1 (b)
#problem(source: "6.1 a")[
    Give a complete derivation in tree format showing that $bot -> bot$ is legal in $lambda C$ where
    $ bot equiv Pi alpha : *. alpha $
]
#solution[
    Here we will show that there exists $s in "sort"$ and $Gamma$ such that $Gamma tack bot -> bot : s$.
    #proof(align(center, prooftree(
        rule(
            name: "Form",
            rule(label: "(6.1 a)", $tack bot : *$),
            rule(
                name: "Weak",
                rule(label: "(6.1 a)", $tack bot : *$),
                rule(label: "(6.1 a)", $tack bot : *$),
                $x : bot tack bot : *$,
            ),
            $tack Pi x : bot. bot : *$,
        ),
    )))
]

// MARK: Q. 6.1 (c)
#problem(source: "6.1 c")[
    To which systems of the $lambda$-cube does $bot$ belong? And $bot -> bot$?
]
#solution[
    The set of $(s_1, s_2)$ pairs in formation rules of the derivation of $bot$ is ${(sort, *)}$. The minimal system corresponding is $lambda 2$. The same for $bot -> bot$. Therefore $bot$ and $bot -> bot$ belongs to $lambda 2$, $lambda omega$, $lambda P$ and $lambda C$.
]

// MARK: Q. 6.2
#problem(source: "6.2")[
    Given context $Gamma equiv S : *, P : S -> *, A : *$. Prove by means of a flag derivation that the following expression is inhabited in $lambda C$ with respect to $Gamma$:
    $ (Pi x : S. (A -> P x)) -> A -> Pi y : S. P y $
]

#solution[
    The inhabitant is
    $
        M equiv lambda u : (Pi x : S. (A -> P x)). lambda v : A. lambda y : S. u y v
    $
    #proof(ded-nat(arr: (
        (0, $S : *, P : S -> *, A : *$, ""),
        (1, $u : Pi x : S. (A -> P x)$, ""),
        (2, $v : A$, ""),
        (3, $y : S$, ""),
        (4, $u y : A -> P y$, "2,4 App"),
        (4, $u y v : P y$, "5,3 App"),
        (3, $lambda y : S. u y v : Pi y : S. P y$, "6 Abst"),
        (2, $lambda v : A.lambda y : S. u y v : A -> Pi y : S. P y$, "7 Abst"),
        (
            1,
            $
                & lambda u : Pi x : S. (A -> P x). lambda v : A.lambda y : S. u y v \
                & quad : Pi x : S. (A -> P x) -> A -> Pi y : S. P y
            $,
            "8 Abst",
        ),
    )))
]
