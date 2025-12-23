#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/cetz:0.4.2" as cc: *;
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
#let operators = ($exists$.body, $lambda$.body, $forall$.body, $Pi$.body)
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

#definition(prompt: "Reference - Calculus of Constructions")[
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
    *The $lambda$-Cube*
    #grid(
        columns: 2,
        column-gutter: 1.25cm,
        cc.canvas({
            import cc.draw: *
            let s = 2.4
            content((0, 0, 0), $lambda ->$, name: "stlc", padding: 0.1)
            content((s, 0, 0), $lambda P$, name: "lp", padding: 0.1)
            content((0, s, 0), $lambda 2$, name: "l2", padding: 0.1)
            content((s, s, 0), $lambda "P2"$, name: "lp2", padding: 0.1)
            content((0, 0, s), $lambda underline(omega)$, name: "lwo", padding: 0.1)
            content((s, 0, s), $lambda P underline(omega)$, name: "lpo", padding: 0.1)
            content((0, s, s), $lambda omega$, name: "lo", padding: 0.1)
            content((s, s, s), $lambda C$, name: "cc", padding: 0.1)
            line("stlc", "lp")
            line("stlc", "lwo")
            line("stlc", "l2")
            line("cc", "lp2")
            line("cc", "lpo")
            line("cc", "lo")
            line("lwo", "lpo")
            line("lpo", "lp")
            line("lo", "lwo")
            line("lo", "l2")
            line("l2", "lp2")
            line("lp2", "lp")
        }),
        table(
            stroke: none,
            columns: (.5fr, .5fr, .5fr, .5fr, .5fr),
            row-gutter: -1.2mm,
            [*$lambda ->$*], $(*, *)$, $$, $$, $$,
            [*$lambda 2$*], $(*, *)$, $(sort, *)$, $$, $$,
            [*$lambda underline(omega)$*], $(*, *)$, $$, $(sort, sort)$, $$,
            [*$lambda P$*], $(*, *)$, $$, $$, $(*, sort)$,
            [*$lambda omega$*], $(*, *)$, $(sort, *)$, $(sort, sort)$, $$,
            [*$lambda "2P"$*], $(*, *)$, $(sort, *)$, $$, $(*, sort)$,
            [*$lambda "P" underline(omega)$*], $(*, *)$, $$, $(sort, sort)$, $(*, sort)$,
            [*$lambda C$*], $(*, *)$, $(sort, *)$, $(sort, sort)$, $(*, sort)$,
        ),
    )
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

// MARK: Q. 6.3 (a)
#problem(source: "6.3 a")[
    Let $cal(J)$ be a judgement
    $ cal(J) equiv S : *, P : S -> * tack lambda x : S. (P x -> bot) : S -> * $
    Derive $cal(J)$ in $lambda C$ with shorthand flag notation.
]
#solution[
    #ded-nat(arr: (
        (0, $S : *, P : S -> *$, ""),
        (1, $x : S$, ""),
        (2, $P x : *$, "1,2 App"),
        (2, $bot : *$, "Weak from 6.1 a"),
        (2, $P x -> bot : *$, "3,4 Form"),
        (1, $lambda x : S. P x -> bot : S -> *$, "5 Abst"),
    ))
]

// MARK: Q. 6.3 (b)
#problem(source: "6.3 b")[
    Deternmine the $(s_1, s_2)$ pairs corresponding to all $Pi$ abstractions occuring in $cal(J)$.
]
#solution[
    #table(
        columns: (.6fr, .4fr, .2fr),
        stroke: none,
        [*Abstraction*], [*Line Number*], [*$(s_1, s_2)$*],
        $P : S -> *$, [1], $(*, sort)$,
        $bot equiv Pi alpha : *. alpha$, [4], $(sort, *)$,
        $P x -> bot$, [5], $(sort, *)$,
        $lambda x : S. P x -> bot : S -> *$, [6], $(*, sort)$,
    )
]

// MARK: Q. 6.3 (c)
#problem(source: "6.3 c")[
    What is the 'smallest' system in the $lambda$-cube to which $cal(J)$ belongs?
]
#solution[
    There are  $(*, *)$ -- $lambda ->$ pairs, $(*, sort)$ -- $lambda P$ pairs, and $(sort, *)$ -- $lambda 2$. Therefore the minimal system $cal(J)$ belongs to is $lambda "P"2$.
]

// MARK: Q. 6.4 (a)
#problem(source: "6.4 a")[
    Let $Gamma equiv S : *, Q : S -> S -> *$ and
    $ M equiv (Pi x, y : S. (Q x y -> Q y x -> bot)) -> Pi z : S. (Q z z -> bot) $
    Derive $Gamma tack M : *$ and determine the smallest subsystemm to which this judgement belongs.
]
#pagebreak()
#solution[
    #ded-nat(arr: (
        (0, $S : *, Q : S -> S -> *$, ""),
        (1, $x : S$, ""),
        (2, $y : S$, ""),
        (3, $Q x : S -> *$, "1,2 App"),
        (3, $Q x y : *$, "4,3 App"),
        (3, $z : Q x y$, ""),
        (4, $Q y : S -> *$, "1,3 App"),
        (4, $Q y x : *$, "7,2 App"),
        (4, $t : Q y x$, ""),
        (5, $bot : *$, "Weak from 6.1 a"),
        (4, $Q y x -> bot : *$, "8,10 Form"),
        (3, $Q x y -> Q y x -> bot : *$, "5,11 Form"),
        (2, $Pi y : S. Q x y -> Q y x -> bot : *$, "1,12 Form"),
        (1, $Pi x,y : S. Q x y -> Q y x -> bot : *$, "1,13 Form"),
        (1, $a : (Pi x, y : S. (Q x y -> Q y x -> bot))$, ""),
        (2, $z : S$, ""),
        (3, $Q z : S -> *$, "1,16 App"),
        (3, $Q z z : *$, "17,16 App"),
        (3, $b : Q z z$, ""),
        (4, $bot : *$, "Weak from 6.1 a"),
        (3, $Q z z -> bot : *$, "18,20 Form"),
        (2, $Pi z : S. Q z z -> bot : *$, "1,21 Form"),
        (
            1,
            $
                & Pi x,y : S. (Q x y -> Q y x -> bot) \
                & quad -> Pi z : S. Q z z -> bot : *
            $,
            "14,22 Form",
        ),
    ))
    Here's a table of all $Pi$s that appeared
    #table(
        columns: (.7fr, .6fr, .2fr),
        stroke: gray.lighten(80%),
        [*Abstraction*], [*Line Number*], [*$(s_1, s_2)$*],
        $S -> *$, [1 / 4 / 7 / 17], $(*, sort)$,
        $S -> S -> *$, [1], $(*, sort)$,
        $bot$, [10 / 11 / 12 / 13 / 14 / 15 / 20 / 21 / 22 / 23], $(sort, *)$,
        $Q y x -> bot$, [11 / 12 / 13 / 14 / 15 / 23], $(*, *)$,
        $Q x y -> Q y x -> bot$, [12 / 13 / 14 / 15 / 23], $(*, *)$,
        $Pi y : S. Q x y -> Q y x -> bot$, [13 / 14 / 23], $(*, *)$,
        $Pi x,y : S. Q x y -> Q y x -> bot$, [14 / 23], $(*, *)$,
        $Q z z -> bot$, [21 / 22 / 23], $(*, *)$,
        $Pi z : S. Q z z -> bot$, [22 / 23], $(*, *)$,
        $
            & Pi x,y : S. Q x y -> Q y x -> bot -> \
            & quad Pi z : S. Q z z -> bot
        $,
        [23],
        $(*, *)$,
    )
    There are $(*, *)$ -- $lambda ->$ pairs, $(*, sort)$ -- $lambda P$ pairs, and $(sort, *)$ -- $lambda 2$ pairs. Therefore the mimimal system available is $lambda "P2"$.
]

// MARK: Q. 6.4 (b)
#problem(source: "6.4 b")[
    Prove in $lambda C$ that $M$ is inhabited in context $Gamma$.
]
#solution[
    A shorthand derivation is given below:
    #proof(ded-nat(arr: (
        (0, $S : *, Q : S -> S -> *$, ""),
        (1, $h : Pi x,y : S. (Q x y -> Q y x -> bot)$, ""),
        (2, $z : S$, ""),
        (3, $a : Q z z$, ""),
        (4, $alpha : *$, ""),
        (5, $h z : Pi y : S. (Q z y -> Q y z -> bot)$, "2,3 App"),
        (5, $h z z : Q z z -> Q z z -> bot$, "6,3 App"),
        (5, $h z z a : Q z z -> bot$, "7,4 App"),
        (5, $h z z a a : Pi alpha : *. alpha$, "8,4 App"),
        (5, $h z z a a alpha : alpha$, "9,5 App"),
        (4, $lambda alpha : *. h z z a a alpha : Pi alpha : *. alpha$, "10 Abst"),
        (3, $lambda a : Q z z lambda alpha : *. h z z a a alpha : Q z z -> bot$, "11 Abst"),
        (2, $lambda z : S. lambda a : Q z z lambda alpha : *. h z z a a alpha : Pi z : S. Q z z -> bot$, "12 Abst"),
        (
            1,
            $
                & lambda h : Pi x,y : S. (Q x y -> Q y x -> bot) \
                & quad lambda z : S. lambda a : Q z z lambda alpha : *. h z z a a alpha \
                & quad : Pi x,y : S. (Q x y -> Q y x -> bot) ->Pi z : S. Q z z -> bot
            $,
            "13 Abst",
        ),
    )))
]

// MARK: Q. 6.4 (c)
#problem(source: "6.4 c")[
    We may consier $Q$ to be a relation on set $S$. Moreover by PAT we may see $A -> bot$ as the negation $not A$ of prop $A$. How can $M$ then be interpreted by the PAT paradigm?
]
#solution[
    By a direct type-to-proposition translation we have
    $ M equiv forall x, y in S, (Q (x, y) => not Q(y, x)) => forall z in S, (not Q(z,z)) $
    It expresses the fact if $Q$ is asymmetric then it is irreflective.
]

// MARK: Q. 6.5 (a)
#problem(source: "5.6 a")[
    Let
    $ cal(J) equiv S : * tack lambda Q : S -> S -> *. lambda x : S. Q x x : (S -> S -> *) -> S -> * $
    Give a shorthand derivation of $cal(J)$ and determine the smallest subsystem to which $cal(J)$ belongs.
]
#solution[
    #ded-nat(arr: (
        (0, $S : *$, ""),
        (1, $Q : S -> S -> *$, ""),
        (2, $x : S$, ""),
        (3, $Q x : S -> *$, "2,3 App"),
        (3, $Q x x : *$, "4,3 App"),
        (2, $lambda x : S. Q x x : S -> *$, "5 Abst"),
        (1, $lambda Q : S -> S -> *. lambda x : S. Q x x : (S -> S -> *) -> S -> *$, "6 Abst"),
    ))

    #table(
        columns: (.7fr, .6fr, .2fr),
        stroke: gray.lighten(80%),
        [*Abstraction*], [*Line Number*], [*$(s_1, s_2)$*],
        $S -> *$, [2 / 4 / 6 / 7], $(*, sort)$,
        $S -> S -> *$, [2 / 7], $(*, sort)$,
        $(S -> S -> *) -> (S -> *)$, [7], $(sort, sort)$,
    )
    The judgement contains $(*, sort)$ -- $lambda P$ pairs and $(sort, sort)$ -- $lambda underline(omega)$ pairs. Therefore the minimal system $cal(J)$ belongs to is $lambda "P" underline(omega)$.
]

// MARK: Q. 6.5 (b)
#problem(source: "6.5 b")[
    In $cal(J)$ of 6.5 a, we may consider the variable $Q$ as expressing a relation on set $S$. How could you describe the subexpression $lambda x : S. Q x x$ in this settings? And what is then the interpretation of the judgement $cal(J)$?
]
#solution[
    By a informal translation, the term meant "Given a relation $Q$ over set $S$ and an arbitrary element of $S$, return whether if $Q(x, x)$ holds".
]

// MARK: Q. 6.6 (a), (b)
#problem(source: "6.6 a & b")[
    Let $ M equiv lambda S : *. lambda P : S -> *. lambda x : S. (P x -> bot) $
    Prove $M$ legal and determine its type.
    What is the smallest system in which the $lambda$-cube in which $M$ may occur?
]
#solution[
    #ded-nat(arr: (
        (0, $* : sort$, "Sort"),
        (0, $S : *$, ""),
        (1, $a : S$, ""),
        (2, $* : sort$, ""),
        (1, $S -> *: sort$, "2,3 Form"),
        (1, $P : S -> *$, ""),
        (2, $x : S$, ""),
        (3, $P x : *$, "6,7 App"),
        (3, $a : P x$, ""),
        (4, $bot : *$, "Weak from 6.1 a"),
        (3, $P x -> bot : *$, "8,10 Form"),
        (2, $lambda x : S. P x -> bot : S ->*$, "11,5 Abst"),
        (2, $S -> * : sort$, "5,5 Weak"),
        (1, $(S -> *) -> S -> *:sort$, "5,13 Form"),
        (1, $lambda P : S -> *.lambda x : S. P x -> bot : (S -> *) -> S -> *$, "12,5 Abst"),
        (0, $Pi S : *. (S -> *) -> S -> * : sort$, "1,14 Form"),
        (
            0,
            $
                & lambda S : *. lambda P : S -> *. lambda x : S. P x -> bot \
                & quad : Pi S : *. (S -> *) -> S -> *
            $,
            "15,16 Abst",
        ),
    ))
    #table(
        columns: (.7fr, .6fr, .2fr),
        stroke: gray.lighten(80%),
        [*Abstraction*], [*Line Number*], [*$(s_1, s_2)$*],
        $S -> *$, [5 / 12 / 13 / 14 / 15], $(*, sort)$,
        $bot equiv Pi alpha : *. alpha$, [10 / 11], $(sort, *)$,
        $P x -> bot$, [11 / 12], $(*, *)$,
        $(S -> *) -> S -> *$, [14 / 15], $(sort, *)$,
        $Pi S : *. (S -> *) -> S -> *$, [16 / 17], $(sort, *)$,
    )
    The derivation contains $(*, *)$ -- $lambda ->$ pairs, $(*, sort)$ -- $lambda P$ pairs, and $(sort, *)$ -- $lambda 2$ pairs. Therefore the minimal system in which $M$ is legal is $lambda "P2"$.
]

// MARK: Q. 6.6 (c)
#problem(source: "6.6 c")[
    How could you interpret the constructor $M$ from 6.6 a, if $A -> bot$ encodes $not A$?
]
#solution[
    Converting into mathematical function notation,
    $ M(S,P,x) = not P(x) "where" S in "set", P subset.eq S, x in S $
    $M$ constructs the negation of a predicate $P$ over a set $S$ applied to $x$, an element of $S$. An inhabitant of $M$ would prove the negation.
]

// MARK: Q. 6.7 (a)
#problem(source: "6.7 a")[
    Given
    $ Gamma equiv S : *, Q : S -> S -> * $
    We define under $Gamma$ terms
    $
        M_1 equiv & lambda x,y : S. Pi R : S -> S -> *. ((Pi z : S. R z z) -> R x y) \
        M_2 equiv & lambda x,y : S. Pi R : S -> S -> *. \
                  & quad ((Pi u,v : S. (Q u v -> R u v)) -> R x y)
    $
    Give an inhabitant of $Pi a : S. M_1 a a$ and a shorthand derivation proving your answer.
]
#solution[
    By $beta$-reduction
    $
                 & Pi a : S. M_1 a a \
           equiv & Pi a : S. (lambda x,y : S. Pi R : S -> S -> *. ((Pi z : S. R z z) -> R x y)) a a \
        ->>_beta & Pi a : S. Pi R : S -> S -> *. ((Pi z : S. R z z) -> R a a)
    $
    One such term
    $ M equiv lambda a : S. lambda R : S -> S -> *. (lambda h : (Pi z : S. R z z). h a ) $
    Is an inhabitant.
    #proof(ded-nat(arr: (
        (0, $S : *, Q : S -> S -> *$, ""),
        (1, $a : S$, ""),
        (2, $b : S$, ""),
        (3, $c : S$, ""),
        (4, $* : sort$, "Sort"),
        (3, $S -> * : sort$, "1,5 Form"),
        (2, $S -> S -> * : sort$, "1,6 Form"),
        (2, $R : S -> S -> *$, ""),
        (3, $z : S$, ""),
        (4, $R z : S -> *$, "8,9 App"),
        (4, $R z z : *$, "10,9 App"),
        (3, $Pi z : S. R z z : *$, "1,11 Form"),
        (3, $h : Pi z : S. R z z$, ""),
        (4, $R a : S -> *$, "8,2 App"),
        (4, $R a a : *$, "14,2 App"),
        (4, $h a : R a a$, "13,2 App"),
        (3, $Pi z : S. R z z -> R a a : *$, "12,15 Form"),
        (3, $lambda h : Pi z : S. R z z. h a : (Pi z : S. R z z) -> R a a$, "16,17 Abst"),
        (2, $Pi R : S -> S -> *.(Pi z : S. R z z) -> R a a : *$, "7,17 Form"),
        (
            2,
            $
                & lambda R : S -> S -> *.lambda h : Pi z : S. R z z. h a \
                & quad : Pi R : S -> S -> *.(Pi z : S. R z z) -> R a a
            $,
            "18,19 Abst",
        ),
        (1, $Pi a : S. Pi R : S -> S -> *.(Pi z : S. R z z) -> R a a : *$, "1,19 Form"),
        (
            1,
            $
                & lambda a : S. lambda R : S -> S -> *.lambda h : Pi z : S. R z z. h a \
                & quad : Pi a : S. Pi R : S -> S -> *.(Pi z : S. R z z) -> R a a
            $,
            "20,21 Abst",
        ),
    )))
]

// MARK: Q. 6.7 (b)
#problem(source: "6.7 b")[
    Under $Gamma$ of 6.7 a, give an inhabitant of $Pi a,b : S. (Q a b -> M_2 a b)$ and a shorthand derivation proving your answer.
]
#solution[
    By $beta$-reduction
    $
                 & Pi a,b : S. (Q a b -> M_2 a b) \
           equiv & Pi a,b : S. Q a b -> (lambda x,y : S. Pi R : S -> S -> *. \
                 & quad (Pi u,v : S. (Q u v -> R u v)) -> R x y) a b \
        ->>_beta & Pi a,b : S. Q a b -> (Pi R : S -> S -> *.
                       Pi u, v: S. (Q u v -> R u v) -> R a b)
    $
    One such term
    $
        M equiv & lambda a,b : S. lambda h : Q a b. lambda R : S -> S -> *. lambda r : (Pi u,v : S. Q u v -> R u v). \
                & quad r a b h
    $
    is an inhabitant.

    _Note:_ this proof would be too long with all formation rules included. For now, legality of abstraction types is assumed. Since we are omitting many lines, line labels are also removed from rule labels.
    #proof(ded-nat(arr: (
        (0, $S : *, Q : S -> S -> *$, ""),
        (1, $a : S$, ""),
        (2, $b : S$, ""),
        (3, $h : Q a b$, ""),
        (4, $R : S -> S -> *$, ""),
        (5, $r : Pi u,v : S. Q u v -> R u v$, ""),
        (6, $r a : Pi v : S. Q a v -> R a v$, "App"),
        (6, $r a b : Q a b -> R a b$, "App"),
        (6, $r a b h : R a b$, "App"),
        (
            5,
            $
                & lambda r : Pi u,v : S. Q u v -> R u v. r a b h \
                & quad : (Pi u,v : S. Q u v -> R u v) -> R a b
            $,
            "Abst",
        ),
        (
            4,
            $
                & lambda R : S -> S -> *. \
                & quad lambda r : Pi u,v : S. Q u v -> R u v. r a b h \
                & quad quad : Pi R : S -> S -> *. \
                & quad (Pi u,v : S. Q u v -> R u v) -> R a b
            $,
            "Abst",
        ),
        (
            3,
            $
                & lambda h : Q a b. lambda R : S -> S -> *. \
                & quad lambda r : Pi u,v : S. Q u v -> R u v. r a b h \
                & quad quad : Q a b -> Pi R : S -> S -> *. \
                & wide quad (Pi u,v : S. Q u v -> R u v) -> R a b
            $,
            "Abst",
        ),
        (
            2,
            $
                & lambda b : S. lambda h : Q a b. lambda R : S -> S -> *. \
                & quad lambda r : Pi u,v : S. Q u v -> R u v. r a b h \
                & quad quad : Pi b : S.Q a b -> Pi R : S -> S -> *. \
                & wide quad (Pi u,v : S. Q u v -> R u v) -> R a b
            $,
            "Abst",
        ),
        (
            1,
            $
                & lambda a,b : S. lambda h : Q a b. lambda R : S -> S -> *. \
                & quad lambda r : Pi u,v : S. Q u v -> R u v. r a b h \
                & quad quad : Pi a,b : S.Q a b -> Pi R : S -> S -> *. \
                & wide quad (Pi u,v : S. Q u v -> R u v) -> R a b
            $,
            "Abst",
        ),
    )))
]

// MARK: Q. 6.8 (a)
#problem(source: "6.8 a")[
    Let $Gamma equiv S : *, P : S -> *$. Find an inhabitant of
    $
        N equiv & [Pi alpha : *. ((Pi x : S. (P x -> alpha)) -> alpha)] -> \
                & quad [Pi x : S. (P x -> bot)] -> bot
    $
    Under $Gamma$ by means of a shortened derivation.
]
#solution[
    One such term
    $
        M equiv & lambda a : Pi alpha : *. ((Pi x : S. (P x -> alpha)) -> alpha) \
                & quad lambda b : Pi x :S. (P x -> bot). \
                & quad quad a bot b
    $
    is an inhabitant.
    #proof(ded-nat(arr: (
        (0, $S : *, P : S -> *$, ""),
        (1, $a : Pi alpha : *. ((Pi x : S. (P x -> alpha)) -> alpha)$, ""),
        (2, $b : Pi x : S. (P x -> bot)$, ""),
        (3, $a bot : (Pi x : S. P x -> bot) -> bot$, "App"),
        (3, $a bot b : bot$, "App"),
        (2, $lambda b : Pi x : S. (P x -> bot). a bot b : [Pi x : S. (P x -> bot)] -> bot$, "Abst"),
        (
            1,
            $
                & lambda a : Pi alpha : *. ((Pi x : S. (P x -> alpha)) -> alpha) \
                & quad lambda b : Pi x : S. (P x -> bot). a bot b : \
                & wide [Pi alpha : *. ((Pi x : S. (P x -> alpha)) -> alpha)] -> \
                & wide quad [Pi x : S. (P x -> bot)] -> bot
            $,
            "Abst",
        ),
    )))
]

// MARK: Q. 6.8 (b)
#problem(source: "6.8 b")[
    What is the smallest system in the $lambda$-cube in which the derivation in 6.8 a may be executed?
]
#solution[
    #table(
        columns: (.7fr, .2fr),
        stroke: gray.lighten(80%),
        [*Abstraction*], [*$(s_1, s_2)$*],
        $S -> *$, $(*, sort)$,
        $P x -> alpha$, $(*, *)$,
        $Pi x : S. (P x -> alpha)$, $(*, *)$,
        $(Pi x : S. (P x -> alpha)) -> alpha$, $(*, *)$,
        $Pi alpha : *. ((Pi x : S. (P x -> alpha)) -> alpha)$, $(sort, *)$,
        $P x -> bot$, $(*, *)$,
        $Pi x : S. (P x -> bot)$, $(*, *)$,
        $[Pi x : S. (P x -> bot)] -> bot$, $(*, *)$,
        $N$, $(*, *)$,
        $bot equiv Pi alpha : *. alpha$, $(sort, *)$,
    )
    The derivation contains $(*, *)$ -- $lambda ->$ pairs, $(*, sort)$ -- $lambda P$ pairs, and $(sort, *)$ -- $lambda 2$ pairs. Therefore the minimal system in which the derivation may be executed is $lambda "P2"$.
]

// MARK: Q. 6.8 (c)
#problem(source: "6.8 c")[
    The expression $Pi alpha : *.(Pi x :S. (P x -> alpha)) -> alpha$ maybe consider as an encoding of $exists x in S, P(x)$ under the PAT paradigm. With $A -> bot equiv not A$ in mind, how can we interpret the content of the expression $N$?
]
#solution[
    $ N equiv (exists x in S, P(x)) => not (forall x in S, not P(x)) $
]
