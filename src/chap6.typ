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
                $x in.not "dom" Gamma$,
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

// MARK: Q. 6.9
#problem(source: "6.9")[
    Given $S : *, P : S -> *$ and $f : S -> S$, we define in $lambda C$ the expression
    $ M equiv lambda x : S. Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q x $
    Give a term of type $Pi a : S. (M a -> M (f a))$ and a (shortened) derivation proving this.
]
#solution[
    By $beta$-reduction
    $
                & Pi a : S. (M a -> M (f a)) \
          equiv & Pi a : S. ((lambda x : S. Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q x) a -> M (f a)) \
        ->_beta & Pi a : S. (Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a -> M (f a)) \
          equiv & Pi a : S. (Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a \
                & quad -> (lambda x : S. Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q x) (f a)) \
        ->_beta & Pi a : S. (Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a) \
                & quad -> Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q (f a) \
    $
    One such term
    $
        M equiv & lambda a : S. lambda h : Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a. \
                & quad lambda Q : S -> *. lambda b : (Pi z : S. (Q z -> Q (f z))). \
                & wide b a (h Q b)
    $
    Is an inhabitant of the type above.
    #proof(ded-nat(arr: (
        (0, $S : *, P : S -> *, f : S -> S$, ""),
        (1, $a : S$, ""),
        (2, $h : Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a$, ""),
        (3, $Q : S -> *$, ""),
        (4, $b : Pi z : S. (Q z -> Q (f z))$, ""),
        (5, $h Q : (Pi z : S. (Q z -> Q (f z))) -> Q a$, "App"),
        (5, $h Q b : Q a$, "App"),
        (5, $b a : Q a -> Q (f a)$, "App"),
        (5, $b a (h Q b) : Q (f a)$, "App"),
        (
            4,
            $
                & lambda b : Pi z : S. (Q z -> Q (f z)). b a (h Q b) \
                & quad : (Pi z : S. (Q z -> Q (f z))) -> Q (f a)
            $,
            "Abst",
        ),
        (
            3,
            $
                & lambda Q : S -> *. lambda b : Pi z : S. (Q z -> Q (f z)). b a (h Q b) \
                & quad : Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q (f a)
            $,
            "Abst",
        ),
        (
            2,
            $
                & lambda h : Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a \
                & quad lambda Q : S -> *. lambda b : Pi z : S. (Q z -> Q (f z)). b a (h Q b) \
                & wide : (Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a) -> \
                & wide quad Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q (f a)
            $,
            "Abst",
        ),
        (
            1,
            $
                & lambda a : S. lambda h : Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a \
                & quad lambda Q : S -> *. lambda b : Pi z : S. (Q z -> Q (f z)). b a (h Q b) \
                & wide : Pi a : S. (Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q a) \
                & wide quad -> Pi Q : S -> *. (Pi z : S. (Q z -> Q (f z))) -> Q (f a)
            $,
            "Abst",
        ),
    )))
]

// MARK: Q. 6.10 (a)
#problem(source: "6.10 a")[
    Given $S : *$ and $P_1, P_2 : S -> *$, we define in $lambda C$ the expression
    $
        R equiv lambda x : S. Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x
    $
    We claim that $R$ codes the intersection of $P_1$ and $P_2$. In order to show this, give inhabitants of
    $
        (1) quad & Pi x : S. (P_1 x -> P_2 x -> R x) \
        (2) quad & Pi x : S. R x -> P_1 x \
        (3) quad & Pi x : S. R x -> P_2 x
    $
    Why do (a), (b), and (c) entail that $R$ is this intersection?
]
#solution[
    By $beta$-reduction
    $
        (1) equiv & Pi x : S. (P_1 x -> P_2 x -> R x) \
            equiv & Pi x : S (P_1 x -> P_2 x -> (lambda x : S. Pi Q : S -> *. \
                  & quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x) x) \
          ->^beta & Pi x : S (P_1 x -> P_2 x -> (Pi Q : S -> *. \
                  & quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x))
    $
    $
        (2) equiv & Pi x : S . R x -> P_1 x \
            equiv & Pi x : S.(lambda x : S. Pi Q : S -> *. \
                  & quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x) x -> P_1 x \
          ->_beta & Pi x : S.(Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x) -> P_1 x
    $
    $
        (3) equiv & Pi x : S . R x -> P_2 x \
            equiv & Pi x : S.(lambda x : S. Pi Q : S -> *. \
                  & quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x) x -> P_2 x \
          ->_beta & Pi x : S.(Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x) -> P_2 x
    $
    Terms
    $
         M_I equiv & lambda x : S. lambda a : P_1 x. lambda b : P_2 x. lambda Q : S -> *. \
                   & quad lambda h : Pi y : S. (P_1 y -> P_2 y -> Q y). \
                   & wide h x a b \
        pi_1 equiv & lambda x : S. lambda h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x. \
                   & quad h P_1 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. a) \
        pi_2 equiv & lambda x : S. lambda h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x. \
                   & quad h P_2 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. b) \
    $
    inhabits (1), (2) and (3) respectively.
    #proof(prompt: "Proof 1", ded-nat(arr: (
        (0, $S : *, P_1, P_2 : S -> *$, ""),
        (1, $x : S$, ""),
        (2, $a : P_1 x$, ""),
        (3, $b : P_2 x$, ""),
        (4, $Q : S -> *$, ""),
        (5, $h : Pi y : S. (P_1 y -> P_2 y -> Q y)$, ""),
        (6, $h x : P_1 x -> P_2 x -> Q x$, ""),
        (6, $h x a : P_2 x -> Q x$, ""),
        (6, $h x a b : Q x$, ""),
        (
            5,
            $
                & lambda h : Pi y : S. (P_1 y -> P_2 y -> Q y). h x a b \
                & quad : (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x
            $,
            "Abst",
        ),
        (
            4,
            $
                & lambda Q : S -> *. lambda h : Pi y : S. (P_1 y -> P_2 y -> Q y). h x a b \
                & quad : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x
            $,
            "Abst",
        ),
        (
            3,
            $
                & lambda b : P_2 x. lambda Q : S -> *. \
                & quad lambda h : Pi y : S. (P_1 y -> P_2 y -> Q y). h x a b \
                & wide : P_2 x -> Pi Q : S -> *. \
                & wide quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x
            $,
            "Abst",
        ),
        (
            2,
            $
                & lambda a : P_1 x. lambda b : P_2 x. lambda Q : S -> *. \
                & quad lambda h : Pi y : S. (P_1 y -> P_2 y -> Q y). h x a b \
                & wide : P_1 x -> P_2 x -> Pi Q : S -> *. \
                & wide quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x
            $,
            "Abst",
        ),
        (
            1,
            $
                & lambda x : S.lambda a : P_1 x. lambda b : P_2 x. lambda Q : S -> *. \
                & quad lambda h : Pi y : S. (P_1 y -> P_2 y -> Q y). h x a b \
                & wide : Pi x : S. P_1 x -> P_2 x -> Pi Q : S -> *. \
                & wide quad (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x
            $,
            "Abst",
        ),
    )))
    #proof(prompt: "Proof 2.", ded-nat(arr: (
        (0, $S : *, P_1, P_2 : S -> *$, ""),
        (1, $x : S$, ""),
        (2, $h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x$, ""),
        (3, $y : S$, ""),
        (4, $a : P_1 y$, ""),
        (5, $b : P_2 y$, ""),
        (6, $a : P_1 y$, "Weak"),
        (5, $lambda b : P_2 y. a : P_2 y -> P_1 y$, "Abst"),
        (4, $lambda a : P_1 y. lambda b : P_2 y. a : P_1 y -> P_2 y -> P_1 y$, "Abst"),
        (3, $lambda y : S.lambda a : P_1 y. lambda b : P_2 y. a : Pi y : S. P_1 y -> P_2 y -> P_1 y$, "Abst"),
        (3, $h P_1 : (Pi y : S. P_1 y -> P_2 y -> P_1 y) -> P_1 x$, "App"),
        (3, $h P_1 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. a) : P_1 x$, "App"),
        (
            2,
            $
                & lambda h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x \
                & quad h P_1 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. a) : \
                & wide (Pi Q : S -> *. (Pi y : S. \
                & wide quad (P_1 y -> P_2 y -> Q y)) -> Q x) -> P_1 x
            $,
            "Abst",
        ),
        (
            1,
            $
                & lambda x : S. lambda h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x \
                & quad h P_1 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. a) : \
                & wide Pi x : S. (Pi Q : S -> *. (Pi y : S. \
                & wide quad (P_1 y -> P_2 y -> Q y)) -> Q x) -> P_1 x
            $,
            "Abst",
        ),
    )))
    #proof(prompt: "Proof 3.", ded-nat(arr: (
        (0, $S : *, P_1, P_2 : S -> *$, ""),
        (1, $x : S$, ""),
        (2, $h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x$, ""),
        (3, $y : S$, ""),
        (4, $a : P_1 y$, ""),
        (5, $b : P_2 y$, ""),
        (6, $b : P_2 y$, "Weak"),
        (5, $lambda b : P_2 y. b : P_2 y -> P_2 y$, "Abst"),
        (4, $lambda a : P_1 y. lambda b : P_2 y. b : P_1 y -> P_2 y -> P_2 y$, "Abst"),
        (3, $lambda y : S.lambda a : P_1 y. lambda b : P_2 y. b : Pi y : S. P_1 y -> P_2 y -> P_2 y$, "Abst"),
        (3, $h P_2 : (Pi y : S. P_1 y -> P_2 y -> P_2 y) -> P_2 x$, "App"),
        (3, $h P_2 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. b) : P_2 x$, "App"),
        (
            2,
            $
                & lambda h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x \
                & quad h P_2 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. b) : \
                & wide (Pi Q : S -> *. (Pi y : S. \
                & wide quad (P_1 y -> P_2 y -> Q y)) -> Q x) -> P_2 x
            $,
            "Abst",
        ),
        (
            1,
            $
                & lambda x : S. lambda h : Pi Q : S -> *. (Pi y : S. (P_1 y -> P_2 y -> Q y)) -> Q x \
                & quad h P_2 (lambda y : S. lambda a : P_1 y. lambda b : P_2 y. b) : \
                & wide Pi x : S. (Pi Q : S -> *. (Pi y : S. \
                & wide quad (P_1 y -> P_2 y -> Q y)) -> Q x) -> P_2 x
            $,
            "Abst",
        ),
    )))
    The three terms correspond to the three rules of conjunction in predicate logic.
    $
         M_I & equiv forall x in S, P_1(x) => P_2(x) => P_1(x) and P_2(x) \
        pi_1 & equiv forall x in S, P_1(x) and P_2(x) => P_1(x) \
        pi_2 & equiv forall x in S, P_1(x) and P_2(x) => P_2(x)
    $
]

// MARK: Q. 6.11 (a)
#problem(source: "6.11 a")[
    Let $Gamma equiv x_1 : A_1, ... x_n : A_n$ in be a well-formed context in $lambda C$. Prove $x_1, ..., x_n$ distinct.
]
#solution[
    We prove by induction over $n$.
    #proof(prompt: "Base Case")[
        When $n = 1$, only one variable $x_1$ exists, which is trivially distinct.
    ]
    #proof(prompt: "Inductive Step")[
        Assume $x_1, ..., x_n$ are distinct. We show $x_(n+1)$ is distinct from all of them. By the Var rule:
        #align(center, prooftree(rule(
            name: "Var",
            rule(
                $...$,
                $x_1 : A_1, ..., x_n : A_n tack A_(n + 1) : s$,
            ),
            $x_(n + 1) in.not {x_1, x_2, ..., x_n }$,
            $x_1 : A_1, ..., x_n : A_n, x_(n + 1) : A_(n + 1) tack x_(n + 1) : A_(n + 1)$,
        )))
        The side condition of the Var rule requires $x_(n + 1) in.not "dom"(Gamma)$, i.e., $x_(n + 1) in.not {x_1, ..., x_n}$. Thus $x_1, ..., x_(n+1)$ are distinct.
    ]
    By the principle of mathematical induction, $x_1, ..., x_n$ are distinct for any $n$.
]

// MARK: Q. 6.11 (b)
#problem(source: "6.11 b")[
    Prove the Free Variables Lemma for $lambda C$.
]
#solution[
    #lemma[
        _Free Variables Lemma_.
        If $Gamma tack A : B$, then $"FV" A union "FV" B subset.eq "dom" Gamma$.
    ]
    We prove by structural induction over the inference rule that derived $Gamma tack A : B$.
    #proof(prompt: "Base Case - Sort Axiom")[
        $"FV" * union "FV" sort = emptyset subset.eq "dom" Gamma$.
    ]
    #proof(prompt: "Var Rule")[
        Then there exists $Gamma'$ and variable $x$ s.t. $Gamma', x : B equiv Gamma$. Therefore $"dom" Gamma' subset.eq "dom" Gamma$. The inference rule is
        #align(center, prooftree(rule(
            $Gamma' tack B : s$,
            $x in.not "dom" Gamma'$,
            $Gamma', x : B tack x : B$,
        )))
        By the inductive hypothesis on the first premise, $"FV" B subset.eq "dom" Gamma'$, thus $"FV" B subset.eq "dom" Gamma$ since $"dom" Gamma' subset.eq "dom" Gamma$. Since $A equiv x$ and $x in "dom" Gamma$ by construction, we have $"FV" A = {x} subset.eq "dom" Gamma$. Therefore $"FV" A union "FV" B subset.eq "dom" Gamma$.
    ]
    #proof(prompt: "Weak Rule")[
        Then there exists $Gamma'$ s.t. $Gamma', x : C equiv Gamma$ for some $C$ legal under $Gamma'$. The rule is
        #align(center, prooftree(rule(
            $Gamma' tack A : B$,
            $Gamma' tack C : s$,
            $Gamma', x : C tack A : B$,
        )))
        By the inductive hypothesis, $"FV" A union "FV" B subset.eq "dom" Gamma'$. Since $"dom" Gamma' subset.eq "dom" Gamma$, we have $"FV" A union "FV" B subset.eq "dom" Gamma$.
    ]
    #proof(prompt: "Form Rule")[
        Then $A equiv Pi x : C. D$ and $B equiv s_2$ for some sort $s_2$. The rule is
        #align(center, prooftree(rule(
            $Gamma tack C : s_1$,
            $Gamma, x : C tack D : s_2$,
            $Gamma tack Pi x : C. D : s_2$,
        )))
        Since $B$ is a sort, $"FV" B = emptyset$. By the definition of FV, $"FV" A = "FV" C union ("FV" D \\ {x})$.

        By the inductive hypothesis on the first premise, $"FV" C subset.eq "dom" Gamma$. By the inductive hypothesis on the second premise, $"FV" D subset.eq "dom" (Gamma, x : C) = "dom" Gamma union {x}$. Thus $"FV" D \\ {x} subset.eq "dom" Gamma$.

        Therefore $"FV" A = "FV" C union ("FV" D \\ {x}) subset.eq "dom" Gamma$, and $"FV" A union "FV" B subset.eq "dom" Gamma$.
    ]
    #proof(prompt: "App Rule")[
        Then $A equiv M N$ and $B equiv D[x := N]$. The rule is
        #align(center, prooftree(rule(
            $Gamma tack M : Pi x : C. D$,
            $Gamma tack N : C$,
            $Gamma tack M N : D[x := N]$,
        )))
        By definition, $"FV" A = "FV" M union "FV" N$ and $"FV" B = "FV" D[x := N] subset.eq ("FV" D \\ {x}) union "FV" N$.

        By the inductive hypothesis on the first premise, $"FV" M union "FV" (Pi x : C. D) subset.eq "dom" Gamma$. Since $"FV" (Pi x : C. D) = "FV" C union ("FV" D \\ {x})$, we have $"FV" D \\ {x} subset.eq "dom" Gamma$.

        By the inductive hypothesis on the second premise, $"FV" N subset.eq "dom" Gamma$.

        Therefore $"FV" A union "FV" B subset.eq "FV" M union "FV" N union ("FV" D \\ {x}) subset.eq "dom" Gamma$.
    ]
    #proof(prompt: "Abst Rule")[
        Then $A equiv lambda x : C. M$ and $B equiv Pi x : C. D$. The rule is
        #align(center, prooftree(rule(
            $Gamma, x : C tack M : D$,
            $Gamma tack Pi x : C. D : s$,
            $Gamma tack lambda x : C. M : Pi x : C. D$,
        )))
        By definition, $"FV" A = "FV" C union ("FV" M \\ {x})$ and $"FV" B = "FV" C union ("FV" D \\ {x})$.

        By the inductive hypothesis on the first premise, $"FV" M union "FV" D subset.eq "dom" (Gamma, x : C) = "dom" Gamma union {x}$. Thus $"FV" M \\ {x} subset.eq "dom" Gamma$ and $"FV" D \\ {x} subset.eq "dom" Gamma$.

        By the inductive hypothesis on the second premise, $"FV" (Pi x : C. D) subset.eq "dom" Gamma$, so $"FV" C subset.eq "dom" Gamma$.

        Therefore $"FV" A union "FV" B = "FV" C union ("FV" M \\ {x}) union ("FV" D \\ {x}) subset.eq "dom" Gamma$.
    ]
    #proof(prompt: "Conv Rule")[
        Then $B =_beta B'$ for some $B'$. The rule is
        #align(center, prooftree(rule(
            $Gamma tack A : B'$,
            $Gamma tack B : s$,
            $B =_beta B'$,
            $Gamma tack A : B$,
        )))
        By the inductive hypothesis on the first premise, $"FV" A subset.eq "dom" Gamma$. By the inductive hypothesis on the second premise, $"FV" B subset.eq "dom" Gamma$. Therefore $"FV" A union "FV" B subset.eq "dom" Gamma$.
    ]
    By the principle of structural induction, for any derivation of $Gamma tack A : B$, we have $"FV" A union "FV" B subset.eq "dom" Gamma$.
]

// MARK: Q. 6.11 (c)
#problem(source: "6.11 c")[
    Take $Gamma equiv x_1 : A_1 , ..., x_n : A_n$ from 6.11 a. Prove
    $ forall i < n, "FV" A_i subset.eq {x_j : 1 <= j <= n} $
]
#solution[
    We first need a lemma $ "dom" Gamma = {x_i : 1 <= i <= n} $
    Proof by induction on $n$.
    #proof(prompt: "Base Case")[Only declaration in $Gamma$, trivial.]
    #proof(prompt: "Inductive Step")[
        We assume a $Gamma' equiv Gamma, x_(n + 1) : A_(n + 1)$. Then
        $
            "dom" Gamma' & equiv "dom" Gamma union {x_(n + 1)} \
                         & equiv {x_1, ..., x_n} union {x_(n + 1)} & equiv {x_i : 1 <= i <= n + 1}
        $
    ]
    #proof(prompt: "Main Proof")[
        Let $Gamma' equiv x_1 : A_1, ..., x_(i-1) : A_(i-1)$ be the prefix of $Gamma$ before the $i$-th declaration. By the Var rule, for $x_i : A_i$ to extend $Gamma'$, we require $Gamma' tack A_i : s$ for some sort $s$.

        By the Free Variables Lemma (6.11 b), $"FV" A_i subset.eq "dom" Gamma'$. By the lemma above, $"dom" Gamma' = {x_1, ..., x_(i-1)}$.

        Therefore $"FV" A_i subset.eq {x_1, ..., x_(i-1)} subset.eq {x_j : 1 <= j <= n}$.
    ]
]
