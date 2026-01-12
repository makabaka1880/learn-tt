#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/fletcher:0.5.8" as fl: *;
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
    title: "Exercises",
    subtitle: "Chapter 8",
    authors: (
        (name: "Sean Li", affiliation: "Redacted"),
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
#let defs = $gt.tri$
#let sorry = `sorry`

#definition[
    We use an informal definition of definitions in $lambda C$. Formal derivation rules will be given in chapter 9, where $lambda D$ will be more formally introduced.
]

// MARK: Q. 8.1
#let coprime = "coprime"
#problem(source: "8.1")[
    Let
    $
        Gamma equiv & ZZ : *_s, NN^+ : *_s \
               defs & p(m, n, u) := sorry : exists x,y : ZZ. (m x + n y = 1) \
               defs & coprime(m, n) := sorry : *_p \
               defs & q(m, n) := sorry : coprime(m, n) -> coprime(n, m) \
              equiv & n : NN^+, m : NN^+, u : coprime(m, n) \
    $
    Prove $exists x,y : ZZ. (n x + m y = 1)$ in $Gamma$.
]
#solution[
    #proof(ded-nat(arr: (
        (0, $q(m, n) : coprime(m, n) -> coprime(n, m)$, ""),
        (0, $q(m, n) u : coprime(n, m)$, ""),
        (0, $p(n, m, (q(m, n) u)) : exists x, y : ZZ. (n x + m y = 1)$, ""),
    )))
]

// MARK: Q. 8.2
#problem(source: "8.2")[
    Consider the following formal proof in analysis.
    #proof(ded-nat(arr: (
        (0, $V : *_s$, ""),
        (1, $u : V subset.eq RR$, ""),
        (2, $"bounded-from-above"(V, u) := exists y : R. forall x : RR, (x in V => x <= y) : *_p$, ""),
        (2, $s : RR$, ""),
        (3, $"upper-bound"(V, u, s) := forall x in RR. (x in V => x <= s) : *_p$, ""),
        (
            3,
            $
                & "least-upper-bound"(V, u, s) := "upper-bound"(V, u, s) and \
                & quad forall x : RR. (x < s => not "upper-bound"(V, u, x)) : *_p
            $,
            "",
        ),
        (2, $v : V != emptyset$, ""),
        (3, $w : "bounded-from-above"(V, u)$, ""),
        (4, $p_4(V, u, w v) := sorry : exists^1 s : RR. "least-upper-bound"(V, u, s)$, ""),
        (0, $S := {x : RR | exists n : RR. (n in NN and x = n / (n + 1))}$, ""),
        (0, $p_6 := sorry : S subset.eq RR$, ""),
        (0, $p_7 := sorry : "bounded-from-above"(S, p_6)$, ""),
        (0, $p_8 := sorry : "least-upper-bound"(S, p_7, 1)$, ""),
    )))
    Translate the proof into a more usual format. Note $exists^1$ denotes unique existence, that is, $ exists^1 n : alpha. P(n) := exists n : alpha. (P(n) and not (exists k : alpha. (P(k) and k != n))) $
    Which lines are formalized definitions? Which of them are formalized mathematical statements?

    Which constants have been introduced before the text and which are introduced within?

    Underline all instantiations of parameter lists and explain accurately what has been instantiated for what, and why that is correct.

]
#solution[
    What we want to prove is that 1 is the least upper bound of the set ${x : RR | exists n in RR, (n in NN and x = n / (n + 1))}$. (For shorter notation we use $S equiv {n / (n + 1) : n in NN}$)
    #proof[
        We first give formal definitions of a set being "bounded above".
        #definition[
            A set #super[(1)] $V subset.eq RR$ #super[(2)] being *bounded from above* #super([(3)]) means that there exists $y in RR$ such that for all $x in RR$, $x$ being an element of $V$ implies that $x <= y$.

            For $s in RR$ #super[(4)] to *be the upper bound of $V$* #super[(5)], it means that any real $x$ being an element of $V$ implies that $x <= s$.

            For $s in RR$ to be the *least upper bound of $V$* #super[(6)], it means that $s$ is a upper bound of $V$ and any real number $x in RR$ such that $x < s$ is not a upper bound of $V$.
        ]
        #corollary[
            Any non-empty set $V subset.eq RR$ bounded from above has one and only one least upper bound.
        ]
        Consider the set $S := {n / (n + 1) : n in NN}$ #super[(10)]. Because division is closed under $RR$ when $n + 1 != 0$, $S subset.eq RR$ #super[(11)]. By ..._proof omitted_..., $S$ is bounded from above #super[(12)], and by ..._proof omitted_... and the fact that $S$ is bounded from above, $1$ is the least upper bound for $S$ #super[(13)].
    ]
    Lines (3), (5), (6), and (10) are definitions; those introduce new notions and constants, and (9), (11), (12), and (13) all statements; those construct the proof for the goal and serve as intermediate steps in the main proof.

    The sets $V$ and $S$, proof $u : V subset.eq RR$, the element $s in RR$ are all defined in the proof. The sets $RR$ and $NN$, the proposition constructor $subset.eq$, the set constructor notation, real operations, and the set $emptyset$ are all defined out of the proof.

    #let inside = it => text(fill: blue, it)
    #let outside = it => text(fill: red, it)
    We use #inside[blue] for constants defined within the proof, and #outside[red] for proofs outside.
    #ded-nat(arr: (
        (0, $inside(V) : *_s$, ""),
        (1, $inside(u) : V outside(subset.eq) outside(RR)$, ""),
        (
            2,
            $inside("bounded-from-above")(V, u) := exists y : R. forall x : RR, (x outside(in) V outside(=>) x outside(<=) y) : *_p$,
            "",
        ),
        (2, $inside(s) : RR$, ""),
        (3, $inside("upper-bound")(V, u, s) := forall x in RR. (x in V => x <= s) : *_p$, ""),
        (
            3,
            $
                & inside("least-upper-bound")(V, u, s) := "upper-bound"underline((V, u, s)^(1)) and \
                & quad forall x : RR. (x < s => not "upper-bound" underline((V, u, x)^2)) : *_p
            $,
            "",
        ),
        (2, $inside(v) : V outside(!=) outside(emptyset)$, ""),
        (3, $inside(w) : "bounded-from-above"underline((V, u)^3)$, ""),
        (
            4,
            $inside(p_4)(V, u, w v) := sorry : outside(exists^1) s : RR. "least-upper-bound"underline((V, u, s)^4)$,
            "",
        ),
        (
            0,
            $inside(S) := outside(\{)x : RR outside(|) exists n : RR. (n in outside(NN) and x outside(=) n outside(\/) (n outside(+) 1))outside(\})$,
            "",
        ),
        (0, $inside(p_6) := sorry : S subset.eq RR$, ""),
        (0, $inside(p_7) := sorry : "bounded-from-above"underline((S, p_6)^5)$, ""),
        (0, $inside(p_8) := sorry : "least-upper-bound"underline((S, p_7, 1)^6)$, ""),
    ))
    In instantiation 1 on line 5, $(V, u, s)$ states the proposition that $s$ is an upper bound of $V$ in order to proof that $s$ is the least upper bound of $V$.

    In instantiation 2 on line 6, $(V, u, x)$ states that the proposition of $x$ being an upper bound of $V$, which eventual leads to contradiction. This proves that no such $x$ exists.

    In instantiation 3 on line 8, $(V, u)$ construct a proposition of $V$ being bounded from above.

    In instantiation 4 on line 9, $(V, u, s)$ constructed a proposition of $s$ being the least upper bound, which was introduced as the one and only one such element of $RR$ that satisfies this.

    In instantiation 5 on line 12, $(S, p_6)$ constructed a proposition that $S$ was bounded from above, and is proven by $p_7$.

    In instantiation 6 on line 13, $(S, p_7, 1)$ constructed a proposition that $S$ has $1$ as the least upper bound, and is proven by $p_8$.

    All of this is is correct because the types match: by the PAT paradigm it means that each evidence provided suffices to construct each next step of the proof.
]

#pagebreak()
// MARK: Q. 8.3
#problem(source: "8.3")[
    Consider the formal proof in 8.2. State the partial order representing the dependencies between the definitions given in this text.
]
#solution[
    Denote the set of definitions as $S$ and dependency as $<=$.

    The Hasse Diagram of $(S, <=)$ is

    #fl.diagram(
        node-stroke: 1pt,
        node((1, 2), [
            *bounded-from-above*
            $ exists y : RR. forall x : RR. x in V => x <= y : *_p $
        ]),
        node((0, 1), [
            *upper-bound*
            $ forall x in RR. x in V => x <= s : *_p $ ]),
        node((0, 2), [
            *least-upper-bound*
            $
                "upper-bound"(V, u, s) and \
                forall x : RR (x < s => not "upper-bound"(V, u, x)) : *_p
            $
        ]),
        node((1, 1), [$ p_4 \ sorry : exists^1 s : RR. "least-upper-bound"(V, u, s) $]),
        edge((0, 1), (0, 2), "->"),
        edge((1, 2), (1, 1), "->"),
        edge((0, 1), (1, 1), "->"),
        node((0, 4), $ S \ {n / (n + 1) | n in NN} : *_s $),
        node((0, 3), $ p_6 \ sorry : S subset.eq RR $),
        edge((0, 4), (0, 3), "->"),
        node((1, 3), $ p_7 \ sorry : "bounded-from-above"(S, p_6) $),
        edge((1, 2), (1, 3), "->"),
        edge((0, 4), (1, 3), bend: -15deg, "->"),
        edge((0, 3), (1, 3), "->"),
        node((.75, 5), $ p_8 \ sorry : "least-upper-bound"(S, p_7, 1) $),
        edge((0, 4), (.75, 5), bend: -20deg, "->"),
        edge((1, 3), (.75, 5), bend: 10deg, "->"),
    )
]

// MARK: Q. 8.4
#problem(source: "8.4")[
    Consider the following formal text in algebra.
    #ded-nat(arr: (
        (0, $S : *_s$, ""),
        (1, $op : S -> S -> S$, ""),
        (2, $"semigroup"(S, op) := forall x, y, z : S. (op x (op y z) = op (op x y) z) : *_p$, ""),
        (2, $u : "semigroup"(S, op)$, ""),
        (3, $e : S$, ""),
        (4, $"unit"(S, op, u, e) := forall x : S. (op x e = x and op e x = x) : *_p$, ""),
        (3, $"monoid"(S,op,u) := exists e : S. "unit"(S, op, u, e) : *_p$, ""),
        (3, $e_1, e_2 : S$, ""),
        (
            4,
            $
                & p_4 (S, op, u, e_1, e_2) := \
                & quad sorry : ("unit"(S, op, u, e_1) and "unit"(S, op, u, e_2)) => e_1 = e_2
            $,
            "",
        ),
    ))
    Translate this into a more usual format.

    Underline all variables that are bound to a binding variable introduced in the text.

    Rewrite definition of $"semigroup"$ and $"unit"$ using $Gamma defs a(...) := M : N$ format.
]
#solution[
    #definition[
        Let $S$ be a set #super[(1)] and $times$ a binary operation closed over $S$ #super[(2)].

        The tuple $chevron.l S, times chevron.r$ forms a *semigroup* #super[(3)] if $times$ is associative over $S$. That is, for any arbitrary elements $x, y, z in S$
        $ x times (y times z) = (x times y) times z $

        Let $u$ #super[(4)] be the semigroup $chevron.l S, times chevron.r$. The element $e in S$ #super[(5)] is called the *unit* #super[(6)] of $u$ if for any element $x in S$, we have
        $ x times e = x "and" e times x = x $

        A semigroup is called a *monoid* #super[(7)] if it has an unit.

        Let $e_1, e_2 in S$ #super[(8)]. If both of them are units of $u$, then $e_1 = e_2$, proof by $sorry$ #super[(9)].
    ]
    #let bm = it => text(fill: blue, it)
    #let rm = it => text(fill: red, it)
    #let gm = it => text(fill: green, it)
    #let ym = it => text(fill: rgb("#e19833"), it)
    #let pm = it => text(fill: purple, it)
    #let om = it => text(fill: orange, it)
    #let tm = it => text(fill: rgb("#19a6a8"), it)
    #let am = it => text(fill: rgb("#2638c3"), it)
    #let op = `op`
    #ded-nat(arr: (
        (0, $bm(S) : *_s$, ""),
        (1, $rm(op) : bm(underline(S)) -> bm(underline(S)) -> bm(underline(S))$, ""),
        (
            2,
            $tm("semigroup")(bm(underline(S)), rm(underline(op))) := forall x, y, z : bm(underline(S)). (rm(underline(op)) x (rm(underline(op)) y z) = rm(underline(op)) (rm(underline(op)) x y) z) : *_p$,
            "",
        ),
        (2, $gm(u) : tm(underline("semigroup"))(bm(underline(S)), rm(underline(op)))$, ""),
        (3, $ym(e) : bm(underline(S))$, ""),
        (
            4,
            $am("unit")(bm(underline(S)), rm(underline(op)), gm(underline(u)), ym(underline(e))) := forall x : bm(underline(S)). (rm(underline(op)) x ym(underline(e)) = x and rm(underline(op)) e x = x) : *_p$,
            "",
        ),
        (
            3,
            $"monoid"(bm(underline(S)),rm(underline(op)),gm(underline(u))) := exists ym(underline(e)) : bm(underline(S)). am(underline("unit"))(bm(underline(S)), rm(underline(op)), gm(underline(u)), ym(underline(e))) : *_p$,
            "",
        ),
        (3, $pm(e_1), om(e_2) : bm(underline(S))$, ""),
        (
            4,
            $
                & p_4 (bm(underline(S)), rm(underline(op)), gm(underline(u)), pm(underline(e_1)), om(underline(e_2))) := \
                & quad sorry : (am(underline("unit"))(bm(underline(S)), rm(underline(op)), gm(underline(u)), pm(underline(e_1))) and am(underline("unit"))(S, rm(underline(op)), gm(underline(u)), om(underline(e_2)))) => pm(underline(e_1)) = om(underline(e_2))
            $,
            "",
        ),
    ))

    The definitions could be rewritten as follows:
    $
        & S : *_s, op : S -> S -> S defs \
        & quad "semigroup"(S, op) := forall x, y, z : S. (op x (op y z)) = op (op x y) z \
        & S : *_s, op : S -> S -> S, u : "semigroup"(S, op), e : S defs \
        & quad "unit"(S, op, u, e) := forall x : S. (op x e = x and op e x = x)
    $
]

// MARK: Q. 8.5
#problem(source: "8.5")[
    Identify the definitions in the following text and rewrite the text in a formal format.

    #definition[
        The real number $r$ is *rational* if there exist integer numbers $p$ and nonzero $q$
        such that $r = p/q$.

        A real number that is not rational is called *irrational*. The set of all rational numbers is called $QQ$.

        Every natural number is rational. The number $0.75$ is rational, but $sqrt(2)$ is irrational.
    ]
    Use the set constructor notation ${x : RR | P x}$.
]
#solution[
    #ded-nat(arr: (
        (0, $r : RR$, ""),
        (1, $ "rational"(r) := exists p, q : ZZ. (q != 0 and r = p / q) : *_p $, ""),
        (1, $ "irrational"(r) := not "rational"(r) : *_p $, ""),
        (0, $QQ := {x : RR | "rational"(x)}$, ""),
        (0, $"all-nat-rational" := sorry : forall n : NN. "rational"(n)$, ""),
        (0, $"p75-rational" := sorry : "rational"(0.75)$, ""),
        (0, $"sqrt2-irrational" := sorry : "irrational"(sqrt(2))$, ""),
    ))
]

// MARK: Q. 8.6
#problem(source: "8.6")[
    Consider the following mathematical text from number theory:
    #definition[
        If $k$, $l$, and $m$ are integers, $m$ being positive, then one says that $k$ is *congruent* to $l$ modulo $m$ if $m$ divides $k - l$.

        We write $k equiv l (mod m)$ to indicate that $k$ is congruent to $l$ modulo $m$.

        Hence $-3 equiv 17 (mod 5)$, but not $-3 equiv -17 (mod 5)$.

        If $k equiv l (mod m)$, then also $l equiv k (mod m)$.

        $k equiv l (mod m)$ iff there is an integer $u$ s.t. $k = l + m u$.
    ]
    Formalize the definitions, indicate the scope of all variables and constants introduced in the text.

    Identify all instantiations in the formal text and check that the type conditions are respected.
]
#solution[
    Different variables have been colored the same, with the binders underlined. All instantiations have been underlined.
    #let bm = it => text(fill: blue, it)
    #let rm = it => text(fill: red, it)
    #let gm = it => text(fill: green, it)
    #let om = it => text(fill: orange, it)
    #let pm = it => text(fill: purple, it)
    #let tm = it => text(fill: rgb("#19a6a8"), it)
    #let am = it => text(fill: rgb("#2638c3"), it)
    #let ym = it => text(fill: rgb("#e19833"), it)
    #let km = it => text(fill: rgb("#ff38fc"), it)
    #ded-nat(arr: (
        (0, $underline(bm(k)), underline(rm(l)), underline(gm(m)) : ZZ$, ""),
        (1, $underline(om(h)) : gm(m) > 0$, ""),
        (2, $"congr-mod"(bm(k), rm(l), gm(m), om(h)) := gm(m) divides bm(k) - rm(l) : *_p$, ""),
        (0, $underline(pm(u)) := sorry : 5 > 0$, ""),
        (0, $p_1 := sorry : "congr-mod"underbrace((-3, 17, 5, pm(u)))$, ""),
        (0, $p_2 := sorry : not "congr-mod"underbrace((-3, -17, 5, pm(u)))$, ""),
        (0, $underline(tm(k)), underline(am(l)), underline(ym(m)) : ZZ$, ""),
        (1, $underline(km(h)) : ym(m) > 0$, ""),
        (
            2,
            $
                underline("congr-sym")(tm(k), am(l), ym(m), km(h)) := "congr-mod"underbrace((tm(k), am(l), ym(m), km(h))) => "congr-mod"underbrace((am(l), tm(k), ym(m), km(h))) : *_p
            $,
            "",
        ),
        (
            2,
            $
                underline("congr-exist")(tm(k), am(l), ym(m), km(h)) := "congr-mod"underbrace((tm(k), am(l), ym(m), km(h))) <=> exists u : ZZ. (tm(k) = am(l) + ym(m) u) : *_p
            $,
            "",
        ),
        (2, $h_"trans" := sorry : "congr-sym"underbrace((tm(k), am(l), ym(m), km(h)))$, ""),
        (2, $h_"exists" := sorry : "congr-exist"underbrace((tm(k), am(l), ym(m), km(h)))$, ""),
    ))
]
