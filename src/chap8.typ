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


// MARK: Q. 8.1
#let coprime = "coprime"
#problem(source: "Q 8.1")[
    Let
    $
        Gamma equiv & ZZ : *_s, NN^+ : *_s \
               defs & p(m, n, u) := sorry : exists x,y : ZZ. (m x + n y = 1) \
               defs & coprime(m, n) := sorry : *_p \
               defs & q(m, n) := sorry : coprime(m, n) -> coprime(n, s) \
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
#problem(source: "Q 8.2")[
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
    Translate the proof into a more usual format. Note $exists^1$ denotes unique existence, that is, $ exists^1 n : alpha. P(n) := exists n : alpha. (P(n) and not (exists k : alpha. (P(n) and k != n))) $
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

            For $s in RR$ to be the *least upper bound of $V$* #super[(6)], it means that $s$ is a upper bound of $V$ and any real number $x in RR$ such that $x <= s$ is not a upper bound of $V$.
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

    In instantiation 2 on line 6, $(V, u, x)$ states that the proposition of $x$ being an upper bound of $V$, which later on eventual leads to contradiction. This proves that no such $x$ required exists.

    In instantiation 3 on line 8, $(V, u)$ construct a proposition of $V$ being bounded from above.

    In instantiation 4 on line 9, $(V, u, s)$ constructed a proposition of $s$ being the least upper bound, which was introduced as the one and only one such element of $RR$ that satisfies this.

    In instantiation 5 on line 12, $(S, p_6)$ constructed a proposition that $S$ was bounded from above, and is proven by $p_7$.

    In instantiation 6 on line 13, $(S, p_7, 1)$ constructed a proposition that $S$ has $1$ as the least upper bound, and is proven by $p_8$.

    All of this is is correct because the types match: by the PAT paradigm it means that each evidence provided suffices to construct each next step of the proof.
]
