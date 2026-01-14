#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/fletcher:0.5.8" as fl: *;
#import "@preview/lovelace:0.3.0": *;
#import "@preview/tdtr:0.4.3": *;
#import "@preview/quick-maths:0.2.1": shorthands


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
    subtitle: "Chapter 9",
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

#show: shorthands.with(
    ($|-$, math.tack),
    ($|>$, defs), // Replaces '≤'
)

#definition[
    Extended Rules for $lambda D_0$
    #align(center, rule-set(
        prooftree(rule(
            name: "def",
            $Delta; Gamma |- K : L$,
            $Delta; overline(a) : overline(M) |- M : N$,
            $Delta, (overline(x) : overline(A) |> a(overline(x)) := M : N); Gamma |- K : L$,
        )),
        prooftree(rule(
            name: "inst",
            $Delta, cal(D); Gamma |- * : sort$,
            $Delta, cal(D); Gamma |- overline(U) : overline(A[overline(x) := overline(U)])$,
            $cal(D) equiv overline(x) : overline(A) |> a(overline(x)) := M : N$,
            $Delta, cal(D) ; Gamma |- a(overline(U)) : N[overline(x) := overline(U)]$,
        )),
        prooftree(rule(
            name: "conv",
            $Delta; Gamma |- x : A$,
            $Delta; Gamma |- A : s$,
            $A =^(Delta, beta) B$,
            $Delta; Gamma |- x : B$,
        )),
    ))
    #lemma[
        Given $cal(D) equiv overline(x) : overline(A) |> a(overline(x)) := M : N$ and $a in.not Delta$
        #align(center, prooftree(rule(
            name: "par",
            $Delta; overline(x) : overline(A) |- M : N$,
            $Delta, cal(D); overline(x) : overline(A) |- a(overline(x)) : N$,
        )))
    ]
]

// MARK: Q. 9.1
#problem(source: "9.1")[
    Given
    $
        (cal(D)_1) quad x : ZZ, y : ZZ quad |> & quad a(x, y) quad       && := x^2 + y^2           &&&  : ZZ \
        (cal(D)_2) quad x : ZZ, y : ZZ quad |> & quad b(x, y) quad       && := 2 dot (x dot y)     &&&  : ZZ \
        (cal(D)_3) quad x : ZZ, y : ZZ quad |> & quad c(x, y) quad       && := a(x, y) + b(x, y)   &&&  : ZZ \
        (cal(D)_4) quad x : ZZ, y : ZZ quad |> & quad "lemma"(x, y) quad && := c(x, y) = (x + y)^2 &&& : *_p \
    $
    Consider $Delta equiv cal(D)_1, cal(D)_2, cal(D)_3, cal(D)_4$. Describe the dependencies between the four definitions and give all possible linearizations of the corresponding partial order.
]
#solution[
    Hasse diagram given below

    #align(center, fl.diagram(
        node-stroke: 1pt,
        node((0, 0), [
            *$cal(D)_1$*
            $ a := x^2 + y^2 : ZZ $
        ]),
        node((2, 0), [
            *$cal(D)_2$*
            $ b := 2 dot (x dot y) : ZZ $
        ]),
        node((1, 0), [
            *$cal(D)_3$*
            $ c := a(x, y) + b(x, y) : ZZ $
        ]),
        node((1, 1), [
            *$cal(D)_4$*
            $ "lemma" := c(x, y) = (x + y)^2: *_p $
        ]),
        edge((2, 0), (1, 0), "->"),
        edge((0, 0), (1, 0), "->"),
        edge((1, 0), (1, 1), "->"),
    ))
    The only incomparable pair is $(cal(D)_1, cal(D_2))$. Therefore there are two possible linearizations:
    $
        (1) quad & cal(D)_1 <= cal(D)_2 <= cal(D)_3 <= cal(D)_4 \
        (2) quad & cal(D)_2 <= cal(D)_1 <= cal(D)_3 <= cal(D)_4
    $
]

// MARK: Q. 9.2
#problem(source: "9.2")[
    Consider
    $
        cal(D)_i equiv overline(x) : overline(A) & |> a(overline(x)) := K : L \
        cal(D)_j equiv overline(y) : overline(B) & |> b(overline(y)) := M : N \
    $
    Let $Delta; Gamma |- U : V$ and assume $cal(D)_i$ and $cal(D)_j$ are elements of list $Delta$, where $cal(D)_i$ precedes $cal(D)_j$. Describe precisesly where constant $a$ may occur in $cal(D)_i$ and $cal(D)_j$ and where constant $b$ may occur in $Delta$.
]
#solution[
    In order for $cal(D)_i$ to be a valid definition, $overline(x) : overline(A) |- K : L$ must be legal. Therefore by the free variable lemma any free variables in $K$ and $L$ must be in $overline(x) : overline(A)$, which by the time, does not yet contain $a$'s definition. Therefore, $a$ could only appear in $cal(D)_j$.

    By similar reasoning $b$ could only have appeared in definitions after $cal(D)_j$. Assuming the list sorted by the suffix, then $b$ could only have been in any $cal(D)_k$ where $k > j$.
]

// MARK: Q. 9.3
#problem(source: "9.3")[
    Recall Q 8.2
    #ded-nat(arr: (
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
        (0, $p_8 := sorry : "least-upper-bound"(S, p_6, 1)$, ""),
    ))
    Write $p_8$ out such that all definitions have been unfolded.
]
#solution[
    $
        p_8 := & "least-upper-bound"(S, p_6, 1) \
        =_delta & "upper-bound"(S, p_6, 1) and forall x : RR. (x < 1 => not "upper-bound"(S, p_6, 1)) \
        =_delta & forall x : RR. (x in S => x <= 1) and forall x : RR. (x < 1 => not (forall y : RR. (y in S => y <= x))) \
        =_delta & forall x : RR. (x in {x : RR | exists n : RR. (n in NN and x = n / (n + 1))} => x <= 1) and \
        & quad forall x : RR. (x < 1 => not forall y : RR. (y in {k : RR | exists n : RR. (n in NN and k = n / (n + 1))} => y <= x))
    $
]

// MARK: Q. 9.4
#problem(source: "9.4")[
    Recall $Delta equiv cal(D)_1, cal(D)_2, cal(D)_3, cal(D)_4$ from 9.1. Give a complete $delta$-reduction diagram for
    $ c(a(u, v), b(w, w)) $
]
#solution[
    Too long to contain. An algorithm for finding the graph is proposed as below:
    #pseudocode-list[
        + *Let* $V := emptyset : #raw("Set") "of type" cal(E)_(lambda D)$
        + *Let* $E := emptyset : #raw("Set") "of type" (cal(E)_(lambda D) times cal(E)_(lambda D) )$
        + *Define* _procedure_ $"reduce"(t : cal(E)_(lambda D), Delta : #raw("Env"))$ _do_
            + *If* $t in V$ *then* _terminate_
            + *Else*
                + *Set* $V := V union {t}$

                + *Loop* for each redex $r$ of $t$ _do_
                    + *Let* $r' := "outermost one-step" delta"-reduction of" r$
                    + *Let* $t' := t[r := r']$
                    + *Set* $E := E union {(t, t')}$
                    + *Execute* $"reduce"(t',Delta)$
                + *End* _loop_
            + *End* _if_
        + *End* _reduce_
        + *Main*
            + *Define* $Delta := cal(D)_1, cal(D)_2, cal(D)_3, cal(D)_4$
            + *Execute* $"reduce"(c(a(u,v), b(w, w)), Delta)$ _and discard result_
            + *Graph* $(V, E)$
            + *Terminates*
        + *End* _main_
    ]
]

// MARK: Q. 9.5
#problem(source: "9.5")[
    Check that all instantiations in the 8.2 proof is legal under _inst_ rule.
]
#solution[
    It is trivial that the first (well-formed context and enviroment) and third (definition existence) holds for all instantiations.

    The instantiation on line 6 $..."upper-bound"(V, u, s)...$ requires the following premises after expansion:
    $
        Delta; Gamma & |- V : (*_s [V := V, u := u, s := s] "which is" *_s)quad           && checkmark \
        Delta; Gamma & |- u : (V subset.eq RR [V := V, u := u, s := s] "which is" V) quad && checkmark \
        Delta; Gamma & |- s : (RR [V := V, u := u, s := s] "which is" RR) quad            && checkmark
    $
    The instantiation on line 6 $..."upper-bound"(V, u, x)...$ requires the following premises after expansion:
    $
        Delta; Gamma & |- V : (*_s [V := V, u := u, s := x] "which is" *_s)quad           && checkmark \
        Delta; Gamma & |- u : (V subset.eq RR [V := V, u := u, s := x] "which is" V) quad && checkmark \
        Delta; Gamma & |- x : (RR [V := V, u := u, s := x] "which is" RR) quad            && checkmark
    $
    The instantiation on line 8 $..."bounded-from-above"(V, u)...$ requires the following premises after expansion:
    $
        Delta; Gamma & |- V : (*_s [V := V, u := u] "which is" *_s) quad                       && checkmark \
        Delta; Gamma & |- u : (V subset.eq RR [V := V, u := u] "which is" V subset.eq RR) quad && checkmark \
    $
    The instantiation on line 9 $..."least-upper-bound"(V,u,s)...$ requires the following premises after expansion:
    $
        Delta; Gamma & |- V : (*_s [V := V, u := u, s := s] "which is" *_s) quad                         && checkmark \
        Delta; Gamma & |- u : ((V subset.eq RR) [V := V, u := u, s := s] "which is" V subset.eq RR) quad && checkmark \
        Delta; Gamma & |- s : (RR [V := V, u := u, s := s] "which is" RR) quad                           && checkmark \
    $
    The instantiation on line 12 $..."bounded-from-above"(S, p_6)...$  requires the following premises after expansion:
    $
        Delta; Gamma & |- S : (*_s [V := S, u := p_6] "which is" *_s) quad                           && checkmark \
        Delta; Gamma & |- p_6 : ((V subset.eq RR) [V := S, u := p_6] "which is" S subset.eq RR) quad && checkmark \
    $
    The instantiation on line 13 $..."least-upper-bound"(S, p_6, 1)...$ requires the following premises after expansion:
    $
        Delta; Gamma & |- S : (*_s [V := S, u := p_6, s := 1] "which is" *_s) quad                           && checkmark \
        Delta; Gamma & |- p_6 : ((V subset.eq RR) [V := S, u := p_6, s := 1] "which is" S subset.eq RR) quad && checkmark \
        Delta; Gamma & |- 1 : (RR [V := S, u := p_6; s := 1] "which is" RR) quad                             && checkmark
    $
    Therefore all of the instantiations are valid.
]
