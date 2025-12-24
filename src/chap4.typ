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
    subtitle: "Chapter 4",
    authors: (
        (name: "Sean Li", affiliation: "Redacted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)
#let nat = $mono("nat")$
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
};
#let symbol = $x$.body.func()
#show math.equation: it => {
    show symbol: set-symbol
    it
}
#let lwo = $lambda underline(omega)$
#let kind = $square$

#definition[
    Some rules for reference.
    #align(center, rule-set(
        prooftree(
            rule(
                name: "Sort",
                $emptyset tack * : kind$,
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
                $x in.not "dom" Gamma$,
                $Gamma, x : C tack A : B$,
            ),
        ),
        prooftree(
            rule(
                name: "Form",
                $Gamma tack A : s$,
                $Gamma tack B : s$,
                $Gamma tack A -> B : s$,
            ),
        ),
        prooftree(
            rule(
                name: "App",
                $Gamma tack M : A -> B$,
                $Gamma tack N : A$,
                $Gamma tack M N : B$,
            ),
        ),
        prooftree(
            rule(
                name: "Abst",
                $Gamma, x : A tack M : B$,
                $Gamma tack A -> B : s$,
                $Gamma tack lambda x : A. M : A -> B$,
            ),
        ),
        prooftree(
            rule(
                name: "Conv",
                $Gamma tack A : B$,
                $Gamma tack B' : s$,
                $B =^beta B'$,
                $Gamma tack A : B'$,
            ),
        ),
    ))
    Previously an alternative version of the flag derivation was used, only putting up a flag for a local premise (abstraction unwrapping) to save horizontal space. Currently, the standard flag derivation format will be used since now single lines will not be as long.
]
#pagebreak()


// MARK: Q. 4.1
#problem(source: "4.1")[
    Give a complete tree diagram of the derivation in section 4.5 (95)
]
#solution[

    #tidy-tree-graph[
        - conclusion (from O-App) (15)
            - abst (14)
                - form (13)
                    - weak (10) from sort (1)
                    - weak (10) from sort (1)
                - form (12)
                    - var (11)
                        - weak (10) from sort (1)
                    - var (11)
                        - weak (10) from sort (1)
            - var (15)
    ]
]

// MARK: Q. 4.2 (a)
#problem(source: "4.2 a")[
    Give a complete #lwo derivation in flag format of
    $ emptyset tack (* -> *) -> * : kind $
]
#solution[
    #ded-nat(arr: (
        (0, $* : kind$, "Sort"),
        (0, $* -> * : kind$, "1,1 Form"),
        (0, $(* -> *) -> * : kind$, "2,1 Form"),
    ))
]

// MARK: Q. 4.2 (b)
#problem(source: "4.2 b")[
    Give a complete #lwo derivation in flag format of
    $ alpha : *, beta : * tack (alpha -> beta) -> alpha : * $
]
#pagebreak()
#solution[
    #ded-nat(arr: (
        (0, $emptyset tack * : kind$, "Sort"),
        (0, $alpha : *$, ""),
        (1, $alpha : *$, "1 Var"),
        (1, $* : kind$, "1,1 Weak"),
        (1, $beta : *$, ""),
        (2, $alpha : *$, "3,4 Weak"),
        (2, $beta : *$, "4 Var"),
        (2, $alpha -> beta : *$, "6,7 Form"),
        (2, $(alpha -> beta) -> alpha : *$, "8,6 Form"),
    ))
]

// MARK: Q. 4.3 (a)
#problem(source: "4.3 a")[
    Give a complete #lwo derivation in flag format of
    $ alpha, beta : *, x : alpha, y : alpha -> beta tack y x : beta $
]
#solution[
    #ded-nat(arr: (
        (0, $* : kind$, "Sort"),
        (0, $alpha : *$, ""),
        (1, $alpha : *$, "1 Var"),
        (1, $* : kind$, "1,1 Weak"),
        (1, $beta : *$, ""),
        (2, $beta : *$, "4 Var"),
        (2, $alpha : *$, "3,4 Weak"),
        (2, $* : kind$, "4,4 Weak"),
        (2, $x : alpha$, ""),
        (3, $x : alpha$, "7 Var"),
        (3, $alpha : *$, "7,7 Weak"),
        (3, $beta : *$, "6,7 Weak"),
        (3, $alpha -> beta : *$, "11,12 Form"),
        (3, $y : alpha -> beta$, ""),
        (4, $y : alpha -> beta$, "13 Var"),
        (4, $x : alpha$, "10,13 Weak"),
        (4, $y x : beta$, "15,16 App"),
    ))
]

// MARK: Q. 4.3 (b)
#problem(source: "4.3 b")[
    Give a shortened #lwo derivation in flag format of
    $ alpha, beta : *, x : alpha, y : alpha -> beta, z : beta -> alpha tack z (y x) : alpha $
]
#solution[
    #ded-nat(arr: (
        (0, $alpha : *$, ""),
        (1, $beta : *$, ""),
        (2, $x : alpha$, ""),
        (3, $y : alpha -> beta$, ""),
        (4, $x : alpha$, "3 Weak"),
        (4, $z : beta -> alpha$, ""),
        (5, $x : alpha$, "5 Weak"),
        (5, $y : alpha -> beta$, "4 Weak"),
        (5, $y x : beta$, "8,7 App"),
        (5, $z (y x) : alpha$, "6,9 App"),
    ))
]

// MARK: Q. 4.4 (a)
#problem(source: "4.4 a")[
    Give a shortened #lwo derivation in flag format of
    $ alpha : *, beta : * -> * tack beta (beta alpha) : * $
]

#solution[
    #ded-nat(arr: (
        (0, $alpha : *$, ""),
        (1, $beta : * -> *$, ""),
        (2, $beta alpha : *$, "2,1 App"),
        (2, $beta (beta alpha) : *$, "2,4 App"),
    ))
]

// MARK: Q. 4.4 (b)
#problem(source: "4.4 b")[
    Give a shortened #lwo derivation in flag format of
    $ alpha : *, beta : * -> *, x : beta (beta alpha) tack lambda y : alpha. x : alpha -> beta (beta alpha) $
]
#solution[
    #ded-nat(arr: (
        (0, $alpha : *$, ""),
        (1, $beta : * -> *$, ""),
        (3, $x : beta (beta alpha)$, ""),
        (4, $y : alpha$, ""),
        (5, $x : beta (beta alpha)$, "3 Var"),
        (4, $lambda y : alpha. x : alpha -> beta (beta alpha)$, "5 Abst"),
    ))
]

// MARK: Q. 4.4 (c)
#problem(source: "4.4 c")[
    Give a shortened #lwo derivation in flag format of
    $ emptyset tack lambda alpha : *. lambda beta : * -> *. beta (beta alpha) : * -> (* -> *) -> * $
]
#solution[
    #ded-nat(arr: (
        (0, $alpha : *$, ""),
        (1, $beta : * -> *$, ""),
        (2, $beta alpha : *$, "2,1 App"),
        (2, $beta (beta alpha) : *$, "2,3 App"),
        (1, $lambda beta : * -> *. beta (beta alpha) : (* -> *) -> *$, "4 Abst"),
        (0, $lambda alpha: *. lambda beta : * -> *. beta (beta alpha) : * -> (* -> *) -> *$, "5 Abst"),
    ))
]

// MARK: Q. 4.4 (d)
#problem(source: "4.4 d")[
    Give a shortened #lwo derivation in flag format of
    $ nat : * tack (lambda alpha : *. lambda beta : * -> *. beta (beta alpha)) nat (lambda gamma : *. gamma) : * $
]

#solution[
    #ded-nat(arr: (
        (0, $nat : *$, ""),
        (1, $alpha : *$, ""),
        (2, $beta : * -> *$, ""),
        (3, $beta alpha : *$, "3,2 App"),
        (3, $beta (beta alpha) : *$, "3,4 App"),
        (2, $lambda beta : * -> *. beta (beta alpha) : (* -> *) -> *$, "5 Abst"),
        (1, $lambda alpha: *. lambda beta : * -> *. beta (beta alpha) : * -> (* -> *) -> *$, "6 Abst"),
        (1, $(lambda alpha: *. lambda beta : * -> *. beta (beta alpha)) nat : (* -> *) -> *$, "7,1 App"),
        (1, $gamma : *$, ""),
        (2, $gamma : *$, "9 Var"),
        (1, $lambda gamma : *. gamma : * -> *$, "10 Abst"),
        (1, $(lambda alpha: *. lambda beta : * -> *. beta (beta alpha)) nat (lambda gamma:*.gamma): *$, "8,11 App"),
    ))
]

// MARK: Q. 4.5
#problem(source: "4.5")[
    Give a shortened #lwo derivation in flag format of
    $ alpha : *. x : alpha tack lambda y : alpha. x : (lambda beta : *. beta -> beta) alpha $
]

#solution[
    #ded-nat(arr: (
        (0, $alpha : *$, ""),
        (1, $x : alpha$, ""),
        (2, $y : alpha$, ""),
        (3, $x : alpha$, "2 Weak"),
        (2, $lambda y : alpha. x : alpha -> alpha$, "4 Abst"),
        (2, $beta : *$, ""),
        (3, $beta -> beta: *$, "6,6 Form"),
        (2, $lambda beta : *. beta -> beta: * -> *$, "7 Abst"),
        (2, $(lambda beta : *. beta -> beta) alpha : *$, "8,1 App"),
        (2, $lambda y : alpha. x : (lambda beta : *. beta -> beta) alpha$, "5,9 Conv"),
    ))
]

// MARK: Q. 4.6 (a)
#problem(source: "4.6 a")[
    Show that no such context $Gamma$ and term $M$ in #lwo such that
    $ Gamma tack kind : M $
    is derivable.
]
#solution[
    Proof by induction on inference rules. Rules like $"Sort"$, $"Var"$, $"Form"$, $"Abst"$, $"App"$ has syntatically or semantic different conclusions than $kind : M$.
    #proof(prompt: "Case 1 : Rule Weak")[
        Let $Gamma', C : s equiv Gamma$. Therefore this derivation requries a premise $Gamma' tack kind: M$. By the inductive hypothesis this is impossible.
    ]
    #proof(prompt: "Case 2 : Rule Conv")[
        This derivation requires a premise $Gamma tack kind: M'$ such that $M =_beta M'$. By the inductive hypothesis this is impossible.
    ]
    By the principle of induction this proves that there's no derivation that could give $Gamma tack kind : M$.
]

// MARK: Q. 4.6 (b)
#problem(source: "4.6 b")[
    Prove there are no such context $Gamma$ and terms $M$ and $N$ in #lwo such that
    $ Gamma tack M -> kind : N $
]
#solution[
    Proof by induction on inference rules. Rules like $"Sort"$, $"Var"$, $"Abst"$, $"App"$ has syntatically or semantically conclusions than $M -> kind : N$.
    #proof(prompt: "Case 1 : Rule Weak")[
        Let $Gamma', C : s equiv Gamma$. The derivation requires a premise $Gamma' tack M -> kind : N$. By the inductive hypothesis this is impossible.
    ]
    #proof(prompt: "Case 2 : Rule Form")[
        This requires a derivation with premise $Gamma tack kind : N$, which by 4.6 a is not possible.
    ]
    #proof(prompt: "Case 3 : Rule Conv")[
        This requires a premise $Gamma tack M -> kind : N'$ such that $N equiv N'$. By the inductive hypothesis this is impossible.
    ]
    By the principle of induction this proves there's no derivation that could give $Gamma tack M -> kind: N$.
]

// MARK: Q. 4.7 (a)
#problem(source: "4.7 a")[
    Give #lwo definition of the notion legal term, #lwo context and domain.
]
#solution[
    #definition(id: "Legal Term")[
        are typable terms. That is, a term $M$ is legal iff there exists a context $Gamma$ and a legal higher-sorted term $alpha$ under $Gamma$ such that $Gamma tack M : alpha$.
    ]
    #definition(id: [#lwo Context.])[
        1. $emptyset$ is a #lwo context.
        2. When $Gamma$ is a valid #lwo context, $alpha$ is valid under $Gamma$, and type of $x$ is $alpha$, and $x in.not "dom" Gamma$, then the context $Gamma, x : alpha$ is valid in $lwo.$
    ]
    #definition(id: "Domain")[
        1. $"dom" emptyset = {}$
        2. $"dom" Gamma, x : s = "dom" Gamma union {x}$
    ]
]

// MARK: Q. 4.7 (b)
#problem(source: "4.7 b")[
    Formulate the Free Variables Lemma, Thinning Lemma, and Subtitution Lemma for #lwo.
]
#solution[
    #lemma[
        *FV Lemma (#lwo)*.
        For any legal term $M$ under $Gamma$, $"FV" M subset.eq "dom "Gamma$.

        More specifically,
        $
            forall M, alpha in Lambda_(underline(omega)), Gamma tack alpha : s, Gamma tack M : alpha quad &==> quad "FV" M &&subset.eq "dom" Gamma \
            M equiv kind quad &==> quad "FV" M equiv emptyset &&subset.eq "dom" Gamma
        $
    ]
    #lemma[
        *Thinning Lemma (#lwo)*. For any legal term $M$ in $Gamma'$ and $Gamma' subset.eq Gamma$, $M$ is legal under $Gamma$.
    ]
    #lemma[
        *Substitution Lemma (#lwo)*. Assume term $kappa : s$ under context $Gamma'$. Under another context $Gamma''$ given a term $Gamma'' tack N : kappa$ and another context $Gamma$ such that $Gamma, x : kappa, Gamma' tack M : A$ for some type $A : s$ under $Gamma$. Then
        $ Gamma, Gamma', Gamma'' tack M[x := N] : A $
    ]
]

---

Completed Dec 20 1:23 am.