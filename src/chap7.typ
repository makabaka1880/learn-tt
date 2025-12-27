
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
    subtitle: "Chapter 7",
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

#definition(prompt: [ Reference - Propositional Logic in $lambda C$ ])[
    #align(center, rule-set(
        prooftree(rule(
            name: [$bot$I or $not$E],
            $A$,
            $not A$,
            $bot$,
        )),
        prooftree(rule(
            name: [$bot$E],
            $bot$,
            $A$,
        )),
        prooftree(rule(
            name: [$and$I],
            $A$,
            $B$,
            $A and B$,
        )),
        prooftree(rule(
            name: [$and$EL],
            $A and B$,
            $A$,
        )),
        prooftree(rule(
            name: [$and$ER],
            $A and B$,
            $B$,
        )),
        prooftree(rule(
            name: [$or$IL],
            $a$,
            $a or b$,
        )),
        prooftree(rule(
            name: [$or$IR],
            $b$,
            $a or b$,
        )),
        prooftree(rule(
            name: [$=>$E],
            $A => B$,
            $A$,
            $B$,
        )),
        prooftree(rule(
            name: [$or$E],
            $A or B$,
            $A -> C$,
            $B -> C$,
            $C$,
        )),
        prooftree(rule(
            name: [$exists$I],
            $a in S$,
            $P(a)$,
            $exists a in S, P(a)$,
        )),
        prooftree(rule(
            name: [$not$I],
            ded-nat(arr: ((0, $A$, ""), (1, "...", ""), (1, $bot$, ""))),
            $not A$,
        )),
        prooftree(rule(
            name: [$=>$I],
            ded-nat(arr: ((0, $A$, ""), (1, $...$, ""), (1, $B$, ""))),
            $A => B$,
        )),
        prooftree(rule(
            name: [$forall I$],
            ded-nat(arr: ((0, $a in S$, ""), (1, $...$, ""), (1, $P(a)$, ""))),
            $forall a in S, P(a)$,
        )),
        prooftree(rule(
            name: [$exists$E],
            $exists x in S, P(x)$,
            $forall x in S, (P(x) => A)$,
            $A$,
        )),
        prooftree(rule(
            name: [$forall$E],
            $a in S$,
            $forall x in S, P(x)$,
            $P(a)$,
        )),
        prooftree(rule(
            name: "DN (Classical)",
            $not not A => A$,
        )),
        prooftree(rule(
            name: "ET (Classical)",
            $A or not A$,
        )),
    ))
]

#definition(prompt: "Reference - 2nd Encoding for Propositional Logic")[
    #table(
        columns: (.4fr, .6fr),
        stroke: none,
        row-gutter: -1mm,
        [*Proposition*], [*Minimal Propositional Logic*],
        $bot$, $forall A, A$,
        $A => B$, $A => B$,
        $not A$, $A => bot$,
        $A and B$, $forall C, (A => B => C) => C$,
        $A or B$, $forall C, (A => C) => (B => C) => C$,
        $forall a in S, P(a)$, $forall a in S. P(a)$,
        $exists a in S, P(a)$, $forall alpha, (forall a in S, (P(a) => alpha)) => alpha$,
    )
]

// MARK: Q. 7.1 (a)
#problem(source: "7.1 a")[
    Prove in natural deduction and $lambda C$ the tautology $ B => (A => B) $
]
#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, $B$, ""),
        (1, $A$, ""),
        (2, $B$, ""),
        (1, $A => B$, [$=>$I]),
        (0, $B => (A => B)$, [$=>$I]),
    )))
    #proof(prompt: $lambda C$, [
        Assuming context $Gamma equiv A : *, B : *$. By the PAT paradigm the proof is equivalent to an inhabitant of $B -> A -> B$.
        #ded-nat(arr: (
            (0, $A : *, B : *$, ""),
            (1, $x : B$, ""),
            (2, $y : A$, ""),
            (3, $x : B$, "Weak"),
            (2, $lambda y : A. x : A -> B$, "4 Abst"),
            (1, $lambda x : B. lambda y : A. x : B -> A -> B$, "5 Abst"),
        ))
    ])
]

// MARK: Q. 7.1 (b)
#problem(source: "7.1 b")[
    Prove in natural deduction and $lambda C$ the tautology $ not A => (A => B) $
]
#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, $not A$, ""),
        (1, $A$, ""),
        (2, $not A$, ""),
        (2, $A$, ""),
        (2, $bot$, [$bot$I]),
        (2, $B$, [$bot$E]),
        (1, $A => B$, [$=>$I]),
        (0, $not A => (A => B)$, [$=>$I]),
    )))
    #proof(prompt: $lambda C$)[
        Assuming context $Gamma equiv A : *, B : *$. By the PAT paradigm the proof is equivalent to an inhabitant of $(A -> bot) -> A -> B$.
        #ded-nat(arr: (
            (0, $A : *, B : *$, ""),
            (1, $x : not A$, ""),
            (2, $y : A$, ""),
            (3, $x y : Pi alpha : *. alpha$, "2,3 App (Neg Elim)"),
            (3, $x y B : B$, "4,1 App (Ex Falso)"),
            (2, $lambda y : A. x y B : A -> B$, "5 Abst"),
            (1, $lambda x : not A. lambda y : A. x y B : not A -> A -> B$, "6 Abst"),
        ))
    ]
]

// MARK: Q. 7.1 (c)
#problem(source: "7.1 c")[
    Prove in natural deduction and $lambda C$ the tautology $ (A => not B) => ((A => B) => not A) $
]

#solution[
    #proof(prompt: "Natural Deduction")[
        #ded-nat(arr: (
            (0, $A => not B$, ""),
            (1, $A => B$, ""),
            (2, $A$, ""),
            (3, $not B$, [1,3 $=>$E]),
            (3, $B$, [2,3 $=>$E]),
            (3, $bot$, [5,4 $bot$I]),
            (2, $not A$, [3,6 $not$I]),
            (1, $(A => B) => not A$, [2,7 $=>$I]),
            (0, $(A => not B) => ((A => B) => not A)$, [1,8 $=>$I]),
        ))
    ]
    #proof(prompt: $lambda C$)[
        Assuming context $Gamma equiv A : *, B : *$. The proof should be equivalent to an inhabitant of $(A -> B -> bot) -> (A -> B ) -> A -> bot$.
        #ded-nat(arr: (
            (0, $A : *, B : *$, ""),
            (1, $h : A -> not B$, ""),
            (2, $q : A -> B$, ""),
            (3, $a : A$, ""),
            (4, $q a : B$, "3,4 App"),
            (4, $h a : B -> bot$, "2,4 App"),
            (4, $h a (q a) : bot$, "6,5 App (Neg Elim)"),
            (3, $lambda a : A. h a (q a) : not A$, "7 Abst (Neg Intro)"),
            (2, $lambda q : A -> B. lambda a : A. h a (q a) : A -> B -> not A$, "8 Abst"),
            (
                1,
                $
                    & lambda h : A -> not B. lambda q : A -> B. lambda a : A. h a (q a) \
                    & quad : (A -> not B) -> A -> B -> not A
                $,
                "9 Abst",
            ),
        ))
    ]
]

// MARK: Q. 7.1 (d)
#problem(source: "7.1 d")[
    Prove in natural deduction and $lambda C$ the tautology
    $ not (A => B) => not B $
]
#solution[
    #proof(prompt: "Natural Deduction", ded-nat(arr: (
        (0, $not (A => B)$, ""),
        (1, $B$, ""),
        (2, $A$, ""),
        (3, $B$, ""),
        (2, $A => B$, [3,4 $=>$I]),
        (2, $bot$, [5,1 $bot$I]),
        (1, $not B$, [6 $not$I]),
        (0, $not (A => B) => not B$, [1,7 $=>$I]),
    )))
    #proof(prompt: $lambda C$)[
        Assuming context $Gamma equiv A : *, B : *$. The proof should be equivalent to an inhabitant of $((A -> B) -> bot) -> B -> bot$.
        #ded-nat(arr: (
            (0, $n : not (A -> B)$, ""),
            (1, $b : B$, ""),
            (2, $a : A$, ""),
            (3, $b : B$, "Weak"),
            (2, $lambda a : A. b : A -> B$, "4 Abst"),
            (2, $n (lambda a : A. b) : bot$, "1,5 App (Neg Elim)"),
            (1, $lambda b : B. n (lambda a : A. b) : not B$, "6 Abst (Neg Intro)"),
            (
                0,
                $
                    & lambda n : not (A -> B). lambda b : B. n (lambda a : A. b) \
                    & quad : not (A -> B) -> not B
                $,
                "7 Abst",
            ),
        ))
    ]
]

// MARK: Q. 7.2
#problem(source: "7.2")[
    Formulate the double negation law as an axiom in $lambda C$, and prove the following tautology in $lambda C$ with DN.
    $ (not A => A) => A $
]
#solution[
    The rule
    #align(center, prooftree(rule(name: "DN-E", $not not A => A$)))
    Could be translated into lambda calculus as
    $ Pi A : *. ((A -> bot) -> bot) -> A $
    #proof[
        Assume context $Gamma equiv A : *.$
        #ded-nat(arr: (
            (0, $A : *$, ""),
            (1, $h : not A -> A$, ""),
            (2, $x : not A$, ""),
            (3, $h x : A$, "2,3 App"),
            (3, $x (h x) : bot$, "3,4 App (Contradiction)"),
            (2, $lambda x : not A. x (h x) : not not A$, "5 Abst (Neg Intro)"),
            (2, $"DN" A : not not A -> A$, "1,1 App"),
            (2, $"DN" A (lambda x : not A. x (h x)) : A$, "App (Axiom DN)"),
            (
                1,
                $
                    & lambda h : not A -> A. "DN" A (lambda x : not A. x (h x)) \
                    & quad : (not A -> A) -> A
                $,
                "8 Abst",
            ),
        ))
    ]
]

// MARK: Q. 7.3 (a)
#problem(source: "7.3 a")[
    Prove the following tautology in classical logic using $lambda C$
    $ (A => B) => (not B => not A) $
]
#solution[
    Assume context $Gamma equiv A : *, B : *$. It suffices the proof to find an inhabitant of type $ (A -> B) -> (not B -> not A) $
    #proof(ded-nat(arr: (
        (0, $A : *, B : *$, ""),
        (1, $h : A -> B$, ""),
        (2, $b : not B$, ""),
        (3, $a : A$, ""),
        (4, $h a : B$, "5,2 App"),
        (4, $b (h a) : bot$, "6,3 App (Contradiction)"),
        (4, $b (h a) (not A) : not A$, "7,5 App (Ex Falso)"),
        (3, $lambda a : A. b (h a) (not A) : A -> not A$, "7 Abst"),
        (3, $a : not A$, ""),
        (4, $a : not A$, "Var"),
        (3, $lambda a: not A. a : (not A -> not A)$, "10 Abst"),
        (3, $"ET" A : A or not A$, "App (Axiom ET)"),
        (
            3,
            $
                & "ET" A (not A) : (A -> not A) -> \
                & quad (not A -> not A) -> not A
            $,
            "12 App",
        ),
        (
            3,
            $
                & "ET" A (not A) (lambda a : A. b (h a) (not A)) : \
                & quad (not A -> not A) -> not A
            $,
            "13,8 App",
        ),
        (
            3,
            $
                & "ET" A (not A) \
                & quad (lambda a : A. b (h a) (not A)) \
                & quad (lambda a : not A . a ) : not A
            $,
            "14,11 App",
        ),
        (
            2,
            $
                & lambda b : not B. "ET" A (not A) \
                & quad (lambda a : A. b (h a) (not A)) \
                & quad (lambda a : not A . a ) : not B -> not A
            $,
            "15 Abst",
        ),
        (
            1,
            $
                & lambda h : A -> B. lambda b : not B. "ET" A (not A) \
                & quad (lambda a : A. b (h a) (not A)) \
                & quad (lambda a : not A . a ) : \
                & wide (A -> B) -> not B -> not A
            $,
            "16 Abst",
        ),
    )))
]

// MARK: Q. 7.3 (b)
#problem(source: "7.3 b")[
    Prove the following tautology in classical logic using $lambda C$
    $ (not B => not A) => (A => B) $
]
#solution[
    Assume context $Gamma equiv A : *, B : *$. It suffices the proof to find an inhabitant of type $ (not B -> not A) -> A -> B $
    #proof(ded-nat(arr: (
        (0, $A : *, B : *$, ""),
        (1, $h : not B -> not A$, ""),
        (2, $a : A$, ""),
        (3, $b : B$, ""),
        (4, $b : B$, "Weak"),
        (3, $lambda b : B. b : B -> B$, ""),
        (3, $b : not B$, ""),
        (4, $h b : not A$, "2,7 App"),
        (4, $h b a : bot$, "8,2 App (Neg Elim)"),
        (4, $h b a B : B$, "9 App (Ex Falso)"),
        (3, $lambda b : not B. h b a B : not B -> B$, "10 Abst"),
        (3, $"ET" B : B or not B$, "1 App (Axiom ET)"),
        (3, $"ET" B B : (B -> B) -> (not B -> B) -> B$, "12,1 App"),
        (3, $"ET" B B (lambda b : B. b) : (not B -> B) -> B$, "13,6 App"),
        (3, $"ET" B B (lambda b : B. b) (lambda b : not B. h b a B ) : B$, "14,11 App"),
        (
            2,
            $
                & lambda a : A."ET" B B (lambda b : B. b) \
                & quad (lambda b : not B. h b a B) : A -> B
            $,
            "15 Abst",
        ),
        (
            1,
            $
                & lambda h : not B -> not A. lambda a : A. \
                & quad "ET" B B (lambda b : B. b) (lambda b : not B. h b a B) \
                & wide : (not B -> not A) -> A -> B
            $,
            "16 Abst",
        ),
    )))
]

// MARK: Q. 7.4
#problem(source: "7.4")[
    Derive *$and$-EL* and *$and$-ER* in $lambda C$.
]
#solution[
    The derivation is the same as proving
    $
        M : Pi C. (A -> B -> C) -> C tack N_1 : A \
        M : Pi C. (A -> B -> C) -> C tack N_2 : B
    $
    #proof(prompt: "Left Projection", ded-nat(arr: (
        (0, $M : Pi C. (A -> B -> C) -> C$, ""),
        (1, $M A : (A -> B -> A) -> A$, ""),
        (1, $x : A$, ""),
        (2, $b : B$, ""),
        (3, $x : A$, "Weak"),
        (2, $lambda b : B. x : B -> A$, "5 Abst"),
        (1, $lambda x : A. lambda b : B. x : A -> B -> A$, "6 Abst"),
        (1, $N_1 equiv M A (lambda x : A. lambda b : B. x) : A$, "2,7 App"),
    )))
    #proof(prompt: "Right Projection", ded-nat(arr: (
        (0, $M : Pi C. (A -> B -> C) -> C$, ""),
        (1, $M B : (A -> B -> B) -> B$, ""),
        (1, $x : A$, ""),
        (2, $b : B$, ""),
        (3, $b : B$, "Weak"),
        (2, $lambda b : B. b : B -> B$, "5 Abst"),
        (1, $lambda x : A. lambda b : B. b : A -> B -> B$, "6 Abst"),
        (1, $N_2 equiv M B (lambda x : A. lambda b : B. b) : B$, "2,7 App"),
    )))
]

// MARK: Q. 7.5 (a)
#problem(source: "7.5 a")[
    Prove tautology under classical logic $ not (A => B) => A $
]

#solution[
    Assume context $Gamma equiv A : *, B : *$. Therefore the proof suffices to find an inhabitant of $ ((A -> B) -> bot) -> A $
    #proof(ded-nat(arr: (
        (0, $A : *, B : *$, ""),
        (1, $h : not (A -> B)$, ""),
        (2, $a : A$, ""),
        (3, $a : A$, "Weak"),
        (2, $lambda a : A. a : A -> A$, "4 Abst"),
        (2, $a : not A$, ""),
        (3, $n : A$, ""),
        (4, $a n : bot$, "6,7 App (Contradiction)"),
        (4, $a n B : B$, "8 App (Ex Falso)"),
        (3, $lambda n : A. a n B : A -> B$, "9 Abst"),
        (3, $h (lambda n : A. a n B) : bot$, "10,2 App (Contra.)"),
        (3, $h (lambda n : A. a n B) A : A$, "11 App (Ex Falso)"),
        (
            2,
            $
                & lambda a : not A. h (lambda n : A. a n B) A \
                & quad : not A -> A
            $,
            "12 Abst",
        ),
        (2, $"ET" : Pi S : *. S or not S$, "Axiom ET"),
        (2, $"ET" A : A or not A$, "14,1 App"),
        (2, $"ET" A A : (A -> A) -> (not A -> A) -> A$, "15,1 App"),
        (
            2,
            $
                & "ET" A A (lambda a : A. a) \
                & quad : (not A -> A) -> A
            $,
            "16,5 App",
        ),
        (
            2,
            $
                & "ET" A A (lambda a : A. a) \
                & quad (lambda a : not A. h (lambda n : A. a n B) A) : A
            $,
            "17,13 App",
        ),
        (
            1,
            $
                & lambda h : not (A -> B). "ET" A A (lambda a : A. a) \
                & quad (lambda a : not A. h (lambda n : A. a n B) A) \
                & wide : not (A -> B) -> A
            $,
            "18 Abst",
        ),
    )))
]

// MARK: Q. 7.5 (b)
#problem(source: "7.5 b")[
    Prove tautology under classical logic
    $ not (A => B) => (A and not B) $
]
#solution[
    Assume context $Gamma equiv A : *, B : *$. Therefore the proof suffices to find an inhabitant of
    $ ((A -> B) -> bot) -> Pi C: *. ((A -> (B -> bot) -> C) -> C) $
    #let ha = $italic("ha")$
    #let hb = $italic("hb")$
    #let hc = $italic("hc")$
    #let hna = $italic("hna")$
    #proof(ded-nat(arr: (
        (0, $A : *, B : *$, ""),
        (1, $p : not (A -> B)$, ""),
        (2, $C : *$, ""),
        (3, $h : A -> not B -> C$, ""),
        (4, $hb : B$, ""),
        (5, $ha : A$, ""),
        (6, $hb : B$, "Weak"),
        (5, $lambda ha : A. hb : A -> B$, "7 Abst"),
        (5, $p (lambda ha : A. hb) : bot$, "2,8 App (Contra.)"),
        (4, $lambda hb : B. p (lambda ha : A. hb) : not B$, "9 Abst (Neg Intro)"),
        (4, $hna : not A$, ""),
        (5, $ha' : A$, ""),
        (6, $hna ha' : bot$, "11,12 App (Contra.)"),
        (6, $hna ha' B : B$, "13,1 App (Ex Falso)"),
        (5, $lambda ha' : A. hna ha' B : A -> B$, "14 Abst"),
        (5, $p (lambda ha' : A. hna ha' B) : bot$, "2,15 App (Contra.)"),
        (5, $p (lambda ha' : A. hna ha' B) A : A$, "2,15 App (Contra.)"),
        (
            4,
            $
                & lambda hna : not A. p \
                & quad (lambda ha' : A. hna ha' B) A \
                & wide : not A -> A
            $,
            "17 Abst",
        ),
        (4, $ha'' : A$, ""),
        (5, $ha'' : A$, "Var"),
        (4, $lambda ha'' : A. ha'' : A -> A$, "20 Abst"),
        (4, $"ET" : Pi S : *. S or not S$, "Axiom ET"),
        (4, $"ET" A : A or not A$, "22,1 App"),
        (4, $"ET" A A : (A -> A) -> (not A -> A) -> A$, "23,1 App"),
        (
            4,
            $
                & "ET" A A \
                & quad (lambda ha'' : A. ha'') \
                & wide : (not A -> A) -> A \
            $,
            "24,21 App",
        ),
        (
            4,
            $
                & "ET" A A \
                & quad (lambda ha'' : A. ha'') \
                & quad (lambda hna : not A. p \
                & wide (lambda ha' : A. hna ha' B) A) : A \
            $,
            "25,18 App",
        ),
        (
            4,
            $
                & h ("ET" A A \
                & quad (lambda ha'' : A. ha'') \
                & quad (lambda hna : not A. p \
                & wide (lambda ha' : A. hna ha' B) A)) \
                & wide quad : not B -> C
            $,
            "4,26 App",
        ),
        (
            4,
            $
                & h ("ET" A A \
                & quad (lambda ha'' : A. ha'') \
                & quad (lambda hna : not A. p \
                & wide (lambda ha' : A. hna ha' B) A)) \
                & quad (lambda hb : B. p (lambda ha : A. hb)) : C \
            $,
            "27,10 App",
        ),
        (
            3,
            $
                & lambda h : A -> not B -> C. h ("ET" A A \
                & quad (lambda ha'' : A. ha'') \
                & quad (lambda hna : not A. p (lambda ha' : A. hna ha' B) A)) \
                & quad (lambda hb : B. p (lambda ha : A. hb)) \
                & wide : (A -> not B -> C) -> C
            $,
            "28 Abst",
        ),
        (
            2,
            $
                & lambda C : *. lambda h : A -> not B -> C. \
                & quad h ("ET" A A \
                & wide (lambda ha'' : A. ha'') \
                & wide (lambda hna : not A. p (lambda ha' : A. hna ha' B) A)) \
                & wide (lambda hb : B. p (lambda ha : A. hb)) : A and not B
            $,
            "29 Abst",
        ),
        (
            1,
            $
                & lambda p : not (A -> B). \
                & quad lambda C : *. lambda h : A -> not B -> C. \
                & wide h ("ET" A A \
                & wide quad (lambda ha'' : A. ha'') \
                & wide quad (lambda hna : not A. p (lambda ha' : A. hna ha' B) A)) \
                & wide quad (lambda hb : B. p (lambda ha : A. hb)) \
                & wide wide : not (A -> B) -> (A and not B)
            $,
            "30 Abst",
        ),
    )))
]

// MARK: Q. 7.6 (a)
#problem(source: "7.6 a")[
    Verify that the following expressions is a tautology in constructive logic
    $
        not A => not (A and B)
    $
]
#solution[
    Suppose context $A : *, B : *$. The proof suffices to give a inhabitant of type
    $
        not A -> not (A and B) equiv
        (A -> bot) -> (Pi C : *. (A -> B -> C) -> C) -> bot
    $
    #let na = $italic("na")$
    #let ha = $italic("ha")$
    #let hb = $italic("hb")$
    #proof(ded-nat(arr: (
        (0, $A : *, B : *$, ""),
        (1, $na : not A$, ""),
        (2, $h : Pi C : *. (A -> B -> C) -> C$, ""),
        (3, $h A : (A -> B -> A) -> A$, "3,1 App"),
        (3, $ha : A$, ""),
        (4, $hb : B$, ""),
        (5, $ha : A$, ""),
        (4, $lambda hb : B. ha : B -> A$, "7 Abst"),
        (3, $lambda ha : A. lambda hb : B. ha : A -> B -> A$, "8 Abst"),
        (3, $h A (lambda ha : A. lambda hb : B. ha) : A$, "4,9 App"),
        (3, $na (h A (lambda ha : A. lambda hb : B. ha)) : bot$, "2,10 App (Contradiction)"),
        (
            2,
            $
                & lambda h : A and B. \
                & quad na (h A (lambda ha : A. lambda hb : B. ha)) \
                & wide : A and B -> bot
            $,
            "11 Abst",
        ),
        (
            1,
            $
                & lambda na : not A. lambda h : A and B. \
                & quad na (h A (lambda ha : A. lambda hb : B. ha)) \
                & wide : not A -> not (A and B)
            $,
            "12 Abst",
        ),
    )))
]

// MARK: Q. 7.6 (b)
#problem(source: "7.6 b")[
    Verify that the following expressions is a tautology in constructive logic
    $
        not (A and not A)
    $
]
#solution[
    Suppose context $A : *, B : *$. The proof suffices to give a inhabitant of type
    $ (Pi S : *. (A -> (A -> bot) -> S) -> S) -> bot $

    #proof(ded-nat(arr: (
        (0, $A : *, B : *, bot : sort$, ""),
        (1, $h : Pi S : *. (A -> not A -> S) -> S$, ""),
        (2, $h bot : (A -> not A -> bot) -> bot$, "2,1 App"),
        (2, $a : A$, ""),
        (3, $n : not A$, ""),
        (4, $n a : bot$, "5,4 App"),
        (3, $lambda n : not A. n a : not A -> bot$, "6 Abst"),
        (2, $lambda a : A. lambda n : not A. n a : A -> not A -> bot$, "7 Abst"),
        (2, $h bot (lambda a : A. lambda n : not A. n a) : bot$, "3,8 App"),
        (1, $lambda h : A and not A. h bot (lambda a : A. lambda n : not A. n a) : A and not A -> bot$, "9 Abst"),
    )))
]
