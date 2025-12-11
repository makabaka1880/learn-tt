#import "@preview/cyan-report:0.1.0": *
#import "@preview/lovelace:0.3.0": *

// Setting up the theme
#let accent = rgb(50, 150, 150)
#show: cyan-report.with(
    title: "Excercises",
    subtitle: "Chapter 2",
    authors: (
        (name: "Makabaka1880", affiliation: "Reducted for privacy"),
    ),
    accent: accent, // Note that the accent color defaults to (50, 150, 150) if not set.
);


This is a sample document to demonstrate what cyan-report is capable of. The problems below come from the book _An Introduction to Formal Languages and Automata_.
= Example Usage of Containers
We are given a language
$ L & = {a b, a, b a a} $
And sentences
$
    u_1 & = a b a a b a a a b a a \
    u_2 & = a a a a b a a a a \
    u_3 & = b a a a a a b a a a a b \
    u_4 & = b a a a a a a b a a
$

// MARK: Problem Box
// You can use a problem box to present a problem / prompt.
// TODO: Definable title and default bg color
#problem(bg: accent)[
    Which of the strings are in $L^*$?
]

// MARK: Solution Box
// A solution box presents a italic Solution tag before the contents.
#solution[
    In order for a sentence to be in the star-closure of a language $L$, then the sentence must be constructable from concatenations of substrings in $L$. Let's prove this lemma.
    // MARK: Lemma Box
    // An elegant container specifying a lemma. Automatic numbering is added.
    // TODO: More customizable numbering
    #lemma[
        $u in L^* <==> exists w_1, w_2, ..., w_n in L, u = w_1 w_2 ... w_n$
        // MARK: Proof Box
        // A proof box looks like a solution box but with a QED tombstone symbol. Currently only supports the tombstone.
        // TODO: Allow customizable QED symbol.
        #proof[
            From the definition of star-closure we have
            $ u in L^* <==> u in union.big_(i = 0)^(infinity) L^i $
            Therefore $u$ must be in at least on of $L^n$. An induction $n$ can be done, starting from $n = 0$ as the base case. Here, $u = lambda$, wIHch exactly the empty concatenation of elements of $L$.

            Now suppose the lemma holds for $n$. For $n + 1$ by definition
            $ L^(n + 1) = L^n L = {v w : v in L^n, w in L} $
            Therefore if $u in L^(n + 1)$, then $u$ must be the concatenation of some $v$ from $L^n$ and $w$ from $L$. By the inductive hypothesis, $v$ is the concatenation of substrings from $L$, thus $u$ is the concatenation of substrings from $L$ and a substring from $L$, thes the concatenation of substrings of $L.$
        ]
    ]

    #let marka = text($a b$, fill: red)
    #let markb = text($a$, fill: blue)
    #let markc = text($b a a$, fill: green)
    Therefore in order for a sentence to be in $L^*$, one just need to guaruntee that the sentence can be constructed from ${marka, markb, markc}$.

    One can easily check that
    $
        u_1 & = markb markc marka markb markb markb markc \
        u_2 & = markb markb markb markb markc markb markb \
        u_3 & = markc markb markb markb markc markb marka \
        u_4 & = markc markb markb markb markb markc
    $
    So the answer is *all of them are sentences under $L^*$*.
]

// MARK: Q.5.2
#problem(bg: accent)[
    Which of the strings are in $L^4$?
]

#solution[
    $u_2$ and $u_3$ are.
    #proof[
        Previously constructed concatenations proved that $ u_2, u_4 in L^3 subset.eq L^4 $
        By a DFS search it can be easily proven that $u_1, u_3 in.not L^4$.
        #pseudocode-list[
            + *set* $L' <- L union L^0$
            + *for* $s_1$ in $L'$ *do*
                + *for* $s_2$ in $L'$ *do*
                    + *for* $s_3$ in $L'$ *do*
                        + *for* $s_4$ in $L'$ *do*
                            + *set* $s <- s_1 s_2 s_3 s_4$
                            + *if* $s = u_1$ *then* *return* $s$
                            + *else* *continue*
            + $s$ *not found*
        ]
        Following is an implementation in `C99`.
        ```c
        #include <stdio.h>
        #include <string.h>
        #include <stdbool.h>

        #define MAX_LEN 100

        // L' = L ∪ L^0
        const char* L_prime[] = {"", "a", "aa"};
        const int L_prime_size = 3;

        bool search_u1(const char* target) {
            char concat[MAX_LEN];

            for (int i = 0; i < L_prime_size; i++) {
                for (int j = 0; j < L_prime_size; j++) {
                    for (int k = 0; k < L_prime_size; k++) {
                        for (int l = 0; l < L_prime_size; l++) {
                            // s = s1 s2 s3 s4
                            snprintf(concat, MAX_LEN, "%s%s%s%s",
                                    L_prime[i], L_prime[j],
                                    L_prime[k], L_prime[l]);
                            if (strcmp(concat, target) == 0) return true;
                        }
                    }
                }
            }
            return false; // s not found
        }
        ```
    ]
]
