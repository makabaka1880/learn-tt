#import "./cyan-report/0.1.0/lib.typ": *;
#import "@preview/derive-it:1.1.0": *;
#import "@preview/tdtr:0.4.2": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set;

#let accent = rgb("#077272")
#show ref: it => {
    if query(it.target) == ([#str(it.target)],) {
        emph(link(it.target, str(it.target)))
    } else {
        it
    }
}
#show: cyan-report.with(
    title: "Excercises",
    subtitle: "Chapter 1",
    authors: (
        (name: "Sean Li", affiliation: "Reducted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)

#let mark(content) = text(content, fill: accent)

// MARK: Q. 1.1
#problem[
    Simplify notation of the following terms
    $
        "(a)" & (lambda x. (((x z) y) (x x))) \
        "(b)" & ((lambda x. (lambda y. (lambda z. (z ((x y) z)))))(lambda u. u))
    $
]
#solution[
    $
        "(a)" & lambda x. (x z y) (x x) \
        "(b)" & (lambda x y z. x (x y z)) (lambda u. u)
    $
]

// MARK: Q. 1.2
#problem[
    Find the alpha equivalent terms to
    $ lambda x. x (lambda x . x) $
    In
    $
        "(a)" & lambda y. y (lambda x. x) \
        "(b)" & lambda y. y (lambda x. y) \
        "(c)" & lambda y. y (lambda x. y)
    $
]
#solution[Only (a).]

// MARK: Q. 1.3
#problem[
    Prove $ lambda x. x (lambda z .y) =_alpha lambda z. z (lambda z. y) $
]
#solution[
    #proof[
        By definition of alpha equivalence
        $ M =_alpha N <==> exists phi, M^phi ->_alpha N and "FR" M = "FR" N $
        The witness of $phi$ is substituting bound variable $x$ with $z$, and $z$ is not a free variable in the term, thus the two terms are alpha equivalent.
        $ lambda x. x (lambda z .y)^(x -> z) ->_alpha lambda z. z (lambda z. y) $
    ]
]

// MARK: Q. 1.4
#problem[
    Consider the following term:
    $ U := (lambda z. z x z) ((lambda y. x y) x) $
    1. Find $"Sub" U$
    2. Draw tree rep of $U$
    3. Find $"FV" U$
    4. Find alpha equivalent terms to $U$ from below and point out which of those follows the Barendregt convention:
    $
        "(a)" & (lambda y. y x y)((lambda z. x z) x) \
        "(b)" & (lambda x. x y x)((lambda z. y z) y) \
        "(c)" & (lambda y. y x y)((lambda y. x y) x) \
        "(d)" & (lambda v. (v x) v) ((lambda u. u v) x) \
    $
]

1. Find $"Sub" U$.
#solution[
    $
        "Sub" & U = { \
              & (lambda z. z x z) ((lambda y. x y) x), (lambda z. z x z), ((lambda y. x y) x), \
              & (lambda y. y x), (y), (lambda z. x z), (x), \
              & (lambda y. y), (x), (lambda z. x), (z),
                (y), (x) \
            }
    $
]

2. Draw a tree rep of $U$.
#solution[

    #tidy-tree-graph[
        - Application
            - $lambda z$
                - Application
                    - Application
                        - z
                        - x
                    - z
            - Application
                - $lambda y$
                    - Application
                        - x
                        - y
                - x
    ]
]

3. Find $"FV" U$
#solution[
    $
        "FV" U & = "FV" (lambda y. y x y) union "FV" (lambda z. x z) x \
               & = ("FV" y x y) \\ {y} union ("FV" lambda z. x z) union {x} \
               & = ("FV" y x) \\ {y} union ("FV" x z) \\ {z} union {x} \
               & = {x}
    $
]

4. Find an alpha-equivalent term.
#solution[
    $ (a) =_alpha (c) =_alpha U $
    (a), (b), and (c) all follow the Barendregt convention. In (d) the free variable $v$ was bound in the first abstraction.
]

// MARK: Q. 1.5
#problem[
    Give the results of the following substitutions
    $
        "(a)" & (lambda x. y (lambda y. x y))[y := lambda z. z x] \
        "(b)" & ((x y z)[x := y])[y := z] \
        "(c)" & ((lambda x. x y z)[x := y])[y := z] \
        "(d)" & (lambda y. y y x)[x := y z] \
    $
]
#solution[
    $
        "(a)" & (lambda v. (lambda z. z x) (lambda u. v u)) \
        "(b)" & (y y z)[y := z] = z z z \
        "(c)" & (lambda x. x y z)[y := z] = (lambda x. x z z) \
        "(d)" & (lambda u. u u (y z)) \
    $
]

// MARK: Q. 1.6
#problem[
    $ not(forall M L N in Lambda, M[x := N, y := L] equiv_alpha M[x := N][y := L]) $
]
#solution[
    #proof[
        Because $"RHS" = M[x := N][y := L] = M[x:= N[y:=L]][y:=L]$, if $y in "FV" N$, then what $x$ gets substituted with will have $y$ substituted for $L$, which is completely different with $"LHS"$.
    ]
]

// MARK: Q. 1.7
#problem[
    Find all available redexes in $ U := (lambda z. z x z) ((lambda y. x y) x) $
    And all reduction pathes to the $beta$-normal form.
]
#solution[
    The first redex is the term as an application itself; another the second term in the application.

    #tidy-tree-graph[
        - $(lambda z. z x z) ((lambda y. x y) x)$
            - $(lambda z. z x z) (x x)$
                - $x x x (x x)$
            - $((lambda y. x y) x) x ((lambda y. x y) x)$
                - $x x x ((lambda y. x y) x)$
                    - $x x x (x x)$
                - $((lambda y. x y) x) x (x x)$
                    - $x x x (x x)$
    ]
]

// MARK: Q. 1.8
#problem[
    Show that $ (lambda x. x x) y !=_beta (lambda x y. y x) x x $
]
#solution[
    By Collorary 1.9.9, it suffices to prove the hypothesis with a proof of a common normal reducted form from LHS and RHS not existing.
    #proof(prompt: "Contradiction")[
        By definition of $=_beta$, there exists
        The set of all terms attainable from $beta$-reduction on $(lambda x. x x) y$ and $(lambda x y. y x) x x$ do not intersect. Therefore,
        $
            not(exists L in Lambda, (lambda x. x x) y ->>_beta L and (lambda x y. y x) x x ->>_beta L) ==> not ((lambda x. x x) y =_beta (lambda x y. y x) x x)
        $
    ]
]

// MARK: Q. 1.9
#problem[
    Define the combinators
    $
        K & := lambda x y. x \
        S & := lambda x y z. x z (y z)
    $
    Prove that
    $ forall P Q in Lambda, K P Q ->>_beta P $
    $ forall P Q R in Lambda, S P Q R ->>_beta P R (Q R) $
]
#solution[
    #proof[
        $ K P Q = (lambda x y. x) P Q ->_beta (lambda y. x)[x := P] Q ->_beta P[y := Q] = P $
        $ S P Q R = (lambda x y z. x z (y z)) ->>_beta (x z (y z))[x := P][y := Q][z := R] = P R (Q R) $
    ]
]

// MARK: Q. 1.10
#problem[
    We define the church numerals
    $
         "zero" & := lambda f x. x \
          "one" & := lambda f x. f x \
          "two" & := lambda f x. f f x \
                & ... \
        "num"_n & := lambda f x. f^n x
    $
    And operations
    $
        "add" & := lambda n m f x. m f (n f x) \
        "mul" & := lambda n m f x. m (n f) x
    $
    Show
    $
        "(a)" & "add" "one" "one" ->>_beta "two" \
        "(b)" & "add" "one" "one" !=_beta "mul" "one" "zero"
    $
]
#solution[
    $
        "(a)" quad "add" "one" "one" & = (lambda n m f x. m f(n f x)) (lambda f x. f x) (lambda f x. f x) \
                                     & ->>_beta (lambda f x. (lambda f x. f x) f ((lambda f x. f x) f x)) \
                                     & ->>_beta (lambda f x. (lambda x. f x) f x) \
                                     & ->>_beta (lambda f x. f f x) = "two"
    $
    $
        "(b)" quad "mul" "one" "one" & = (lambda n m f x. m (n f) x)(lambda f x. f x)(lambda f x. f x) \
                                     & ->>_beta lambda f x. (lambda f x. f x) ((lambda f x. f x) f) x \
                                     & ->>_beta lambda f x. f x = "one"
    $
    Because no intermediate form in the beta reduction process of the two terms are $alpha$-equivalent, by collorary 1.9.9 the two terms are not $beta$-equivalent.
]

// MARK: Q. 1.11
#problem[
    We define
    $ "succ" := lambda m f x. f (m f x) "s.t." forall "num"_n, "succ" "num"_n = "num"_(n + 1) $
    Prove $ "succ" "zero" =_beta "one" \
    "succ" "one" =_beta "two" $
]
#solution[
    It suffices to provide a witness of a reduction chain from one side to the other to prove $beta$-equivalence.
    #proof[
        $
            "succ" "zero" & = (lambda m f x. f (m f x)) (lambda f x. x) \
                          & ->_beta (lambda f x. f ((lambda f x. x) f x)) \
                          & ->>_beta (lambda f x. f x) = "one"
        $
        The path $"succ" "zero" ->>_beta "one"$ derived above is the witness of a reduction chain from LHS to RHS.
        $
            "succ" "one" & =(lambda m f x. f (m f x)) (lambda f x. f x) \
                         & ->_beta (lambda f x. f ((lambda f x. f x) f x)) \
                         & ->>_beta (lambda f x. f (f x)) = "two"
        $
        The path $"succ" "one" ->>_beta "two"$ derived above is the witness of a reduction chain from LHS to RHS.
    ]
]

// MARK: Q. 1.12
#problem[
    We define the $lambda$-terms $top_lambda ("true")$ and $bot_lambda ("false")$ and $not_lambda ("not")$ by:
    $
        top_lambda := lambda x y. x quad bot_lambda := lambda x y.y quad \
        not_lambda := lambda a. a bot_lambda top_lambda
    $
    Show that $ not_lambda (not_lambda top_lambda) =_beta top_lambda \
    not_lambda (not_lambda bot_lambda) =_beta bot_lambda $
]

#solution[
    It suffices to provide a witness of a reduction chain from one side to the other to prove $beta$-equivalence.
    #proof[
        $
            not_lambda (not_lambda top_lambda) & = not_lambda ((lambda a. a bot_lambda top_lambda) (lambda x y. x)) \
                                               & ->>_beta not_lambda ((lambda x y. x) bot_lambda top_lambda) \
                                               & ->>_beta (lambda a. a bot_lambda top_lambda) bot_lambda \
                                               & ->>_beta (lambda x y. y) bot_lambda top_lambda \
                                               & ->>_beta top_lambda
        $
        $
            not_lambda (not_lambda bot_lambda) & = not_lambda ((lambda a. a bot_lambda top_lambda) (lambda x y. y)) \
                                               & ->>_beta not_lambda ((lambda x y. x) bot_lambda top_lambda) \
                                               & ->>_beta (lambda a. a bot_lambda top_lambda) top_lambda \
                                               & ->>_beta (lambda x y. x) bot_lambda top_lambda \
                                               & ->>_beta bot_lambda
        $
    ]
]

// MARK: Q. 1.13
#problem[
    Define $ "iszero" := lambda m. m (lambda x. bot_lambda) top_lambda $
    Prove $ "iszero" "zero" ->>_beta top_lambda \ forall n in NN^+, "iszero" "num"_n ->>_beta bot_lambda $
]
#solution[
    $
        "iszero" "zero" & = (lambda m. m (lambda x. bot_lambda) top_lambda) (lambda f x. x) \
                        & ->>_beta (lambda f x. x) (lambda x. bot_lambda) top_lambda \
                        & ->>_beta top_lambda
    $
    $
        "iszero" "num"_n & = (lambda m. m(lambda x. bot_lambda) top_lambda) (lambda f x. f^n x) \
                         & ->>_beta (lambda f x. f^n x) (lambda x. bot_lambda) top_lambda \
                         & ->>_beta (lambda x. bot_lambda) ((lambda x. bot_lambda)^(n - 1) top_lambda)
                           ->>_beta bot_lambda
    $
]

// MARK: Q. 1.14
#problem[
    If-else can be modeled as
    $ "ifelse" = lambda x t f. x t f $
    Where when $x$, then $t$, else $f$.
    Prove correctness by applying $top_lambda$ and $bot_lambda$ on $"ifelse"$.
]
#solution[
    $
        "ifelse" top_lambda & = (lambda x t f. x t f) top_lambda \
                            & ->>_beta (lambda t f. (lambda x y. x) t f) ->>_beta (lambda t f. t)
    $
    $
        "ifelse" top_lambda & = (lambda x t f. x t f) bot_lambda \
                            & ->>_beta (lambda t f. (lambda x y. y) t f) ->>_beta (lambda t f. f)
    $
    By applying the results to any two values, the correct corresponding value returns, ex, for $"ifelse" top_lambda$, $t$ is always returned.
]


// MARK: Q. 1.15
// TODO: In the book it also requires a proof that (lambda x. x x x) does not have a beta-nf, which is not true. Maybe a flaw in the book..?
#problem[
    Prove that $Omega := (lambda x. x x) (lambda x. x x)$ does not have a $beta$-nf.
]
#solution[
    Firstly let's prove $Omega.$
    #proof[
        Induction on $Omega$'s only reduction path proves that every $Omega ->>_beta Omega_i = Omega$. For the base case because $Omega$ has one and only one redux, it could only reduce to $Omega_1$ which is equivalent to itself. For the inductive step, $Omega_i = Omega$, therefore $Omega_i ->_beta Omega_(i + 1)$ is still $Omega$.

        By definition, a term having a $beta$-nf requires the existence of a form in $beta$-nf such that the term can reduce to. By induction, $Omega$ only reduces to $Omega$, and $Omega$ is not in $beta$-nf because it contains $beta$-redex. Therefore, $Omega$ can never reduce to a $beta$-nf, thus it does not have a $beta$-nf.
    ]
]

// MARK: Q. 1.16
#problem[
    Let $M$ be a $lambda$-term with the following properties:
    - $M$ has a $beta$-nf.
    - There exists an infinite reduction path $M equiv M_0 ->_beta M_1 ->_beta ...$ on $M$.
    Prove that every $M_i$ has a $beta$-nf,  and give an example of $M$.
]

#solution[
    An example would be $(lambda x y. y)Omega$. Reduction can go on infinitely by reducing on $Omega$, but the $beta$-nf of the term is $lambda y. y$
    #proof[
        Denote $beta$-nf of $M$ as $M'$. For any form in the reduction path, $M ->>_beta M_i$. In conjunction with $M ->>_beta M'$, by the Church-Rosser theorem, there exists $L$ such that $M_i ->>_beta L$ and $M' ->>_beta L$. Because $M'$ is in $beta$-nf, $L$ can only be $M'$, thus $M_i ->>_beta M'$, so $M_i$ is capable of reducing to $M'$, a $beta$-nf. Therefore, any form in the reduction path has a $beta$-nf.
    ]
]

// MARK: Q. 1.17
#problem[
    If $M N$ is strongly normalizing, then both $M$ and $N$ are strongly normalizing.
]
#solution[
    #proof[If $M$ is not strongly normalizing, then there exists a reduction path $M_0 ->_beta M_1 ->_beta ...$ Therefore, $M N$ would have had a reduction path $M N ->_beta M_1 N ->_beta ...$ that is infinite, which contradicts with $M N$ being strongly normalizing. Vice versa for $N$.]
]

// MARK: Q. 1.18
#problem[
    Let $L, M, N in Lambda$ such that $L =_beta M$ and $L ->>_beta N$. Moreover, $N$ is in $beta$-nf. Prove that $M ->>_beta N$.
]
#solution[
    Collorary 1.9.9.
]

// MARK: Q. 1.19
#problem[
    Define
    $ U := lambda z x. x (z z x) quad "and" quad Z := U U $
    Prove $Z$ is a fixed point combinator.
]
#solution[
    Proving $forall L in Lambda, L (Z L) ->>_beta Z L$.
    #proof[
        $
            Z L & = (lambda z x . x (z z x)) (lambda z x . x (z z x)) L \
                & ->>_beta L ((lambda z x . x (z z x))(lambda z x . x (z z x)) L) ->>_beta L (Z L)
        $
    ]
]

// MARK: Q. 1.20
#problem[
    Solve for $M in Lambda$ in each equation:
    $
              M & =_beta lambda x y. x M y \
        M x y z & =_beta x y z M
    $
]
#solution[
    By the property of the $Y$ combinator: $ f (Y f) = Y f $
    The first equation can be remodeled as
    $ M =_beta L M "where" L = lambda m x y.x m y $
    Solving for fixed point of $L$ :
    $
        M & equiv Y L equiv L(Y L) \
          & = (lambda x. L(x x)) (lambda x. L(x x)) \
          & = (lambda x. (lambda m u v. u m v) (x x)) (lambda x. (lambda m u v. u m v) (x x)) \
          & ->>_beta (lambda x. (lambda u v. u (x x) v)) (lambda x. (lambda u v. u (x x) v)) \
    $
    The second equation can be $eta$-reduced on both sides:
    $
        M x y z & =_beta x y z M \
              M & =_beta lambda x y z. x y z M
    $
    Remodeling equation:
    $ M = N M "where" M = lambda m x y z. x y z m $
    then
    $
        M & equiv Y N equiv N (Y N) \
          & = (lambda x. N (x x)) (lambda x. N (x x)) \
          & = (lambda x. (lambda m u y z. u y z m) (x x)) (lambda x. (lambda m u y z. u y z m) (x x)) \
          & ->>_beta (lambda x. (lambda u y z. u y z (x x))) (lambda x. (lambda u y z. u y z (x x)))
    $
]
