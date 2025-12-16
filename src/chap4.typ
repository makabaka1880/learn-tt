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
        (name: "Sean Li", affiliation: "Reducted"),
    ),
    accent: accent,
);
#let problem = (..it) => problem(bg: accent, ..it)
#let nat = $mono("nat")$
#let bool = $mono("bool")$
#let ltrue = $"true"$
#let lfalse = $"false"$
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
}; #let symbol = $x$.body.func()
#show math.equation: it => {
    show symbol: set-symbol
    it
}

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


