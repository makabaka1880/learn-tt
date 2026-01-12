#import "constants.typ": *
#let theorem-cnt = state("theorem-cnt", 1)
#let lemma-cnt = state("lemma-cnt", 1)
#let corollary-cnt = state("collary-cnt", 1)
#let theorem(content) = context {
    theorem-cnt.update(it => it + 1)
    v(box-vspace)
    block(
        [
            #line(start: (-70pt, 0pt), length: page.width - 140pt)
            #place(
                left,
                dx: -70pt,
                [
                    #block([
                        _Theorem #theorem-cnt.get()._
                        #label("theorem" + str(lemma-cnt.get()))
                    ])
                ],
            )
            #content
            #line(start: (-70pt, 0pt), length: page.width - 140pt)
        ],
        width: page.width - page.margin.left * 2,
    )
    v(box-vspace)
}

#let corollary(content) = context {
    corollary-cnt.update(it => it + 1)
    v(box-vspace)
    block(
        [
            #line(start: (-70pt, 0pt), length: page.width - 140pt)
            #place(
                left,
                dx: -70pt,
                [
                    #block([
                        _Corollary #corollary-cnt.get()._
                        #label("cor." + str(corollary-cnt.get()))
                    ])],
            )
            #content
            #line(start: (-70pt, 0pt), length: page.width - 140pt)
        ],
        width: page.width - page.margin.left * 2,
    )
    v(box-vspace)
}
#let lemma(content) = context {
    lemma-cnt.update(it => it + 1)
    v(box-vspace)
    block(
        [
            #line(start: (-70pt, 0pt), length: page.width - 140pt)
            #place(
                left,
                dx: -70pt,
                [
                    #block([
                        _Lemma #lemma-cnt.get()._
                        #label("lemma" + str(lemma-cnt.get()))
                    ])],
            )
            #content
            #line(start: (-70pt, 0pt), length: page.width - 140pt)
        ],
        width: page.width - page.margin.left * 2,
    )
    v(box-vspace)
}

#let proof(content, prompt: "Proof") = context {
    block(
        [ _#prompt._ #" "
            #content
            #h(1fr) $qed$
        ],
        width: 100%,
    )
}

#let solution(content) = context {
    block(
        [ _Solution._  #" "
            #content
        ],
        width: 100%,
    )
}

#let problem(content, bg: none, source: none) = context {
    v(box-vspace)
    block(
        breakable: false,
        [ #block(text([*Problem*], fill: white), inset: (top: 8pt, left: 8pt, bottom: -5pt))
            #block(
                [ #if source != none [ #" " _(#source)_ #" " ]
                    #content ],
                fill: accent-lighteren(bg),
                inset: 8pt,
                width: 100%,
            )
        ],
        fill: (bg),
        width: 100%,
    )
    v(box-vspace)
}

#let example(content, bg: none) = context {
    v(box-vspace)
    block(
        breakable: false,
        [ #block(text([*Example*], fill: white), inset: (top: 8pt, left: 8pt, bottom: -5pt))
            #block(
                content,
                fill: accent-lighteren(bg),
                inset: 8pt,
                width: 100%,
            )
        ],
        fill: (bg),
        width: 100%,
    )
    v(box-vspace)
}

#let io-problem(content, bg: none, source: none) = problem(content, bg: bg, source: source)

#let definition(content, id: none, prompt: "Definition") = context {
    block(breakable: false, [
        #line(length: 100%)
        #text([*#(prompt)* _#(id)_])
        #content
        #line(length: 100%)
    ])
}

#let implementation(content, file: none) = context {
    block(
        stroke: 1pt,
        inset: 8pt,
        [
            #if file != none {
                place(right, [_#raw(file)_])
            }
            #content
        ],
        width: 100%,
    )
}
#let stdout(content, stream: "STDOUT") = context {
    block(
        stroke: 1pt,
        inset: 8pt,
        [
            #stream \
            #content
        ],
        width: 100%,
    )
}
#let extension(content) = context {}
