#import "processor.typ": process-credits, to-string
#import "constants.typ": *

// ============================================
// MAIN TEMPLATE FUNCTION
// ============================================

#let cyan-report(
    doc, // Document content
    title: none, // Title of document
    title-size: 50pt,
    subtitle: none, // Optional Subtitle
    authors: (), // List of author and affiliation
    accent: rgb(50, 150, 150), // Accent color
) = {
    // === ACCENT COLOR PALETTE ===
    let accent-darker = accent.darken(70%).saturate(40%)
    let accent-dark = accent.darken(30%)
    let accent-light = accent.lighten(30%).desaturate(10%)
    let accent-lighter = accent.lighten(70%).desaturate(30%)

    // === DOCUMENT SETTINGS ===
    set page(..page-config)
    set heading(numbering: "1. A. i. ")

    // === SHOW RULES ===
    // TODO: Set up a theme parametric to the accent color
    // set raw(theme: "color.xml")
    show raw: set text(font: "JetBrains Mono")
    show regex("> .+"): it => [
        #quote(to-string(it).slice(2))
    ]

    // === PROCESS AUTHOR/AFFILIATION DATA ===
    let processed-credits = process-credits(authors)

    // === TITLE PAGE HEADER ===
    context (
        pad(
            left: -page.margin.left,
            top: -page.margin.top,
            [
                #block(
                    [
                        #set par(leading: 2em)

                        // Title
                        #text(title-size, fill: white)[#smallcaps(title)] \

                        // Subtitle (optional)
                        #if subtitle != none {
                            text(17pt, fill: white)[#smallcaps(subtitle)]
                            linebreak()
                        }

                        // Authors
                        #for author in processed-credits.authors {
                            text(17pt, fill: accent-lighter)[
                                #smallcaps(author.name)
                                #super(str(author.affiliation))
                                #if processed-credits.authors.last() != author { " / " }
                            ]
                        }

                        // Affiliations
                        #linebreak()
                        #set par(leading: 0.1em)
                        #let _i = 0
                        #for affiliation in processed-credits.affiliations {
                            _i += 1
                            text(10pt, fill: accent-lighter)[
                                #_i. #affiliation
                            ]
                            linebreak()
                        }
                    ],
                    fill: accent-darker,
                    inset: (
                        left: page-config.margin.left,
                        top: page.margin.top / 2,
                        bottom: page.margin.top / 2,
                    ),
                    width: page.width,
                )
            ],
        )
    )

    // Spacing after header
    context [#v(page.margin.top / 2)]

    // === MAIN CONTENT ===
    doc
}
