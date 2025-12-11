#let process-credits(authors) = {
    let affiliations = ()
    let _authors = ()

    for author in authors {
        let found-idx = affiliations.position(it => it == author.affiliation)

        let idx = if found-idx == none {
            affiliations += (author.affiliation,)
            affiliations.len() - 1
        } else {
            found-idx
        }

        _authors += ((name: author.name, affiliation: idx + 1),)
    }

    (authors: _authors, affiliations: affiliations)
}

#let to-string(it) = {
    if type(it) == str {
        it
    } else if type(it) != content {
        str(it)
    } else if it.has("text") {
        it.text
    } else if it.has("children") {
        it.children.map(to-string).join()
    } else if it.has("body") {
        to-string(it.body)
    } else if it == [ ] {
        " "
    }
}
