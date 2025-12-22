# Answers
## Type Theory & Formal Proof - An Introduction

Excercises I did while learning type theory. **These answers have not been checked by anyone** so should only be used as an reference.

Issues on pointing out mistakes are welcomed.


## Dependencies
The answers were written in typst (currently 0.14.1). Libs used were:
- *derive-it:1.1.0* - for typesetting fitch derivations
- *tdtr:0.4.2* - for drawing trees
- *curryst:0.6.0* - for typesetting derivation trees
- *commute:0.3.0* - for drawing diagrams
- *cetz:0.4.2* - for drawing advanced diagrams

The template used (cyan-report) was written by me. I couldn't quite make sense of how to contribute to the typst universe so I just copied the lib into the project dir. It is not recommended to submit PRs to enhance the lib since it is not part of this project. Later on when I complete the template I will have a dedicated repository for it.

## Automation
I used a precommit hook to compile the typ docs into the ./out directory. Note that I need the cyan-report package inside ./src/ for compilation to work.
