# Type Theory & Formal Proof - Exercise Solutions

Exercise solutions from **Type Theory & Formal Proof: An Introduction**. **These answers have not been formally verified** and should only be used as a reference. Issues pointing out mistakes are welcomed.

## Dependencies

Written in [Typst](https://typst.app/) v0.14.1 with the following packages:

| Package | Version | Purpose |
|---------|---------|---------|
| `derive-it` | 1.1.0 | Fitch-style natural deduction derivations |
| `tdtr` | 0.4.2 | Tree structures |
| `curryst` | 0.6.0 | Derivation trees and proof trees |
| `commute` | 0.3.0 | Commutative diagrams |
| `cetz` | 0.4.2 | Advanced diagrams |

### Custom Template

Uses a custom `cyan-report` template (included in project). This template will have its own repository once completed - PRs to enhance it here are not recommended as it's outside this project's scope.

## Building

### Manual Build
```bash
typst compile src/<filename>.typ out/<filename>.pdf
```

### Automated Build
Run `./build.sh` to compile all `.typ` files to the `./out` directory. This script can also be used as a git pre-commit hook:
```bash
ln -s ../../build.sh .git/hooks/pre-commit
```

**Note**: The `cyan-report` template must be present in `./src/` for compilation to work.

## Project Structure
```
.
├── src/           # Source typst files
├── out/           # Compiled PDFs (generated)
├── build.sh       # Build script
└── README.md
```

## Contributing

Found a mistake? Open an issue or submit a PR with:
- Chapter/exercise number
- Clear description of the issue
- Reference or explanation for the correction

---

**Note**: Please respect the original textbook's copyright when using these materials.
