# formal-methods-2026

Formal Methods in Software Development course at EKKE

## Compile the LaTeX presentation

Requirements: `make`, `latexmk`, a TeX distribution with XeLaTeX and the Beamer Metropolis theme, and the **JetBrainsMono Nerd Font** installed on your system.

From the repository root, run:

```sh
make -C presentation/latex
```

or from `presentation/latex`:

```sh
make
```

The generated PDF is `presentation/latex/main.pdf`.

To clean up build files while keeping the PDF:

```sh
make -C presentation/latex clean
```
