# Formalisation of NRC
Olivia Hartley Weston, supervised by Cécilia Pradic.

# File structure
The current working file with all the big stuff is `Semantics.v`. `Syntax.v` has a definition of NRC syntax but it's been temporarily copied over to `Semantics.v` so it's less problematic to handle Coq's file imports and qualified names.

# Prerequisites and versions
Coq version used: [8.14.1](https://github.com/coq/coq/releases/tag/V8.14.1)  
OCaml version used: [4.14.0](https://github.com/ocaml/ocaml/archive/4.14.0.tar.gz)

Check your Coq version with `coqtop -v`. Check your OCaml version with `ocaml --version`.

Olivia's editor: `GNU Emacs + EViL Mode + Proof General + company-coq`.

[GNU Emacs download.](https://www.gnu.org/software/emacs/download.html)  
[Using packages in Emacs to download EViL mode and Proof General](https://melpa.org/#/getting-started) (EViL Mode is for Vim style keybindings, optional).  
[EViL mode GitHub repository.](https://github.com/emacs-evil/evil)  
[Proof General website.](https://proofgeneral.github.io/)  
[company-coq GitHub repository.](https://github.com/cpitclaudel/company-coq)

# Compiling
Either:
- Use my makefile wrapper: `make` should be enough as long as the Makefile is in the same directory.
- Manually create the Coq makefile first: `coq_makefile -f _CoqProject -o CoqMakefile`. Proceed to run `CoqMakefile` using `make`.

Compiling ensures that any `.v` files you have can be linked together.  
To actually see Coq code being interpreted, open your `.v` file in Emacs and use Proof General's controls to navigate the worker through the Coq file.

This project does not use any external Coq packages, thus OPAM is not required.
