# Two-level type theory in Coq

In this repository, you can find the emulation of two HTS-like systems in Coq.

* the first one (in directory [MLTT2](MLTT2)) is close to the original HTS system [1] or to the one presented in [2,3]

* the second one (in directory [MLTT2F](MLTT2F)) use a finer notion of fibrancy, which allow to add a fibrant replacement

[1] Vladimir Voevodsky. A simple type system with two identity types. Unpublished notes, http://uf-ias-2012.wikispaces.com/file/view/HTS.pdf, 2013.

[2] Thorsten Altenkirch, Paolo Capriotti, and Nicolai Kraus. Extending homotopy type theory with strict equality. Computer Science Logic, 2016, Marseille, France.

[3] Danil Annenkov, Paolo Capriotti, and Nicolai Kraus. Two-Level Type Theory and Applications. Preprint on arXiv: https://arxiv.org/abs/1705.03307


## Compilation ##

* This development compiles with Coq8.7
* To compile simply run ` make `


## Plugin Myrewrite ##

To emulate HTS, we use a private inductive type to define path identity types,
so that we can't destruct a path equality without checking the fibrancy condition.

Unfortunately, there is a bug and the `rewrite` tactic allow "escape" the private inductive type.
When we use it for the first time it generates a lemma `paths_internal_rew` which is used to rewrite
but which is proved by matching over the path equality.
To circumvent that, we define a plugin to explicitly specify which lemma use to rewrite instead of `paths_internal_rew`.
See also comments in [Overture.v](MLTT2/Overture.v) for some details.

Another drawback of the private inductive type is that it breaks some tactics, and especially `destruct`.
To solve this problem, we defined a tactic `destruct_path` which revert all hypothesis depending on
the equality considered, apply paths_ind, and then reintroduce the reverted hypothesis.


## Description of files ##

Project root:

* `Overture.v` contains basic definitions and notations (sigma types, ...) and the definition of a strict equality

* `Strict_eq.v` contains some facts about strict equality (transport, equality of pairs, ...)

* `Category.v` contains the definition of categories and model structures


In each directory [MLTT2](MLTT2) and [MLTT2F](MLTT2F):

* `Overture.v` contains the definition of fibrancy, the fibrancy rules and the definition of path equality

* `Path_eq.v` contains facts about path equality

* `Equivalences.v` contains the definition of type theoretic equivalences


Only in [MLTT2](MLTT2):
* `FibReplInconsistent.v` contains a proof that MLTT2 is incompatible with the fibrant replacement.

Only in [MLTT2F](MLTT2F):

* `Fibrant_replacement.v` contains the definition of the fibrant replacement
