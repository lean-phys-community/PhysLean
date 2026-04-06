# Linting Physlib

`Linting` is the process of checking changes to the project
for certain types of stylistic errors. This process is carried out
by automatic scripts called `linters`.

Physlib has a number of linters which check for various different things.
They can all be run on your local version of the project, but some of them
are also automatically run on pull-requests to Physlib. These latter linters
must be passed before the pull-request can be merged with the main branch of the
project.

Below we summarize the linters Physlib has, in each bullet point the initial `code snippet`
is how the linter can be run locally.

The first two linters are the most important, but in an ideal world you would check that
all of the following linters run correctly.

- `lake exe lint_all` (**A PR must in general pass this linter**): This linter is split into seven steps, strictly speaking not all of these steps must be past for a PR to be merged, but it is best to just fix them all.
  - step 1: This checks for basic style mistakes such as double spaces and string combinations like `):`
  - step 2: This builds the project
  - step 3: Checks all files are imported to `Physlib.lean` and that they are sorted correctly.
  - step 4: Checks that no tags on TODO items are duplicates of one another.
  - step 5: Checks that all lemmas and definitions dependent on `sorry` or `Lean.ofReduceBool` are correctly attributed with `@[sorryful]` or `@[pseudo]`
  - step 6: Checks all Lean linters run without error, this picks up things like lack of doc-strings on definitions, or incompatible `@[simp]` attributes
  - step 7: Checks there are not transitive imports, e.g. A imports B and C, but B already
  imports C.
This linter may need running a number of times.
- `./scripts/lint-style.sh` (**A PR must pass this linter**): This linter checks for some
  style errors e.g. too long lines or wrong indentations, as well as checking if all necessary `simp` lemmas are of the form `simp only [...]`. For this linter
  to work properly you must first commit your changes to github.
- `lake exe style_lint` : A linter which only does step 1 of `lake exe lint_all`.
- `lake exe runPhyslibLinters` : A linter which only does step 6 of `lake exe lint_all`.
- `lake exe module_doc_lint` : Checks that module documentation is laid out according to a set standard. This does not check any file in the list `./scripts/MetaPrograms/module_doc_no_lint.txt`. Slowly we will empty this list of files.
- `lake exe spelling` : Checks the spelling of words in Physlib against a given list
  of correctly spelled words which can be found in `./scripts/MetaPrograms/spellingWords.txt`
