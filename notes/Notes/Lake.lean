import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Lake" =>
%%%
tag := "lake"
htmlSplit := .never
%%%

*Lake*{index}[Lake] is Lean's build tool and package manager.
It resolves dependencies, builds libraries and executables, and records the exact revisions that were used.

Each of `lean/` and `notes/` is an independent Lake package.
Lake commands are therefore run from inside the relevant package directory, which is what the root `Makefile` does.

# Package files
%%%
tag := "lake-files"
%%%

Every package has at least three important files.

: `lakefile.toml`

  Declares the package name, its dependencies, and its build targets.
  Dependencies can come from a registry, a Git URL, or a local path.

: `lake-manifest.json`

  Records the resolved Git revision of every dependency.
  Commit this file when the project is under version control so that builds are reproducible.

: `lean-toolchain`

  Names the Lean version for the package, for example `leanprover/lean4:v4.35.0`.
  `elan` uses it to select the compiler automatically.

The `lean/` package additionally contains the `Brane` library, while `notes/` contains the `Notes` library and the `notes` executable that renders this manual.

# A minimal lakefile
%%%
tag := "lake-example"
%%%

The shape of the build configuration used in this repository:

```
name = "brane"
defaultTargets = ["Brane"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0"

[[lean_lib]]
name = "Brane"
```

The `[[require]]` table adds a dependency.
`[[lean_lib]]` declares a library whose root module is `Brane.lean`.
An executable is declared with `[[lean_exe]]` and a `root` module, as in `notes/`.

# Commands
%%%
tag := "lake-commands"
%%%

Run these from a package directory:

```
lake build              # build the default targets
lake build Brane.Basic  # build one module
lake update             # re-resolve dependencies
lake update mathlib     # update a single dependency
lake clean              # remove build artifacts
lake env lean file.lean # run lean with the package's search path
```

`lake build` is what `make lean` and `make notes` call.
In `notes/`, `lake exe notes` runs the manual generator, and `lake exe verso-serve _out/html-multi` runs the preview server.

# Why two packages
%%%
tag := "lake-two-packages"
%%%

Verso and Mathlib are both large dependencies, and the manual does not need Mathlib.
Splitting the repository keeps the notes build small and fast, while `lean/` can use Mathlib freely.

The connection is one-directional: `notes/` reads code from `../lean` through Verso's external-code support.
It never imports the `Brane` library, so the two packages can be built independently.
See {ref "verso-anchors"}[Anchors and external code] for the mechanism.
