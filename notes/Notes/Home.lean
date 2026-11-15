import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Home" =>
%%%
tag := "home"
htmlSplit := .never
%%%

This manual is the research notebook for the *Brane*{index}[Brane] project.
It is written in Lean with Verso, the same language and toolchain as the code it describes.

The repository keeps two concerns in separate Lake packages:

 * `lean/` contains the Lean source code and its Mathlib dependency.
 * `notes/` contains this manual and depends on Verso only.

Keeping them separate means the notes build does not rebuild Mathlib, while code snippets in the notes are still read from `lean/` at build time.
A quoted declaration therefore cannot silently drift away from the source.

# Layout
%%%
tag := "layout"
%%%

```
brane/
├── lean/
│   ├── Brane.lean
│   ├── Brane/
│   │   ├── Basic.lean
│   │   ├── Exercises.lean
│   │   └── Playground.lean
│   ├── lakefile.toml
│   ├── lake-manifest.json
│   └── lean-toolchain
├── notes/
│   ├── Notes.lean
│   ├── Notes/
│   │   ├── Home.lean
│   │   └── ...
│   ├── Main.lean
│   ├── lakefile.toml
│   ├── lake-manifest.json
│   └── lean-toolchain
├── Makefile
└── README.md
```

Both packages use Lean `v4.35.0`.
The `lean/` package pins Mathlib `v4.35.0` and a `subverso` revision compatible with Verso `v4.35.0`.
The `notes/` package pins Verso `v4.35.0`.

# Building
%%%
tag := "building"
%%%

From the repository root:

```
make lean     # check the Lean sources
make notes    # build this manual into notes/_out/html-multi
make serve    # preview the manual at http://localhost:8000
```

`make notes` runs `lake exe notes` in `notes/`.
The build output is a directory of HTML pages; the development server watches the sources and rebuilds on demand.

# Reading path
%%%
tag := "reading-path"
%%%

If you are new to this setup, read the chapters in order:

 * {ref "lean"}[Lean 4] introduces the language.
 * {ref "lake"}[Lake] explains the build tool.
 * {ref "mathlib"}[Mathlib] and {ref "reservoir"}[Reservoir] cover the library ecosystem.
 * {ref "lean-nvim"}[lean.nvim] and {ref "astro-nvim"}[AstroNvim] describe the editor.
 * {ref "verso"}[Verso] explains how these notes are written.
 * {ref "project"}[Project Map] connects files to chapters.
 * {ref "exercises"}[Exercises] is the first hands-on task.
