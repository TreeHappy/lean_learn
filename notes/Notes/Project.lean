import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Project Map" =>
%%%
tag := "project"
htmlSplit := .never
%%%

This chapter connects the files in the repository to the chapters that explain them.
The map is deliberately explicit: every note has a stable tag, and every source file has a clear role.

# Source map
%%%
tag := "project-source-map"
%%%

: `lean/Brane/Basic.lean`

  Core examples: `hello`, `double`, and `double_eq_two_mul`.
  Quoted in {ref "lean"}[Lean 4] through anchors.

: `lean/Brane/Exercises.lean`

  The first exercise, `add_comm_exercise`, and the unsolved `zero_add_exercise`.
  Quoted in {ref "exercises"}[Exercises].

: `lean/Brane/Playground.lean`

  Scratch space for experiments.
  It is not imported by `Brane.lean`, so it can be edited freely.

: `lean/lakefile.toml`

  Declares the `Brane` library, Mathlib, and the pinned SubVerso revision.
  Explained in {ref "lake"}[Lake].

: `notes/Notes.lean`

  The root of this manual: metadata, imports, and the ordered list of chapters.

: `notes/Main.lean`

  The `notes` executable; it passes the root part to `manualMain`.

: `notes/Notes/`

  One module per chapter. Add a chapter by creating a file, importing it, and including it in the root part.

# Note identifiers
%%%
tag := "project-tags"
%%%

Each chapter sets a `tag` in its metadata block.
Those tags are the targets of `{ref}` links and are stable across file renames.

: `home`

  This notebook's entry point and reading path.

: `lean`

  Lean language basics.

: `lake`

  The build tool and package format.

: `mathlib`

  The mathematical library and its cache.

: `reservoir`

  The package registry.

: `lean-nvim`

  The Lean plugin, including the PATH and configuration fixes.

: `astro-nvim`

  The editor distribution and its layout.

: `verso`

  How the manual is written and built.

: `project`

  This source map.

: `exercises`

  The first hands-on task.

# Build workflow
%%%
tag := "project-workflow"
%%%

The intended loop is:

 * Edit Lean code in `lean/` and check it with `make lean`.
 * Edit prose in `notes/` and preview it with `make notes` and `make serve`.
 * Commit source and notes together so that quoted code and its explanation stay in sync.

Because the notes build invokes the Lean build for any quoted module, a broken source file also breaks the manual.
That is intentional: the documentation is part of the build, not an afterthought.

# Editor workflow
%%%
tag := "project-editor"
%%%

Open any `.lean` file in the repository with Neovim.
`lean.nvim` starts `lake serve` in the nearest package, so both `lean/` and `notes/` get a working language server.

Useful checks:

```
:lua =vim.fn.exepath("lake")
:lua =vim.lsp.get_clients()
```

See {ref "lean-nvim"}[lean.nvim] for the full set of mappings and commands.
